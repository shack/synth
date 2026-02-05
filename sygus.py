from collections import defaultdict
from pathlib import Path

import re
import tinysexpr
import tyro
import json

from dataclasses import dataclass, field

from synth.spec import Func, SynthFunc, Constraint, Problem, Production, Nonterminal
from synth.synth_n import LenCegis
from synth.downscaling import Downscale

from z3 import *

from synth.util import is_val, analyze_precond, free_vars, subst_with_number, Debug

# Default component sets (see SyGuS spec appendix B)

def panic(msg, ctx=None):
    print(f'error: {msg}')
    sys.exit(1)

def assertion(cond, msg, ctx=None):
    if not cond:
        panic(msg, ctx=ctx)

b = Bool('b')

def create_bv_lib(w: int):
    x, y = BitVecs('x y', w)
    return [
        Func('bvnot',  ~x),
        Func('bvneg',  -x),
        Func('bvand',  x & y),
        Func('bvor',   x | y),
        Func('bvadd',  x + y),
        Func('bvmul',  x * y),
        Func('bvudiv', UDiv(x, y), precond=(y != 0)),
        Func('bvurem', URem(x, y), precond=(y != 0)),
        Func('bvshl',  x << y),
        Func('bvlshr', LShR(x, y)),
        Func('ite',    If(b, x, y)),
        Func('bvult',  ULT(x, y)),
    ]

x, y = Reals('x y')
n, m = Ints('n m')
c, d = Bools('c d')

logics = {

    'Bool': lambda _: [
        Func('not', Not(c)),
        Func('and', And([c, d])),
        Func('or',  Or([c, d])),
        Func('xor', Xor(c, d)),
        Func('=>',  Implies(c, d)),
        Func('=',   c == d),
    ],
    'LIA': lambda _: [
        Func('-', -n),
        Func('+', n + m),
        Func('*', n * m),
        Func('div', n / m, precond=(m != 0)),
        Func('mod', n % m, precond=(m != 0)),
        Func('abs', If(n >= 0, n, -n)),
        Func('ite', If(b, n, m)),
        Func('<', n < m),
        Func('<=', n <= m),
        Func('>', n > m),
        Func('>=', n >= m),
        Func('=', n == m),
    ],
    'NRA': lambda _: [
        Func('-', -x),
        Func('+', x + y),
        Func('*', x * y),
        Func('/', x / y, precond=(y != 0)),
        Func('ite', If(b, x, y)),
        Func('<', x < y),
        Func('<=', x <= y),
        Func('>', x > y),
        Func('>=', x >= y),
        Func('=', x == y),
    ],
    'BV': create_bv_lib,
}

def productions_from_components(nonterminal: str, components: list[Func]) -> Production:
    return [ Production(op, tuple([nonterminal] * len(op.inputs)) ) for op in components ]

logics['NIA'] = logics['LIA']

_LITERAL_RE = re.compile(r'' \
                         r'(?P<int>-?\d+)|' \
                         r'(?P<flt>-?\d*\.\d+)|' \
                         r'(?P<hex>#x[0-9a-fA-F]+)|' \
                         r'(?P<bin>#b[01]+)|' \
                         r'(?P<true>true)|' \
                         r'(?P<false>false)')

def parse_literal(s, bv_sort=None):
    if m := _LITERAL_RE.fullmatch(s):
        for k, v in m.groupdict().items():
            if v is not None:
                match k:
                    case 'int':
                        return IntVal(int(v))
                    case 'flt':
                        return RealVal(float(v))
                    case 'hex':
                        bv_sort = bv_sort if not bv_sort is None else len(v[2:]) * 4
                        return BitVecVal(int(v[2:], 16), bv_sort)
                    case 'bin':
                        bv_sort = bv_sort if not bv_sort is None else len(v[2:])
                        return BitVecVal(int(v[2:], 2), bv_sort)
                    case 'true':
                        return BoolVal(True)
                    case 'false':
                        return BoolVal(False)
    raise ValueError(f'unknown literal {s}')

def get_sort(s):
    match s:
        case 'Int':
            return IntSort()
        case 'Real':
            return RealSort()
        case 'Bool':
            return BoolSort()
        case _ if isinstance(s, Sequence):
            match s:
                case ['_', 'BitVec', n]:
                    return BitVecSort(int(n))
                case ['BitVec', n]:
                    return BitVecSort(int(n))
                case ['_', 'Array', s1, s2]:
                    return ArraySort(get_sort(s1), get_sort(s2))
        case _:
            raise ValueError(f'unknown sort {s}')

def parse_synth_fun(toplevel: 'SyGuS', sexpr):
    # name of the function, its parameters and return type
    _, name, params, ret = sexpr[:4]
    ret_sort = get_sort(ret)
    non_terminals = {}
    constants = {}
    params = { n: get_sort(s) for n, s in params }
    components = []

    # if we have a grammar definition
    if len(sexpr) > 4:
        # get the grammar definition
        rest = sexpr[4:]
        if len(rest) == 2:
            # we have a list of non-terminals and their sorts,
            # and a list of components per nonterminal
            # as described in the SyGuS spec
            non_terms, comps = rest
        else:
            assertion(len(rest) == 1, 'expecting only one more s-expr', ctx=rest)
            # we only have a list of components, so create a default non-terminal
            # this seems to appear in older files. Not really spec-conforming.
            comps = rest[0]
            # non_term = rest[0][0]
            non_terms = [ ('Start', ret) ]

        # map from names to Nonterminal objects
        nts = {}
        # chained non-terminals
        chain = defaultdict(list)
        # get a mapping of non-terminal names to SMT sorts
        non_terminals = { name: get_sort(sort) for name, sort in non_terms }
        # for each non-terminal, parse its components
        for non_term, sort_name, nt_comps in comps:
            sort = get_sort(sort_name)
            assertion(sort == non_terminals[non_term],
                      f'sort mismatch for non-terminal {non_term}: {sort} != {non_terminals[non_term]}',
                      ctx=comps)

            # constants that are allowed for this non-terminal
            # None means arbitrary constants of the given sort are allowed
            # otherwise we give a dict from constant to max number of
            # allowed occurrences (None means unbounded).
            # (the empty dict means no constants are allowed)
            constants = {}
            # Parameters that are allowed for this non-terminal
            parameters = tuple()
            productions = tuple()

            for t in nt_comps:
                match t:
                    case str() as s:
                        if s in params:
                            parameters += (s,)
                        elif s in non_terminals:
                            # the non-terminal s appears plain in the productions of non_term
                            chain[non_term] += [s]
                        else:
                            # constant
                            if constants is not None:
                                # It could be that we have seen (Constant) before.
                                # In that case, all constants are allowed and we
                                # ignore this specific constant.
                                c = parse_literal(s, sort)
                                constants[c] = None
                    case _:
                        match t[0]:
                            case 'Constant':
                                # we're allowed arbitrary constants of the given sort
                                constants = None
                            case 'Variable':
                                # we can use all parameters of the nonterminal's sort
                                parameters = tuple(p for p, s in params.items() if s == sort)
                            case _:
                                s = ComponentScope(toplevel, params, non_terminals)
                                res = s.parse_term(t)
                                precond = And(analyze_precond(res))
                                res_simpl = simplify(res)
                                if is_val(res_simpl) and constants is not None:
                                    constants[res_simpl] = None
                                else:
                                    args     = [ x[0] for x in s.args.values() ]
                                    operands = [ x[1] for x in s.args.values() ]
                                    func     = Func(t[0], res, inputs=tuple(args), precond=precond)
                                    for p in productions:
                                        if func.is_symmetric_of(p.op):
                                            break
                                    else:
                                        sexpr = subst_with_number(str(t), non_terminals)
                                        p = Production(
                                                op=func,
                                                operands=tuple(operands),
                                                operand_is_nt=tuple(x in non_terminals for x in operands),
                                                sexpr=sexpr,
                                                attributes=s.attr)
                                        productions += (p,)
            nts[non_term] = Nonterminal(non_term, sort, parameters, productions, constants)

        # now resolve chained non-terminals
        seen = set()
        def resolve(nt_name):
            assertion(nt_name not in seen, f'cyclic non-terminal definitions involving {nt_name}', ctx=rest)
            nt = nts[nt_name]
            for t in chain[nt_name]:
                if t in chain:
                    resolve(t)
                nts[nt_name] = Nonterminal(
                    nt.name,
                    nt.sort,
                    nt.parameters + nts[t].parameters,
                    nt.productions + nts[t].productions,
                    nt.constants | nts[t].constants,
                )
            seen.add(nt_name)
        for nt_name in chain:
            resolve(nt_name)

    elif toplevel.logic == 'BV':
        # unclear what size to use, so scan parameters and return type
        # for bit-vectors sorts and use the first one found
        size = None
        for s in [ ret_sort ] + [ s for s in params.values() ]:
            if isinstance(s, BitVecSortRef):
                if size is None:
                    size = s.size()
                else:
                    assertion(s.size() == size, 'all bit-vector sorts must have the same size', ctx=rest)
        assertion(size, 'no bit-vector sorts found for BV logic', ctx=rest)
        productions = productions_from_components('Start', create_bv_lib(size))
        nts['Start'] = Nonterminal('Start', ret_sort, tuple(params.keys()), tuple(productions))
    else:
        components = logics[toplevel.logic](None)
        productions = productions_from_components('Start', components)
        nts['Start'] = Nonterminal('Start', ret_sort, tuple(params.keys()), tuple(productions))
    return name, SynthFunc(outputs=[ ('res', ret_sort) ],  # outputs
                           inputs=[ (p, s) for p, s in params.items() ], # parameters
                           result_nonterminals=(next(iter(nts.keys())),),
                           nonterminals=nts)

class Scope:
    def __init__(self, toplevel: 'SyGuS'):
        self.toplevel = toplevel
        self.parent = None
        self.map = {}

    def push(self):
        s = Scope(self.toplevel)
        s.parent = self
        return s

    def __str__(self):
        return '{' + ', '.join(f'{k}: {v}' for k, v in self.map.items()) + '}'

    def __contains__(self, k):
        return k in self.map or (self.parent and k in self.parent)

    def __getitem__(self, k):
        if k in self.map:
            return self.map[k]
        if self.parent:
            return self.parent[k]
        raise KeyError(k)

    def __setitem__(self, k, v):
        self.map[k] = v

    def fun_appl(self, op, args, expr):
        assertion(op in self.toplevel.funs, f'unknown function {op}', ctx=expr)
        (body, inputs) = self.toplevel.funs[op]
        assertion(len(args) == len(inputs), f'wrong number of arguments for {op}', ctx=expr)
        p = [ (v, a) for v, a in list(zip(inputs, args)) ]
        return substitute(body, p)

    def parse_const(self, s, bv_sort=None):
        lit = parse_literal(s, bv_sort)
        if lit is None:
            raise ValueError(f'unknown constant {s}')
        return lit

    def parse_term(self, expr):
        match expr:
            case ['let', bindings, body]:
                scope = self.push()
                for var, expr in bindings:
                    scope[var] = scope.parse_term(expr)
                return scope.parse_term(body)
            case ['!', *args]:
                return self.parse_term(args[0])
            case [op, *args]:
                x = [ self.parse_term(a) for a in args ]
                match op:
                    case 'bvnot':    return ~x[0]
                    case 'bvneg':    return -x[0]
                    case 'bvand':    return x[0] & x[1]
                    case 'bvor':     return x[0] | x[1]
                    case 'bvxor':    return x[0] ^ x[1]
                    case 'bvadd':    return x[0] + x[1]
                    case 'bvsub':    return x[0] - x[1]
                    case 'bvmul':    return x[0] * x[1]
                    case 'bvsdiv':   return x[0] / x[1]
                    case 'bvsrem':   return x[0] % x[1]
                    case 'bvudiv':   return UDiv(x[0], x[1])
                    case 'bvurem':   return URem(x[0], x[1])
                    case 'bvshl':    return x[0] << x[1]
                    case 'bvlshr':   return LShR(x[0], x[1])
                    case 'bvashr':   return x[0] >> x[1]
                    case 'bvnot':    return ~x[0]
                    case 'bvult':    return ULT(x[0], x[1])
                    case 'bvule':    return ULE(x[0], x[1])
                    case 'bvugt':    return UGT(x[0], x[1])
                    case 'bvuge':    return UGE(x[0], x[1])
                    case 'bvslt':    return x[0] <  x[1]
                    case 'bvsle':    return x[1] <= x[0]
                    case 'bvsgt':    return x[1] >  x[0]
                    case 'bvsge':    return x[0] >= x[1]
                    case '-':        return -x[0] if len(x) == 1 else x[0] - x[1]
                    case '+':        return x[0] + x[1]
                    case '*':        return x[0] * x[1]
                    case 'div':      return x[0] / x[1]
                    case 'mod':      return x[0] % x[1]
                    case 'abs':      return Abs(x[0])
                    case '<':        return x[0] < x[1]
                    case '<=':       return x[0] <= x[1]
                    case '>':        return x[0] >  x[1]
                    case '>=':       return x[0] >= x[1]
                    case '=>':       return Implies(x[0], x[1])
                    case 'not':      return Not(x[0])
                    case 'and':      return And([x[0], x[1]])
                    case 'or':       return Or([x[0], x[1]])
                    case 'xor':      return Xor(x[0], x[1])
                    case '=':        return x[0] == x[1]
                    case 'ite':      return If(x[0], x[1], x[2])
                    case 'distinct': return Distinct(*x)
                return self.fun_appl(op, x, expr)
            case str() as s:
                if s in self:
                    return self[s]
                elif s in self.toplevel.funs:
                    return self.fun_appl(s, (), expr)
                else:
                    return self.parse_const(s)

class ConstraintScope(Scope):
    def __init__(self, toplevel: 'SyGuS'):
        super().__init__(toplevel)

    def push(self):
        s = ConstraintScope(self.toplevel)
        s.parent = self
        return s

    def parse_const(self, s, bv_sort=None):
        try:
            return super().parse_const(s, bv_sort)
        except ValueError as e:
            if s in self.toplevel.synth_funs:
                return self.fun_appl(s, (), ctx=None)
            else:
                raise e

    def fun_appl(self, name, args, expr):
        if name in self.toplevel.synth_funs:
            k = (name, tuple(args))
            if k in self.toplevel.fun_appl:
                res = self.toplevel.fun_appl[k][0]
            else:
                fun = self.toplevel.synth_funs[name]
                assertion(len(args) == len(fun.inputs), f'wrong number of arguments for {name}')
                res  = FreshConst(fun.outputs[0][1], f'y_{name}')
                self.toplevel.fun_appl[k] = (res,)
            return res
        else:
            return super().fun_appl(name, args, expr)

    def parse(self, e):
        res = self.parse_term(e)
        fv = free_vars(res)
        appl = { app: outs for app, outs in self.toplevel.fun_appl.items() if outs[0] in fv }
        return Constraint(res, tuple(self.toplevel.vars.values()), appl)

class ComponentScope(Scope):
    def __init__(self, toplevel: 'SyGuS', params: dict[str, SortRef], non_terminals: dict[str, SortRef]):
        super().__init__(toplevel)
        self.non_terminals = non_terminals
        self.params = params
        self.args = {}
        self.attr = {}

    def push(self):
        s = ComponentScope(self.toplevel, self.params, self.non_terminals)
        s.args = self.args
        return s

    def parse_term(self, expr):
        match expr:
            case ['!', *args]:
                self.attr = { key[1:]: val for key, val in zip(args[1::2], args[2::2]) }
                return self.parse_term(args[0])
            case str() as s:
                if s in self.non_terminals:
                    name = f'x{len(self.args)}'
                    res = FreshConst(self.non_terminals[s], name)
                    self.args[name] = (res, s)
                    return res
                elif s in self.params:
                    if s in self.args:
                        return self.args[s][0]
                    else:
                        res = Const(s, self.params[s])
                        self.args[s] = (res, s)
                        return res
        return super().parse_term(expr)

@dataclass
class Check:
    pass

@dataclass
class Default:
    pass

@dataclass
class SyGuS:
    """Parser for SyGuS v2 format."""

    file: Path

    def __post_init__(self):
        self.funs = {}
        self.vars = {}
        self.synth_funs = {}
        self.constraints = []
        self.fun_appl = {}
        self.result = 0

    def problems(self):
        with open(self.file) as f:
            while True:
                s = tinysexpr.read(f)
                if s is None:
                    break
                if p := self.parse_command(s):
                    yield p

    def parse_command(self, s):
        match s[0]:
            case 'set-logic':
                self.logic = s[1]
                assertion(self.logic in logics, f'Unsupported logic {self.logic}. Supported logics: {list(logics.keys())}', ctx=s)
            case 'define-fun':
                _, name, args, _, phi = s
                scope = Scope(self)
                inputs = { n: FreshConst(get_sort(s), n) for n, s in args }
                for n, c in inputs.items():
                    scope[n] = c
                body = scope.parse_term(phi)
                assertion(not name in self.funs, f'fun already defined: {name}', s)
                self.funs[name] = (body, inputs.values())
            case 'synth-fun':
                name, fun = parse_synth_fun(self, s)
                assertion(not name in self.synth_funs, f'synth-fun already defined: {name}', s)
                self.synth_funs[name] = fun
            case 'declare-var':
                _, name, sort = s
                self.vars[name] = Const(name, get_sort(sort))
            case 'constraint':
                scope = ConstraintScope(self)
                for name, v in self.vars.items():
                    scope[name] = v
                self.constraints += [ scope.parse(s[1]) ]
            case 'check-synth':
                return Problem(
                    constraints=self.constraints,
                    funcs=self.synth_funs,
                    theory=self.logic,
                    name=self.file)
            case _:
                print('ignoring command', s)

        return None

def problem(file: tyro.conf.PositionalRequiredArgs[Path]):
    s = SyGuS(file)
    for p in SyGuS(file).problems():
        print(p)
    return 0

def syntax(file: tyro.conf.PositionalRequiredArgs[Path]):
    s = SyGuS(file)
    for _ in SyGuS(file).problems():
        pass
    return 0

def synth(
    file: tyro.conf.PositionalRequiredArgs[Path],
    stats: Path | None = None,
    progress: bool = False,
    fuse_constraints: bool = False,
    opt_grammar: bool = True,
    bv_downscale: int = 0):

    for problem in SyGuS(file).problems():
        if opt_grammar:
            funcs = { name: f.optimize_grammar() for name, f in problem.funcs.items() }
            problem = Problem(
                constraints=problem.constraints,
                funcs=funcs,
                theory=problem.theory,
                name=problem.name)
        if len(problem.funcs) > 0:
            fuse_constraints = True
        if fuse_constraints:
            c = Constraint(
                And(c.phi for c in problem.constraints),
                params=next(iter(problem.constraints)).params,
                function_applications={k: v for d in problem.constraints for k, v in d.function_applications.items()}
            )
            problem = Problem(
                constraints=[c],
                funcs=problem.funcs,
                theory=problem.theory,
                name=problem.name)

        if progress:
            synth = LenCegis(debug=Debug(what='len|cex'), size_range=(0, 50))
        else:
            synth = LenCegis()
        if bv_downscale > 0 and problem.theory == 'BV':
            sy = Downscale(base=synth, target_bitwidth=[bv_downscale])
        else:
            sy = synth

        prgs, synth_stats = sy.synth_prgs(problem)
        if stats:
            with open(stats, 'w') as f:
                json.dump(synth_stats, f, indent=4)

        if prgs is None:
            print('(fail)')
            return 1
        else:
            print('(')
            for name, p in prgs.items():
                p = p.copy_propagation().dce()
                print(p.sexpr(name, sep='\n\t'))
            print(')')
            return 0

def term_size(expr):
    match expr:
        case ['let', bindings, body]:
            return sum(term_size(e) for _, e in bindings) + term_size(body)
        case ['!', *args]:
            return sum(term_size(e) for e in args)
        case [op, *args]:
            return 1 + sum(term_size(e) for e in args)
        case str() as s:
            return 0
    assertion(False, f'unknown expression: {expr}', ctx=expr)

def solution_sizes(input):
    funs = tinysexpr.read(input)
    for s in funs:
        if s[0] == 'define-fun':
            _, name, _, _, phi = s
            sz = term_size(phi)
            yield (name, sz)

def size(file: tyro.conf.PositionalRequiredArgs[Path]):
    with open(file) as f:
        for name, sz in solution_sizes(f):
            print(f'({name} {sz})')

if __name__ == '__main__':
    exit(tyro.extras.subcommand_cli_from_dict({
        'synth': synth,
        'syntax': syntax,
        'problem': problem,
        'size': size,
    }))