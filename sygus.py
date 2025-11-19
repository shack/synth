import re
import pathlib
import tinysexpr
import tyro
import json

from dataclasses import dataclass, field

from synth.spec import Func, SynthFunc, Constraint, Problem
from synth import SYNTHS

from z3 import *

# Default component sets (see SyGuS spec appendix B)

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
        case _ if type(s) == list:
            match s:
                case ['_', 'BitVec', n]:
                    return BitVecSort(int(n))
                case ['BitVec', n]:
                    return BitVecSort(int(n))
                case ['_', 'Array', s1, s2]:
                    return ArraySort(get_sort(s1), get_sort(s2))
        case _:
            raise ValueError(f'unknown sort {s}')

def parse_synth_fun(toplevel: SyGuS, sexpr):
    def get_component_str(t):
        match t:
            case str() as s:
                if s in non_terminals:
                    return non_terminals[s].name()
                else:
                    return s
            case [op, *args]:
                x = [ get_component_str(a) for a in args ]
                return f'({op} {" ".join(x)})'
            case _:
                assert False, f'unknown terminal {t}'

    _, name, params, ret = sexpr[:4]
    ret_sort = get_sort(ret)
    non_terminals = {}
    constants = {}
    params = { n: get_sort(s) for n, s in params }
    components = []

    if len(sexpr) > 4:
        rest = sexpr[4:]
        comp_map = {}
        const_map = {}
        if len(rest) == 2:
            # we have a list of non-terminals and a list their components
            # as described in the SyGuS spec
            non_terms, comps = rest
        else:
            assert len(rest) == 1
            # we only have a list of components, so create a default non-terminal
            comps = rest[0]
            non_term = rest[0][0]
            non_terms = [ ('Start', ret) ]

        non_terminals = { name: get_sort(sort) for name, sort in non_terms }
        for non_term, sort, nt_comps in comps:
            sort = non_terminals[non_term]
            for t in nt_comps:
                match t:
                    case str() as s:
                        if s in params:
                            pass
                        elif s in non_terminals:
                            pass
                        else:
                            # constant
                            const_map[s] = parse_literal(s, sort)
                    case _:
                        match t[0]:
                            case 'Constant':
                                # we're allowed arbitrary constants of the given sort
                                const_map = None
                            case 'Variable':
                                # we can always use variables otherwise the program would be constant
                                pass
                            case _:
                                s = ComponentScope(toplevel, params, non_terminals)
                                id = get_component_str(t)
                                if id in comp_map:
                                    # duplicate component
                                    # can happen in different non-terminals which we don't model yet
                                    # assert not id in comp_map, f'duplicate component {id}'
                                    pass
                                else:
                                    res    = s.parse_term(t)
                                    args   = [ x[0] for x in s.args.values() ]
                                    constr = [ x[1] for x in s.args.values() ]
                                    comp_map[id] = Func(t[0], res, inputs=tuple(args), param_constr=tuple(constr))
        components = comp_map.values()
        max_const = None if const_map else 0
        constants = None if const_map is None else { c: None for c in const_map.values() }
    elif toplevel.logic == 'BV':
        # unclear what size to use, so scan parameters and return type
        # for bit-vectors sorts and use the first one found
        size = None
        for s in [ ret_sort ] + [ s for s in params.values() ]:
            if isinstance(s, BitVecSortRef):
                if size is None:
                    size = s.size()
                else:
                    assert s.size() == size, 'all bit-vector sorts must have the same size'
        assert size, 'no bit-vector sorts found for BV logic'
        components = create_bv_lib(size)
        max_const = None
        constants = None
    else:
        components = logics[toplevel.logic](None)
        max_const = None
        constants = None
    return name, SynthFunc([ ('res', ret_sort) ],  # outputs
                           [ (p, s) for p, s in params.items() ], # inputs
                           { op: None for op in components }, # components
                           # if there are no constants allowed, we can force max_const to 0
                           # else we need to leave it unbounded.
                           max_const,
                           constants)

class Scope:
    def __init__(self, toplevel: SyGuS):
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

    def parse_fun(self, op, args):
        assert op in self.toplevel.funs, f'unknown function {op}'
        (body, inputs) = self.toplevel.funs[op]
        p = [ (v, self.parse_term(a)) for v, a in list(zip(inputs, args)) ]
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
                return args[1]
            case [op, *args]:
                x = [ self.parse_term(a) for a in args ]
                match op:
                    case 'bvnot':  return ~x[0]
                    case 'bvneg':  return -x[0]
                    case 'bvand':  return x[0] & x[1]
                    case 'bvor':   return x[0] | x[1]
                    case 'bvxor':  return x[0] ^ x[1]
                    case 'bvadd':  return x[0] + x[1]
                    case 'bvsub':  return x[0] - x[1]
                    case 'bvmul':  return x[0] * x[1]
                    case 'bvsdiv': return x[0] / x[1]
                    case 'bvsrem': return x[0] % x[1]
                    case 'bvudiv': return UDiv(x[0], x[1])
                    case 'bvurem': return URem(x[0], x[1])
                    case 'bvshl':  return x[0] << x[1]
                    case 'bvlshr': return LShR(x[0], x[1])
                    case 'bvashr': return x[0] >> x[1]
                    case 'bvnot':  return ~x[0]
                    case 'bvult':  return ULT(x[0], x[1])
                    case 'bvule':  return ULE(x[0], x[1])
                    case 'bvugt':  return UGT(x[0], x[1])
                    case 'bvuge':  return UGE(x[0], x[1])
                    case 'bvslt':  return x[0] < x[1]
                    case 'bvsle':  return x[1] >= x[0]
                    case 'bvsgt':  return x[1] < x[0]
                    case 'bvsge':  return x[0] >= x[1]
                    case '-':      return -x[0] if len(x) == 1 else x[0] - x[1]
                    case '+':      return x[0] + x[1]
                    case '*':      return x[0] * x[1]
                    case 'div':    return x[0] / x[1]
                    case 'mod':    return x[0] % x[1]
                    case 'abs':    return Abs(x[0])
                    case '<':      return x[0] < x[1]
                    case '<=':     return x[0] <= x[1]
                    case '>':      return x[0] >  x[1]
                    case '>=':     return x[0] >= x[1]
                    case '=>':     return Implies(x[0], x[1])
                    case 'not':    return Not(x[0])
                    case 'and':    return And([x[0], x[1]])
                    case 'or':     return Or([x[0], x[1]])
                    case 'xor':    return Xor(x[0], x[1])
                    case '=':      return x[0] == x[1]
                    case 'ite':    return If(x[0], x[1], x[2])
                    case 'distinct':  return Distinct(*x)
                return self.parse_fun(op, args)
            case str() as s:
                if s in self:
                    return self[s]
                elif s in self.toplevel.funs:
                    return self.parse_fun(s, ())
                else:
                    return self.parse_const(s)

class ConstraintScope(Scope):
    def push(self):
        s = ConstraintScope(self.toplevel)
        s.parent = self
        return s

    def parse_const(self, s, bv_sort=None):
        try:
            return super().parse_const(s, bv_sort)
        except ValueError as e:
            if s in self.toplevel.synth_funs:
                return self.parse_fun(s, ())
            else:
                raise e

    def parse_fun(self, name, args):
        if name in self.toplevel.synth_funs:
            fun = self.toplevel.synth_funs[name]
            # get the number of applications of that synth fun so far
            assert len(args) == len(fun.inputs), f'wrong number of arguments for {name}'
            args = tuple(self.parse_term(a) for a in args)
            n_appl = len(self.toplevel.fun_appl.setdefault(name, ()))
            res  = Const(f'{name}_{n_appl}_out', fun.outputs[0][1])
            self.toplevel.fun_appl[name] += ( ((res,), args ), )
            return res
        else:
            return super().parse_fun(name, args)

class ComponentScope(Scope):
    def __init__(self, toplevel: SyGuS, params: dict[str, SortRef], non_terminals: dict[str, SortRef]):
        super().__init__(toplevel)
        self.non_terminals = non_terminals
        self.params = params
        self.args = {}

    def push(self):
        s = ComponentScope(self.toplevel, self.params, self.non_terminals)
        s.args = self.args
        return s

    def parse_term(self, expr):
        match expr:
            case str() as s:
                if s in self.non_terminals:
                    name = f'x{len(self.args)}'
                    res = Const(name, self.non_terminals[s])
                    self.args[name] = (res, None)
                    return res
                elif s in self.params:
                    if s in self.args:
                        return self.args[s][0]
                    else:
                        res = Const(s, self.params[s])
                        self.args[s] = (res, None)
                        return res
        return super().parse_term(expr)

@dataclass
class Check:
    pass

@dataclass
class SyGuS:
    """Parser for SyGuS v2 format."""

    synth: SYNTHS | Check
    """Synthesizer to use."""

    file: tyro.conf.Positional[pathlib.Path]
    """File to parse."""

    stats: str | None = None
    """Dump statistics about synthesis to a JSON file."""

    print_problem: bool = False
    """Print the parsed problem."""

    def __post_init__(self):
        self.funs = {}
        self.vars = {}
        self.synth_funs = {}
        self.constraints = []
        self.fun_appl = {}
        self.result = 0

        with open(self.file) as f:
            while True:
                s = tinysexpr.read(f)
                if s is None:
                    break
                self.parse_command(s)

    def parse_command(self, s):
        match s[0]:
            case 'set-logic':
                self.logic = s[1]
                assert self.logic in logics, f'Unsupported logic {self.logic}. Supported logics: {list(logics.keys())}'
            case 'define-fun':
                _, name, args, res, phi = s
                scope = Scope(self)
                inputs = { n: Const(n, get_sort(s)) for n, s in args }
                for n, c in inputs.items():
                    scope[n] = c
                body = scope.parse_term(phi)
                assert not name in self.funs
                self.funs[name] = (body, inputs.values())
            case 'synth-fun':
                name, fun = parse_synth_fun(self, s)
                assert not name in self.synth_funs
                self.synth_funs[name] = fun
            case 'declare-var':
                _, name, sort = s
                self.vars[name] = Const(name, get_sort(sort))
            case 'constraint':
                scope = ConstraintScope(self)
                for v in self.vars:
                    scope[v] = self.vars[v]
                self.constraints += [ scope.parse_term(s[1]) ]
            case 'check-synth':
                c = Constraint(And(self.constraints),
                               tuple(self.vars.values()),
                               self.fun_appl)
                self.problem = Problem(constraint=c, funcs=self.synth_funs)
                if self.print_problem:
                    print(self.problem)

                if isinstance(self.synth, Check):
                    return
                prgs, stats = self.synth.synth_prgs(self.problem)
                if self.stats:
                    with open(self.stats, 'w') as f:
                        json.dump(stats, f, indent=4)
                if not prgs is None:
                    print('(')
                    for name, p in prgs.items():
                        p = p.copy_propagation().dce()
                        print(p.to_sygus(name))
                    print(')')
                else:
                    print('(fail)')
                    self.result |= 1
            case _:
                print('ignoring command', s)


if __name__ == '__main__':
    res = tyro.cli(SyGuS)
    exit(res.result)