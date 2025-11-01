from itertools import combinations as comb
from itertools import permutations as perm
from functools import cache, cached_property
from dataclasses import dataclass, field
from collections.abc import Sequence

from z3 import *

from synth.util import IgnoreList, eval_model, timer, Debug, no_debug

class Eval:
    def __init__(self, inputs, outputs, solver):
        self.inputs = inputs
        self.outputs = outputs
        self.solver = solver

    def __call__(self, input_vals):
        s = self.solver
        s.push()
        for var, val in zip(self.inputs, input_vals):
            s.add(var == val)
        assert s.check() == sat
        res = eval_model(s.model(), self.outputs)
        s.pop()
        return res

    def sample_n(self, n):
        """Samples the specification n times.
           The result is a list that contains n lists of
           input values that are unique.
           The list may contain less than n elements if there
           are less than n unique inputs.
        """
        res = []
        s = self.solver
        s.push()
        for _ in range(n):
            if s.check() == sat:
                ins  = eval_model(s.model(), self.inputs)
                res += [ ins ]
                s.add(Or([ v != iv for v, iv in zip(self.inputs, ins) ]))
            else:
                return res
        s.pop()
        return res

@dataclass(frozen=True)
class Signature:
    outputs: list[tuple[str, SortRef]]
    """The output variable names and their types."""

    inputs: list[tuple[str, SortRef]]
    """The input variable names and their types."""

    @cached_property
    def out_types(self):
        return [ s for _, s in self.outputs ]

    @cached_property
    def in_types(self):
        return [ s for _, s in self.inputs ]

@dataclass(frozen=True)
class Constraint:
    """\
    A class that represents a synthesis constraint.

    A synthesis constraint is a predicate (phi) over several variables (parameters).
    Phi uses the outputs of functions that are to be synthesized.

    The inputs to these functions can be expressions that use the inputs (parameters)
    of phi. These expressions are given by inputs.
    """

    phi: BoolRef
    """The synthesis constraint."""

    params: tuple[Const]
    """The parameters of the synthesis constraint."""

    function_applications: dict[str, tuple[tuple[tuple[ExprRef], tuple[ExprRef]]]] = field(compare=False)
    """\
    In the constraint, there are applications of functions that are to be synthesized.
    Each function application has a tuple of output variables and a tuple of input expressions.
    The output variables are variables that appear in phi.
    The input expressions are expressions over the parameters of the constraint.
    The function applications are given in this dictionary.
    The key of the dictionary is the name of the function.
    The value of the dictionary is a list of applications of the function.
    """

    def check_signatures(self, signatures: dict[str, Signature]):
        def eq(a, b):
            return len(a) == len(b) and all(x == y for x, y in zip(a, b))
        for name, apps in self.function_applications.items():
            assert name in signatures, f'function {name} not in signatures'
            sig = signatures[name]
            for outs, ins in apps:
                assert eq(tuple(o.sort() for o in outs), sig.out_types), \
                    f'function {name} application has wrong output types'
                assert eq(tuple(i.sort() for i in ins), sig.in_types), \
                    f'function {name} application has wrong input types'

    @cached_property
    def counterexample_eval(self):
        s = Solver()
        s.add(Not(self.phi))
        return Eval(self.params, self.params, s)

    def verify(self, prgs: dict[str, 'Prg'], d: Debug=no_debug, verbose=False):
        verif = Solver()
        verif.add(Not(self.phi))
        for name, applications in self.function_applications.items():
            for outs, args in applications:
                for c in prgs[name].eval_clauses(args, outs):
                    verif.add(c)
        if verbose:
            d('verif_constr', 'verification assertions:', verif)
        stat = {}
        if verbose:
            stat['verif_constraint'] = str(verif)
        with timer() as elapsed:
            res = verif.check()
            verif_time = elapsed()
        stat['verif_time'] = verif_time
        d('verif_time', f'verif time {verif_time / 1e9:.3f}')
        if res == sat:
            # there is a counterexample
            m = verif.model()
            counterexample = eval_model(m, self.params)
            if verbose:
                d('verif_model', 'verification model:', m)
                stat['verif_model'] = str(m)
            stat['counterexample'] = [ str(v) for v in counterexample ]
            return counterexample, stat
        else:
            # we found no counterexample, the program is therefore correct
            stat['counterexample'] = []
            return [], stat

    def add_instance_constraints(self, instance_id: str, synths: dict[str, Any], args: Sequence[ExprRef], res):
        param_subst = list(zip(self.params, args))
        out_subst = []
        tmp = []

        for name, synth in synths.items():
            for k, (out_vars, args) in enumerate(self.function_applications[name]):
                id = f'{instance_id}_{k}'
                inst_args = [ substitute(i, param_subst) for i in args ]
                _, inst_outs = synth.instantiate(id, inst_args, tmp)
                out_subst += list(zip(out_vars, inst_outs))

        phi = substitute(self.phi, param_subst)
        phi = substitute(phi, out_subst)
        res.append(simplify(phi))
        for c in tmp:
            res.append(substitute(simplify(c), out_subst))
        return res

class Spec(Constraint):
    def __init__(self, name: str,
                 phi: BoolRef, outputs: tuple[Const], inputs: tuple[Const],
                 precond: BoolRef = BoolVal(True)):
        """
        Create a specification.

        A specification object represents n specifications each given
        by a Z3 expression (phi).

        inputs is the list of input variables that the n formulas use.
        outputs is the list of output variables that the n formulas use.
        There must be as many variables in outputs as there are formulas in phi.
        Each specification can optionally have a precondition (preconds)
        to express partial functions.
        If preconds is None, all preconditions are True.

        Specifications can be non-deterministic.

        Attributes:
        name: Name of the specification.
        phi: Z3 expression that represents the specification
        outputs: List of output variables in phi.
        inputs: List of input variables in phi.
        precond: A precondition for the specification
            (if None, the precondition is True).

        Note that the names of the variables don't matter because when
        used in the synthesis process their names are substituted by internal names.
        """
        inputs = tuple(inputs)
        outputs = tuple(outputs)
        Constraint.__init__(
            self,
            phi=Implies(precond, phi),
            params=inputs,
            function_applications={ name: [ (outputs, inputs) ] },
        )
        self.name = name

    @cached_property
    def precond(self):
        return self.phi.arg(0)

    @cached_property
    def postcond(self):
        return self.phi.arg(1)

    @cached_property
    def arity(self):
        return len(self.params)

    @cached_property
    def inputs(self):
        return self.params

    @cached_property
    def outputs(self):
        ((outs, _),) = self.function_applications[self.name]
        return outs

    @cached_property
    def in_types(self):
        return tuple(s.sort() for s in self.inputs)

    @cached_property
    def out_types(self):
        return tuple(s.sort() for s in self.outputs)

    @cached_property
    def is_identity(self):
        if not (len(self.inputs) == 1 and len(self.outputs) == 1 and \
                self.inputs[0].sort() == self.outputs[0].sort()):
            return False
        solver   = Solver()
        solver.add(self.precond)
        solver.add(self.phi)
        solver.add(self.inputs[0] != self.outputs[0])
        return solver.check() == unsat

    def instantiate(self, outs, ins):
        assert len(outs) == len(self.outputs)
        assert len(ins) == len(self.inputs)
        phi = substitute(self.phi, list(zip(self.outputs + self.inputs, outs + ins)))
        pre = substitute(self.precond, list(zip(self.inputs, ins)))
        return pre, phi

class Func(Spec):
    def _collect_vars(expr):
        res = set()
        def collect(expr):
            if len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED:
                res.add(expr)
            else:
                for c in expr.children():
                    collect(c)
        collect(expr)
        return res

    def __init__(self, name, phi, precond=BoolVal(True), inputs=None, constraints=None):
        """Creates an Op from a Z3 expression.

        Attributes:
        name: Name of the operator.
        phi: Z3 expression that represents the semantics of the operator.
        precond: Z3 expression that represents the precondition of the operator.
        inputs: List of input variables in phi. If [] is given, the inputs
            are taken in lexicographical order.
        """
        self.constraints = constraints
        input_vars = Func._collect_vars(phi)
        # if no inputs are specified, we take the identifiers in
        # lexicographical order. That's just a convenience
        if inputs is None:
            inputs = tuple(sorted(input_vars, key=lambda v: str(v)))
        # create Z3 variable of a given sort
        input_names = set(str(v) for v in inputs)
        names = tuple(n for n in 'yzr' if not n in input_names)
        res_ty = phi.sort()
        out = Const(names[0], res_ty) if names else FreshConst(res_ty, 'y')
        super().__init__(name, out == phi, (out,), inputs, precond=precond)

    @cached_property
    def func(self):
        return self.phi.arg(1).arg(1)

    @cached_property
    def out_type(self):
        return self.out_types[0]

    @cached_property
    def is_commutative(self):
        # if the operator inputs have different sorts, it cannot be commutative
        if len(set(self.in_types)) > 1 or len(self.inputs) > 3:
            return False
        precond = self.precond
        func    = self.func
        ins     = self.params
        subst   = lambda f, i: substitute(f, list(zip(ins, i)))
        fs = [ And([ subst(precond, a), subst(precond, b), \
                     subst(func, a) != subst(func, b) ]) \
                for a, b in comb(perm(ins), 2) ]
        s = Solver()
        s.add(Or(fs))
        return s.check() == unsat

@dataclass(frozen=True)
class SynthFunc(Signature):
    """A function to be synthesized."""

    ops: dict[Func, int | None]
    """The operator library. The target number gives the number of times
       the operator may be used at most. None indicates no restriction
       on the number of uses."""

    max_const: int | None = None
    """The maximum amount of constants that can be used. None means no limit."""

    const_map: dict[ExprRef, int | None] | None = None
    """A set of constants that can be used. If given, synthesis must only
       use constants from this set. If None, synthesis must synthesise
       constants as well."""

    def copy_with_different_ops(self, new_ops):
        return SynthFunc(self.outputs, self.inputs, new_ops, self.max_const, self.const_map)

@dataclass(frozen=True)
class Problem:
    constraint: Constraint
    funcs: dict[str, SynthFunc]
    theory: str | None = None
    name: str | None = None

def Task(spec: Spec, ops, max_const=None, const_map=None, theory=None):
    synth_func = SynthFunc(
        outputs=[ (str(v), v.sort()) for v in spec.outputs ],
        inputs=[ (str(v), v.sort()) for v in spec.inputs ],
        ops=ops,
        max_const=max_const,
        const_map=const_map,
    )
    return Problem(constraint=spec, funcs={ spec.name: synth_func })

class Prg:
    def __init__(self, sig: Signature, insns, outputs):
        """Creates a program.

        Attributes:
        func: The function that this program implements.
        insns: List of instructions.
            This is a list of pairs where each pair consists
            of an Op and a list of pairs that denotes the arguments to
            the instruction. The first element of the pair is a boolean
            that indicates whether the argument is a constant or not.
            The second element is either the variable number of the
            operand or the constant value of the operand.
        outputs: List of outputs.
            For each output variable in `spec` there is a tuple
            `(is_const, v)` in this list. `is_const` indicates that
            the output is constant. In this case, `v` is a Z3 constant
            that gives the value of the constant output. If `is_const`
            is false, `v` is a Python int that indicates the number of
            the instruction in this program whose value is the output.
            Note that the first n numbers are taken by the n inputs
            of the program.
        """
        self.sig          = sig
        self.insns        = insns
        self.outputs      = outputs
        self.output_names = [ n for n, _ in sig.outputs ]
        self.input_names  = [ n for n, _ in sig.inputs ]
        self.n_inputs     = len(self.input_names)
        # this map gives for every temporary/input variable
        # which output variables are set to it
        self.output_map = { }
        for (is_const, v), name in zip(outputs, self.output_names):
            if not is_const:
                self.output_map.setdefault(v, []).append(name)

    def var_name(self, i):
        if i < self.n_inputs:
            return self.input_names[i]
        elif i in self.output_map:
            return self.output_map[i][0]
        else:
            return f'x{i}'

    def __eq__(self, other):
        return self.insns == other.insns and \
               self.outputs == other.outputs

    def __len__(self):
        return len(self.insns)

    def _is_insn(self, v):
        return self.n_inputs <= v < self.n_inputs + len(self.insns)

    def _get_insn(self, v):
        return self.insns[v - self.n_inputs] if self._is_insn(v) else None

    def eval_clauses(self, in_vars, out_vars, instance_id=None,
                     const_translate=lambda ins, n, ty, v: v,
                     intermediate_vars=IgnoreList()):
        suffix = f'_{instance_id}' if instance_id else ''
        vars = list(in_vars)
        n_inputs = len(vars)
        def get_val(ins, n_input, ty, p):
            is_const, v = p
            assert is_const or v < len(vars), f'variable out of range: {v}/{len(vars)}'
            return const_translate(ins, n_input, ty, v) if is_const else vars[v]
        for ins, (insn, opnds) in enumerate(self.insns):
            subst = [ (i, get_val(ins, n_input, i.sort(), p)) \
                      for (n_input, (i, p)) in enumerate(zip(insn.inputs, opnds)) ]
            res = Const(f'{self.var_name(ins + n_inputs)}{suffix}', insn.func.sort())
            vars.append(res)
            intermediate_vars.append(res)
            yield And([substitute(insn.precond, subst), res == substitute(insn.func, subst)])
        for n_out, (o, p) in enumerate(zip(out_vars, self.outputs)):
            yield o == get_val(len(self.insns), n_out, o.sort(), p)

    def copy_propagation(self):
        @cache
        def prop(val):
            if res := self._get_insn(val):
                op, args = res
                if op.is_identity:
                    c, v = args[0]
                    if not c:
                        return prop(v)
            return val

        new_insns = [ (op, [ (c, prop(v) if not c else v) for c, v in args ])
                        for op, args in self.insns ]
        new_outs  = [ (c, prop(v) if not c else v) for c, v in self.outputs ]
        return Prg(self.sig, new_insns, new_outs)

    def dce(self):
        live = set(insn for is_const, insn in self.outputs if not is_const)
        get_idx = lambda i: i + self.n_inputs
        for i, (_, args) in reversed(list(enumerate(self.insns))):
            # print(i, live)
            if get_idx(i) in live:
                live.update([ v for c, v in args if not c ])
        m = { i: i for i in range(self.n_inputs) }
        new_insns = []
        map_args = lambda args: [ (c, m[v]) if not c else (c, v) for c, v in args ]
        for i, (op, args) in enumerate(self.insns):
            idx = get_idx(i)
            if idx in live:
                m[idx] = get_idx(len(new_insns))
                new_insns.append((op, map_args(args)))
        new_outs = map_args(self.outputs)
        return Prg(self.sig, new_insns, new_outs)

    @cached_property
    def eval(self):
        s = Solver()
        for p in self.eval_clauses():
            s.add(p)
        return Eval(self.in_vars, self.out_vars, s)

    def to_string(self, sep='\n'):
        all_names  = [ self.var_name(i) for i in range(len(self) + self.n_inputs) ]
        max_len    = max(map(len, all_names))
        max_op_len = max(map(lambda x: len(x[0].name), self.insns), default=0)
        jv = lambda args: ', '.join(str(v) if c else self.var_name(v) for c, v in args)
        res = []
        for i, names in self.output_map.items():
            if i < self.n_inputs:
                res += [ f'{n:{max_len}} = {self.input_names[i]}' for n in names ]
        for i, (op, args) in enumerate(self.insns):
            y = self.var_name(i + self.n_inputs)
            res += [ f'{y:{max_len}} = {op.name:{max_op_len}} ({jv(args)})' ]
        for names in self.output_map.values():
            for n in names[1:]:
                res += [ f'{n:{max_len}} = {names[0]}']
        for n, (is_const, v) in zip(self.output_names, self.outputs):
            if is_const:
                res += [ f'{n:{max_len}} = {v}' ]
        return sep.join(res)

    def __str__(self):
        return self.to_string(sep='; ')

    def to_sygus(self, name, sep=' '):
        assert len(self.outputs) == 1, 'sygus output only supports single output programs'
        def arg_to_sexpr(is_const, v):
            return str(v) if is_const else self.var_name(v)
        def insn_to_sexpr(op, args):
            return f'({op.name} {" ".join(arg_to_sexpr(c, v) for c, v in args)})'
        res = [ f'(define-fun {name} (' ]
        res[0] += ' '.join([ f'({n} {ty.sexpr()})' for n, ty in self.sig.inputs ])
        res[0] += f') {self.sig.outputs[0][1].sexpr()}'
        to_close = 1
        for i, names in self.output_map.items():
            if i < self.n_inputs:
                res += [ f'(let ({n} {self.input_names[i]})' for n in names ]
                to_close += 1
        for i, (op, args) in enumerate(self.insns):
            y = self.var_name(i + self.n_inputs)
            res += [ f'(let ({y} {insn_to_sexpr(op, args)})' ]
            to_close += 1
        for n, (is_const, v) in zip(self.output_names, self.outputs):
            if is_const:
                res += [ f'(let ({n} {v})' ]
                to_close += 1
        res += [ self.output_names[0] ]
        res = sep.join(res)
        return res + ')' * to_close

    def print_graphviz(self, file):
        constants = {}
        def print_arg(node, i, is_const, v):
            if is_const:
                if not v in constants:
                    constants[v] = f'const{len(constants)}'
                    print(f'  {constants[v]} [label="{v}"];')
                v = constants[v]
            print(f'  {node} -> {v} [label="{i}"];')

        save_stdout, sys.stdout = sys.stdout, file
        n_inputs = len(self.input_names)
        print(f"""digraph G {{
  rankdir=BT
  {{
    rank = same;
    edge[style=invis];
    rankdir = LR;
""")
        for i, inp in enumerate(self.input_names):
            print(f'    {i} [label="{inp}"];')
        print(f"""
    { ' -> '.join([str(i) for i in range(n_inputs)])};
  }}""")

        for i, (op, args) in enumerate(self.insns):
            node = i + n_inputs
            print(f'  {node} [label="{op.name}",ordering="out"];')
            for i, (is_const, v) in enumerate(args):
                print_arg(node, i, is_const, v)
        print(f'  return [label="return",ordering="out"];')
        for i, (is_const, v) in enumerate(self.outputs):
            print_arg('return', i, is_const, v)
        print('}')
        sys.stdout = save_stdout

def create_bool_func(func):
    import re
    def is_power_of_two(x):
        return (x & (x - 1)) == 0
    if re.match('^0[bodx]', func):
        base = { 'b': 2, 'o': 8, 'd': 10, 'x': 16 }[func[1]]
        func = func[2:]
    else:
        base = 16
    assert is_power_of_two(base), 'base of the number must be power of two'
    bits_per_digit = int(math.log2(base))
    n_bits = len(func) * bits_per_digit
    bits = bin(int(func, base))[2:].zfill(n_bits)
    assert len(bits) == n_bits
    assert is_power_of_two(n_bits), 'length of function must be power of two'
    n_vars  = int(math.log2(n_bits))
    vars    = [ Bool(f'x{i}') for i in range(n_vars) ]
    clauses = []
    binary  = lambda i: bin(i)[2:].zfill(n_vars)
    for i, bit in enumerate(bits):
        if bit == '1':
            clauses += [ And([ vars[j] if b == '1' else Not(vars[j]) \
                            for j, b in enumerate(binary(i)) ]) ]
    return Func(func, Or(clauses) if len(clauses) > 0 else BoolVal(False), inputs=vars)
