from itertools import combinations as comb
from itertools import permutations as perm
from functools import cached_property
from typing import Dict, Optional, Iterable
from dataclasses import dataclass

from z3 import *

from synth.util import eval_model

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
                assert len(res) > 0, 'cannot evaluate'
        s.pop()
        return res

class Spec:
    def collect_vars(expr):
        res = set()
        def collect(expr):
            if len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED:
                res.add(expr)
            else:
                for c in expr.children():
                    collect(c)
        collect(expr)
        return res

    def __init__(self, name: str, phi: ExprRef, outputs: list[ExprRef], \
                 inputs: list[ExprRef], precond: BoolRef = None):
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
        self.ctx      = phi.ctx
        self.name     = name
        self.arity    = len(inputs)
        self.inputs   = inputs
        self.outputs  = outputs
        self.phi      = phi
        self.precond  = BoolVal(True, ctx=self.ctx) if precond is None else precond
        self.vars     = Spec.collect_vars(phi)
        all_vars      = outputs + inputs
        assert len(set(all_vars)) == len(all_vars), 'outputs and inputs must be unique'
        assert self.vars <= set(all_vars), \
            f'phi must use only out and in variables: {self.vars} vs {all_vars}'
        assert Spec.collect_vars(self.precond) <= set(self.inputs), \
            f'precondition must use input variables only'
        assert Spec.collect_vars(self.phi) <= set(inputs + outputs), \
            f'i-th spec must use only i-th out and input variables {phi}'

    def __repr__(self):
        return self.name

    def __str__(self):
        return self.name

    def translate(self, ctx):
        ins  = [ x.translate(ctx) for x in self.inputs ]
        outs = [ x.translate(ctx) for x in self.outputs ]
        pre  = self.precond.translate(ctx)
        phi  = self.phi.translate(ctx)
        return Spec(self.name, phi, outs, ins, pre)

    @cached_property
    def eval(self):
        s = Solver(ctx=self.ctx)
        s.add(self.precond)
        s.add(self.phi)
        return Eval(self.inputs, self.outputs, s)

    @cached_property
    def out_types(self):
        return [ v.sort() for v in self.outputs ]

    @cached_property
    def in_types(self):
        return [ v.sort() for v in self.inputs ]

    @cached_property
    def is_total(self):
        solver = Solver(ctx=self.ctx)
        solver.add(Not(self.precond))
        return solver.check() == unsat

    @cached_property
    def is_deterministic(self):
        solver  = Solver(ctx=self.ctx)
        ins     = [ FreshConst(ty) for ty in self.in_types ]
        outs    = [ FreshConst(ty) for ty in self.out_types ]
        _, phi  = self.instantiate(outs, ins)
        solver.add(self.precond)
        solver.add(self.phi)
        solver.add(phi)
        solver.add(And([a == b for a, b in zip(self.inputs, ins)]))
        solver.add(Or ([a != b for a, b in zip(self.outputs, outs)]))
        return solver.check() == unsat

    def instantiate(self, outs, ins):
        self_outs = self.outputs
        self_ins  = self.inputs
        assert len(outs) == len(self_outs)
        assert len(ins) == len(self_ins)
        assert all(x.ctx == y.ctx for x, y in zip(self_outs + self_ins, outs + ins))
        phi = substitute(self.phi, list(zip(self_outs + self_ins, outs + ins)))
        pre = substitute(self.precond, list(zip(self_ins, ins)))
        return pre, phi

class Func(Spec):
    def __init__(self, name, phi, precond=BoolVal(True), inputs=[]):
        """Creates an Op from a Z3 expression.

        Attributes:
        name: Name of the operator.
        phi: Z3 expression that represents the semantics of the operator.
        precond: Z3 expression that represents the precondition of the operator.
        inputs: List of input variables in phi. If [] is given, the inputs
            are taken in lexicographical order.
        """
        input_vars = Spec.collect_vars(phi)
        # if no inputs are specified, we take the identifiers in
        # lexicographical order. That's just a convenience
        if len(inputs) == 0:
            inputs = sorted(input_vars, key=lambda v: str(v))
        # create Z3 variable of a given sort
        input_names = set(str(v) for v in inputs)
        names = [ n for n in 'yzr' if not n in input_names ]
        res_ty = phi.sort()
        self.func = phi
        out = Const(names[0], res_ty) if names else FreshConst(res_ty, 'y')
        super().__init__(name, out == phi, [ out ], inputs, precond=precond)

    @cached_property
    def out_type(self):
        return self.out_types[0]

    def translate(self, ctx):
        ins = [ i.translate(ctx) for i in self.inputs ]
        return Func(self.name, \
                    self.func.translate(ctx), \
                    self.precond.translate(ctx), ins)

    @cached_property
    def is_deterministic(self):
        return True

    @cached_property
    def is_commutative(self):
        # if the operator inputs have different sorts, it cannot be commutative
        if len(set(v.sort() for v in self.inputs)) > 1 or len(self.inputs) > 3:
            return False
        ctx     = Context()
        precond = self.precond.translate(ctx)
        func    = self.func.translate(ctx)
        ins     = [ x.translate(ctx) for x in self.inputs ]
        subst   = lambda f, i: substitute(f, list(zip(ins, i)))
        fs = [ And([ subst(precond, a), subst(precond, b), \
                     subst(func, a) != subst(func, b) ], ctx) \
                for a, b in comb(perm(ins), 2) ]
        s = Solver(ctx=ctx)
        s.add(Or(fs, ctx))
        return s.check() == unsat

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

@dataclass(frozen=True)
class Task:
    """A synthesis task."""

    spec: Spec
    """The specification."""

    ops: Dict[Func, Optional[int]]
    """The operator library. The target number gives the number of times
       the operator may be used at most. None indicates no restriction
       on the number of uses."""

    max_const: Optional[int] = None
    """The maximum amount of constants that can be used. None means no limit."""

    const_map: Optional[Dict[ExprRef, Optional[int]]] = None
    """A set of constants that can be used. If given, synthesis must only
       use constants from this set. If None, synthesis must synthesise
       constants as well."""

    theory: Optional[str] = None
    """Optionally specify a theory."""

    def copy_with_different_ops(self, new_ops):
        return Task(self.spec, new_ops, self.max_const, self.const_map, self.theory)

class Prg:
    def __init__(self, ctx, insns, outputs, out_vars, in_vars):
        """Creates a program.

        Attributes:
        spec: The original specification
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
        assert all(insn.ctx == ctx for insn, _ in insns)
        self.ctx          = ctx
        self.insns        = insns
        self.outputs      = outputs
        self.output_names = [ str(v) for v in out_vars ]
        self.input_names  = [ str(v) for v in in_vars ]
        self.out_vars     = out_vars
        self.in_vars      = in_vars
        # this map gives for every temporary/input variable
        # which output variables are set to it
        self.output_map = { }
        for (is_const, v), name in zip(outputs, self.output_names):
            if not is_const:
                self.output_map.setdefault(v, []).append(name)

    def var_name(self, i):
        if i < len(self.input_names):
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

    def eval_clauses_external(self, in_vars, out_vars, const_to_var, ctx, intermediate_vars):
        vars = list(in_vars)
        n_inputs = len(vars)
        def get_val(ins, n_input, ty, p):
            is_const, v = p
            assert is_const or v < len(vars), f'variable out of range: {v}/{len(vars)}'
            return const_to_var(ins, n_input, ty, v) if is_const else vars[v]
        for ins, (insn, opnds) in enumerate(self.insns):
            assert insn.ctx == self.ctx
            subst = [ (i.translate(ctx), get_val(ins, n_input, i.sort(), p)) \
                      for (n_input, (i, p)) in enumerate(zip(insn.inputs, opnds)) ]
            res = Const(self.var_name(ins + n_inputs), insn.func.translate(ctx).sort())
            vars.append(res)
            intermediate_vars.append(res)
            yield res == substitute(insn.func.translate(ctx), subst)
        for n_out, (o, p) in enumerate(zip(out_vars, self.outputs)):
            yield o == get_val(len(self.insns), n_out, o.sort(), p) 

    def eval_clauses(self):
        vars = list(self.in_vars)
        n_inputs = len(vars)
        def get_val(p):
            is_const, v = p
            assert is_const or v < len(vars), f'variable out of range: {v}/{len(vars)}'
            return v if is_const else vars[v]
        for i, (insn, opnds) in enumerate(self.insns):
            assert insn.ctx == self.ctx
            subst = [ (i, get_val(p)) \
                      for i, p in zip(insn.inputs, opnds) ]
            res = Const(self.var_name(i + n_inputs), insn.func.sort())
            vars.append(res)
            yield res == substitute(insn.func, subst)
        for o, p in zip(self.out_vars, self.outputs):
            yield o == get_val(p)

    def dce(self):
        live = set(insn for is_const, insn in self.outputs if not is_const)
        get_idx = lambda i: i + len(self.in_vars)
        for i, (_, args) in reversed(list(enumerate(self.insns))):
            # print(i, live)
            if get_idx(i) in live:
                live.update([ v for c, v in args if not c ])
        m = { i: i for i, _ in enumerate(self.in_vars) }
        new_insns = []
        map_args = lambda args: [ (c, m[v]) if not c else (c, v) for c, v in args ]
        # print(live, m)
        for i, (op, args) in enumerate(self.insns):
            idx = get_idx(i)
            if idx in live:
                m[idx] = get_idx(len(new_insns))
                new_insns.append((op, map_args(args)))
        new_outs = map_args(self.outputs)
        return Prg(self.ctx, new_insns, new_outs, self.out_vars, self.in_vars)

    @cached_property
    def eval(self):
        s = Solver(ctx=self.ctx)
        for p in self.eval_clauses():
            s.add(p)
        return Eval(self.in_vars, self.out_vars, s)

    def __str__(self):
        n_inputs   = len(self.input_names)
        all_names  = [ self.var_name(i) for i in range(len(self) + n_inputs) ]
        max_len    = max(map(len, all_names))
        max_op_len = max(map(lambda x: len(x[0].name), self.insns), default=0)
        jv = lambda args: ', '.join(str(v) if c else self.var_name(v) for c, v in args)
        res = []
        for i, names in self.output_map.items():
            if i < n_inputs:
                res += [ f'{n:{max_len}} = {self.input_names[i]}' for n in names ]
        for i, (op, args) in enumerate(self.insns):
            y = self.var_name(i + n_inputs)
            res += [ f'{y:{max_len}} = {op.name:{max_op_len}} ({jv(args)})' ]
        for names in self.output_map.values():
            for n in names[1:]:
                res += [ f'{n:{max_len}} = {names[0]}']
        for n, (is_const, v) in zip(self.output_names, self.outputs):
            if is_const:
                res += [ f'{n:{max_len}} = {v}' ]
        return '\n'.join(res)

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
