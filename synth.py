#! /usr/bin/env python3

import random
import itertools
import time
import json

from itertools import combinations as comb
from itertools import permutations as perm
from functools import cached_property, lru_cache

from contextlib import contextmanager
from typing import Any

from z3 import *

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

class Spec:
    def __init__(self, name, phi, outputs, inputs):
        """
        Create a specification from a Z3 expression.

        Attributes:
        name: Name of the specification.
        phi: Z3 expression that represents the specification.
        outputs: List of output variables in phi.
        inputs: List of input variables in phi.

        Note that the names of the variables don't matter because when
        used in the synthesis process their names are substituted by internal names.
        """
        self.name    = name
        self.arity   = len(inputs)
        self.inputs  = inputs
        self.outputs = outputs
        self.phi     = phi
        self.vars    = collect_vars(phi)

        all_vars     = outputs + inputs
        assert len(set(all_vars)) == len(all_vars), 'outputs and inputs must be unique'
        assert self.vars <= set(all_vars), \
            f'phi must use only out and in variables: {self.vars} vs {all_vars}'

    def __str__(self):
        return self.name

    @cached_property
    def out_types(self):
        return [ v.sort() for v in self.outputs ]

    @cached_property
    def in_types(self):
        return [ v.sort() for v in self.inputs ]

    def instantiate(self, outs, ins, ctx):
        assert len(outs) == len(self.outputs)
        assert len(ins) == len(self.inputs)
        assert all([x.ctx == ctx for x in ins + outs])
        outputs = [x.translate(ctx) if x.ctx != ctx else x for x in self.outputs]
        inputs =  [x.translate(ctx) if x.ctx != ctx else x for x in self.inputs]
        phi = self.phi.translate(ctx) if self.phi.ctx != ctx else self.phi
        return substitute(phi, list(zip(outputs + inputs, outs + ins)))

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
        input_vars = collect_vars(phi)
        # if no inputs are specified, we take the identifiers in
        # lexicographical order. That's just a convenience
        if len(inputs) == 0:
            inputs = sorted(input_vars, key=lambda v: str(v))
        # create an output variable name that is not already present
        i = 0
        while out := f'out_{i}' in set(str(v) for v in inputs):
            i += 1
        # check if precondition uses only variables that are in phi
        assert collect_vars(precond) <= input_vars, \
            'precondition uses variables that are not in phi'
        # create Z3 variable of a given sort
        self.res_ty = phi.sort()
        self.func = phi
        self.precond = precond
        out = Const(out, self.res_ty)
        super().__init__(name, And([precond, out == phi]), [ out ], inputs)

    @cached_property
    def is_commutative(self):
        # if the operator inputs have different sorts, it cannot be commutative
        if len(set(v.sort() for v in self.inputs)) > 1:
            return False
        ctx   = Context()
        subst = lambda f, i: substitute(f, list(zip(self.inputs, i)))
        ins = [ Const(f'{self.name}_in_comm_{i}', ty) \
                for i, ty in enumerate(self.in_types) ]
        fs = [ And([ subst(self.precond, a), subst(self.precond, b), \
                     subst(self.func, a) != subst(self.func, b) ]) \
                for a, b in comb(perm(ins), 2) ]
        s = Solver(ctx=ctx)
        s.add(Or(fs).translate(ctx))
        return s.check() == unsat

    # Used for instructions of type Implies(insn_0_op == XY)
    def set_z3_symbol(self, z3_id):
        self.z3_id = z3_id

    # Used for instructions of type Implies(insn_0_op == XY)
    def get_z3_symbol(self):
        return self.z3_id

class SpecWithContext:

    def get_var(self, name, ty, ctx):
        var = Const(name, ty)
        if var.ctx != ctx:
            var = var.translate(ctx)
        return var

    def __init__(self, spec: Spec, context: Context, ops: list[Func]):
        self.spec    = spec
        self.context = context
        self.verif_solver  = Solver(ctx=self.context)
        self.inputs  = [ self.get_var(f'{spec.name}_in_{i}', ty, self.context)  for i, ty in enumerate(spec.in_types) ]
        self.outputs = [ self.get_var(f'{spec.name}_out_{i}', ty, self.context) for i, ty in enumerate(spec.out_types) ]
        instantiated = spec.instantiate(self.outputs, self.inputs, self.context)
        self.verif_solver.add(instantiated)

        self.ops     = ops
        (op_sort, cons) = EnumSort("Operator", list(op.name for op in ops), ctx=self.context)
        self.op_sort = op_sort
        for i, op in enumerate(ops):
            op.set_z3_symbol(cons[i])
        self.ops_by_symbol = { op.get_z3_symbol(): op for op in ops}


class Prg:
    def __init__(self, input_names, insns, outputs):
        """Creates a program.

        Attributes:
        input_names: list of names of the inputs
        insns: List of instructions.
            This is a list of pairs where each pair consists
            of an Op and a list of pairs that denotes the arguments to
            the instruction. The first element of the pair is a boolean
            that indicates whether the argument is a constant or not.
            The second element is either the variable number of the
            operand or the constant value of the operand.
        outputs: List of variable numbers that constitute the output.
        """
        self.input_names = input_names
        self.insns = insns
        self.outputs = outputs

    def var_name(self, i):
        return self.input_names[i] if i < len(self.input_names) else f'x{i}'

    def __len__(self):
        return len(self.insns)

    def __str__(self):
        n_inputs = len(self.input_names)
        jv   = lambda args: ', '.join(str(v) if c else self.var_name(v) for c, v in args)
        res = ''.join(f'{self.var_name(i + n_inputs)} = {op.name}({jv(args)})\n' \
                      for i, (op, args) in enumerate(self.insns))
        return res + f'return({jv(self.outputs)})'

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

@contextmanager
def timer():
    start = time.process_time_ns()
    yield lambda: time.process_time_ns() - start

def synth_n(spec_solver: SpecWithContext, n_insns, \
            debug=0, max_const=None, output_prefix=None, \
            opt_no_dead_code=True, opt_no_cse=True, opt_const=True, \
            opt_commutative=True):

    """Synthesize a program that computes the given functions.

    Attributes:
    spec: The specification of the program to be synthesized.
    ops: List of operations that can be used in the program.
    n_insn: Number of instructions in the program.
    verif: The verification solver. If None, a new solver is created.
    debug: Debug level. 0: no debug output, >0 more debug output.
    max_const: Maximum number of constants that can be used in the program.
    output_prefix: If set to a string, the synthesizer dumps every SMT problem to a file with that prefix.

    Returns:
    A triple (prg, stats, prg) where prg is the synthesized program (or None
    if no program has been found), stats is a list of statistics for each
    iteration of the synthesis loop, and verif is the used/created verification
    solver (to be used in potential subsequent calls to synth_n).
    """

    # create a debug function that prints only if the debug level is high enough
    def d(level, *args):
        if debug >= level:
            print(*args)

    d(1, 'size', n_insns)

    context   = spec_solver.context


    ops       = spec_solver.ops
    spec      = spec_solver.spec
    in_tys    = spec.in_types
    out_tys   = spec.out_types
    n_inputs  = len(in_tys)
    n_outputs = len(out_tys)
    out_insn  = n_inputs + n_insns
    length    = out_insn + 1

    max_arity = max(op.arity for op in ops)
    arities   = [ 0 ] * n_inputs + [ max_arity ] * n_insns + [ n_outputs ]

    # create map of types to their id
    n_types = 0
    types = {}
    for op in ops:
        for ty in op.out_types + op.in_types:
            if not ty in types:
                types[ty] = n_types
                n_types += 1

    bv_sort = lambda n: BitVecSort(len(bin(n)) - 2, ctx=context)
    ty_sort = bv_sort(n_types)
    op_sort = spec_solver.op_sort
    ln_sort = bv_sort(length)

    # get the verification solver and its input and output variables
    eval_ins  = spec_solver.inputs
    eval_outs = spec_solver.outputs
    verif     = spec_solver.verif_solver

    def eval_spec(input_vals):
        """Evaluates the specification on the given inputs.
           The list has to be of length n_inputs.
           If you want to not set an input, use None.
        """
        assert len(input_vals) == n_inputs
        verif.push()
        for i, (v, e) in enumerate(zip(input_vals, eval_ins)):
            if not v is None:
                verif.add(e == v)
        res = verif.check()
        assert res == sat, 'specification is unsatisfiable'
        m = verif.model()
        verif.pop()
        return [ m[v] for v in eval_ins ], [ m[v] for v in eval_outs ]

    @lru_cache
    def get_var(ty, name):
        cons = Const(name, ty)
        if cons.ctx != context:
            cons = cons.translate(context)
        return cons

    @lru_cache
    def ty_name(ty):
        return str(ty).replace(' ', '_') \
                      .replace(',', '_') \
                      .replace('(', '_') \
                      .replace(')', '_')

    def var_insn_op(insn):
        return get_var(op_sort, f'insn_{insn}_op')

    def var_insn_opnds_is_const(insn):
        for opnd in range(arities[insn]):
            yield get_var(BoolSort(ctx=context), f'insn_{insn}_opnd_{opnd}_is_const')

    def var_insn_op_opnds_const_val(insn, opnd_tys):
        for opnd, ty in enumerate(opnd_tys):
            yield get_var(ty, f'insn_{insn}_opnd_{opnd}_{ty_name(ty)}_const_val')

    def var_insn_opnds(insn):
        for opnd in range(arities[insn]):
            yield get_var(ln_sort, f'insn_{insn}_opnd_{opnd}')

    def var_insn_opnds_val(insn, tys, instance):
        for opnd, ty in enumerate(tys):
            yield get_var(ty, f'insn_{insn}_opnd_{opnd}_{ty_name(ty)}_{instance}')

    def var_outs_val(instance):
        for opnd in var_insn_opnds_val(out_insn, out_tys, instance):
            yield opnd

    def var_insn_opnds_type(insn):
        for opnd in range(arities[insn]):
            yield get_var(ty_sort, f'insn_{insn}_opnd_type_{opnd}')

    def var_insn_res(insn, ty, instance):
        return get_var(ty, f'insn_{insn}_res_{ty_name(ty)}_{instance}')

    def var_insn_res_type(insn):
        return get_var(ty_sort, f'insn_{insn}_res_type')

    def var_input_res(insn, instance):
        return var_insn_res(insn, in_tys[insn], instance)

    def is_op_insn(insn):
        return insn >= n_inputs and insn < length - 1

    def add_constr_wfp(solver: Solver):
        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for insn in range(length):
            for v in var_insn_opnds(insn):
                con = ULE(v, insn - 1)
                solver.add(ULE(v, insn - 1))

        # for all instructions that get an op
        # add constraints that set the type of an instruction's operands and result type
        for insn in range(n_inputs, length - 1):
            for op in ops:
                # add constraints that set the result type of each instruction
                solver.add(Implies(var_insn_op(insn) == op.get_z3_symbol(), \
                                   var_insn_res_type(insn) == types[op.res_ty]))
                # add constraints that set the type of each operand
                for op_ty, v in zip(op.in_types, var_insn_opnds_type(insn)):
                    solver.add(Implies(var_insn_op(insn) == op.get_z3_symbol(), v == types[op_ty]))

            # constrain the op variable to the number of ops
            #o = var_insn_op(insn)
            #solver.add(ULE(o, len(ops) - 1))

        # define types of inputs
        for inp, ty in enumerate(in_tys):
            solver.add(var_insn_res_type(inp) == types[ty])

        # define types of outputs
        for v, ty in zip(var_insn_opnds_type(out_insn), out_tys):
            solver.add(v == types[ty])

        # constrain types of outputs
        for insn in range(n_inputs, length):
            for other in range(0, insn):
                for opnd, c, ty in zip(var_insn_opnds(insn), \
                                       var_insn_opnds_is_const(insn), \
                                       var_insn_opnds_type(insn)):
                    solver.add(Implies(Not(c), Implies(opnd == other, \
                                       ty == var_insn_res_type(other))))

        # bound the type variables
        for insn in range(n_inputs, length):
            for ty in var_insn_opnds_type(insn):
                solver.add(ULE(ty, n_types - 1))
            res_type = var_insn_res_type(insn)
            solver.add(ULE(res_type, n_types - 1))

        # Add a constraint for the maximum amount of constants.
        # The output instruction is exempt because we need to be able
        # to synthesize constant outputs correctly.
        max_const_ran = range(n_inputs, length - 1)
        if not max_const is None and len(max_const_ran) > 0:
            solver.add(AtMost(*[ v for insn in max_const_ran \
                                   for v in var_insn_opnds_is_const(insn)], max_const))

    def add_constr_opt(solver: Solver):
        for insn in range(n_inputs, out_insn):
            op_var = var_insn_op(insn)
            for op in ops:
                # if operator is commutative, force the operands to be in ascending order
                if opt_commutative and op.is_commutative:
                    opnds = list(var_insn_opnds(insn))
                    c = [ ULE(l, u) for l, u in zip(opnds[:op.arity - 1], opnds[1:]) ]
                    if len(c) > 0:
                        solver.add(Implies(op_var == op.get_z3_symbol(), And(c)))

                # force that at least one operand is not-constant
                # otherwise, the operation is not needed because it would be fully constant
                if opt_const:
                    vars = [ Not(v) for v in var_insn_opnds_is_const(insn) ][:op.arity]
                    assert len(vars) > 0
                    solver.add(Implies(op_var == op.get_z3_symbol(), Or(vars)))

            # Computations must not be replicated: If an operation appears again
            # in the program, at least one of the operands must be different from
            # a previous occurrence of the same operation.
            if opt_no_cse:
                for other in range(n_inputs, insn):
                    un_eq = [ p != q for p, q in zip(var_insn_opnds(insn), var_insn_opnds(other)) ]
                    assert len(un_eq) > 0
                    solver.add(Implies(op_var == var_insn_op(other), Or(un_eq)))

        # no dead code: each produced value is used
        if opt_no_dead_code:
            for prod in range(n_inputs, length):
                opnds = [ prod == v for cons in range(prod + 1, length) for v in var_insn_opnds(cons) ]
                if len(opnds) > 0:
                    solver.add(Or(opnds))

    def iter_opnd_info(insn, tys, instance):
        return zip(tys, \
                   var_insn_opnds(insn), \
                   var_insn_opnds_val(insn, tys, instance), \
                   var_insn_opnds_is_const(insn), \
                   var_insn_op_opnds_const_val(insn, tys))

    def add_constr_conn(solver, insn, tys, instance):
        for ty, l, v, c, cv in iter_opnd_info(insn, tys, instance):
            # if the operand is a constant, its value is the constant value
            solver.add(Implies(c, v == cv))
            # else, for other each instruction preceding it ...
            for other in range(insn):
                r = var_insn_res(other, ty, instance)
                # ... the operand is equal to the result of the instruction
                solver.add(Implies(Not(c), Implies(l == other, v == r)))

    def add_constr_instance(solver, instance):
        # for all instructions that get an op
        for insn in range(n_inputs, length - 1):
            # add constraints to select the proper operation
            op_var = var_insn_op(insn)
            for op in ops:
                res = var_insn_res(insn, op.res_ty, instance)
                opnds = list(var_insn_opnds_val(insn, op.in_types, instance))
                solver.add(Implies(op_var == op.get_z3_symbol(), op.instantiate([ res ], opnds, context)))
            # connect values of operands to values of corresponding results
            for op in ops:
                add_constr_conn(solver, insn, op.in_types, instance)
        # add connection constraints for output instruction
        add_constr_conn(solver, out_insn, out_tys, instance)

    def add_constr_io_sample(solver, instance, io_sample):
        # add input value constraints
        in_vals, out_vals = io_sample
        assert len(in_vals) == n_inputs and len(out_vals) == n_outputs
        for inp, val in enumerate(in_vals):
            if not val is None:
                res = var_input_res(inp, instance)
                solver.add(res == val)
        for out, val in zip(var_outs_val(instance), out_vals):
            if not val is None:
                solver.add(out == val)

    def add_constr_sol_for_verif(model):
        for insn in range(length):
            if is_op_insn(insn):
                v = var_insn_op(insn)
                if model[v] is not None:
                    op = spec_solver.ops_by_symbol[model[v]] # .as_long()
                else: # the operator is irrelevant
                    op = spec_solver.ops[0]
                tys = op.in_types
                verif.add(op.get_z3_symbol() == v)
            else:
                tys = out_tys

            # set connection values
            for _, opnd, v, c, cv in iter_opnd_info(insn, tys, 'verif'):
                is_const = is_true(model[c]) if not model[c] is None else False
                verif.add(is_const == c)
                if is_const:
                    verif.add(model[cv] == v)
                else:
                    verif.add(model[opnd] == opnd)

    def add_constr_spec_verif():
        for inp, e in enumerate(eval_ins):
            verif.add(var_input_res(inp, 'verif') == e)
        verif.add(Or([v != e for v, e in zip(var_outs_val('verif'), eval_outs)]))

    def create_prg(model):
        def prep_opnds(insn, tys):
            for _, opnd, v, c, cv in iter_opnd_info(insn, tys, 'verif'):
                is_const = is_true(model[c]) if not model[c] is None else False
                yield (is_const, model[cv] if is_const else model[opnd].as_long())

        insns = []
        for insn in range(n_inputs, length - 1):
            if model[var_insn_op(insn)] is not None:
                op     = spec_solver.ops_by_symbol[model[var_insn_op(insn)]]
            else:
                op    = spec_solver.ops[0]
            opnds  = [ v for v in prep_opnds(insn, op.in_types) ]#[:op.arity]
            insns += [ (op, opnds) ]

        outputs     = [ v for v in prep_opnds(out_insn, out_tys) ]
        input_names = [ str(v) for v in spec.inputs ]
        return Prg(input_names, insns, outputs)

    def write_smt2(solver, *args):
        if not output_prefix is None:
            filename = f'{output_prefix}_{"_".join(str(a) for a in args)}.smt2'
            with open(filename, 'w') as f:
                print(solver.to_smt2(), file=f)

    # setup the synthesis solver
    synth = Solver(ctx = context)
    add_constr_wfp(synth)
    add_constr_opt(synth)

    stats = []
    # sample the specification once for an initial set of input samples
    sample = eval_spec([None] * n_inputs)
    i = 0
    while True:
        stat = {}
        stats += [ stat ]

        d(1, 'sample', i, sample)
        add_constr_instance(synth, i)
        add_constr_io_sample(synth, i, sample)

        d(4, 'synth', i, synth)
        write_smt2(synth, 'synth', n_insns, i)
        with timer() as elapsed:
            res = synth.check()
            d(3, 'synthesis statistics', synth.statistics())
            synth_time = elapsed()
            d(2, f'synth time: {synth_time / 1e9:.3f}')
            stat['synth'] = synth_time

        if res == sat:
            # if sat, we found location variables
            m = synth.model()
            prg = create_prg(m)
            stat['prg'] = str(prg).replace('\n', '; ')

            d(3, 'model: ', m)
            d(2, 'program: ', prg)

            # push a new verification solver state
            verif.push()
            # Add constraints that represent the instructions of
            # the synthesized program
            add_constr_instance(verif, 'verif')
            # Add constraints that relate the specification to
            # the inputs and outputs of the synthesized program
            add_constr_spec_verif()
            # add constraints that set the location variables
            # in the verification constraint
            add_constr_sol_for_verif(m)

            d(4, 'verif', i, verif)
            write_smt2(verif, 'verif', n_insns, i)
            with timer() as elapsed:
                res = verif.check()
                d(3, 'verification statistics', verif.statistics())
                verif_time = elapsed()
                stat['verif'] = verif_time
                d(2, f'verif time {verif_time / 1e9:.3f}')

            if res == sat:
                # there is a counterexample, reiterate
                m = verif.model()
                d(3, 'verification model', m)
                verif.pop()
                sample = eval_spec([ m[e] for e in eval_ins ])
                i += 1
            else:
                # clean up the verification solver state
                verif.pop()
                # we found no counterexample, the program is therefore correct
                d(1, 'no counter example found')
                return prg, stats
        else:
            assert res == unsat
            d(1, f'synthesis failed for size {n_insns}')
            return None, stats

def synth(spec: Spec, ops: list[Func], iter_range, **args):
    """Synthesize a program that computes the given functions.

    Attributes:
    spec: List of functions that the program has to compute.
        All functions have to have the same number of operands and
        have to agree on their operand types.
    ops: List of operations that can be used in the program.
    iter_range: Range of program lengths that are tried.
    args: arguments passed to the synthesizer

    Returns:
    A tuple (prg, stats) where prg is the synthesized program (or None
    if no program has been found) and stats is a list of statistics for each
    iteration of the synthesis loop.
    """

    all_stats = []
    context = Context() # main_ctx() # Context()
    spec_solver = SpecWithContext(spec, context, ops)
    for n_insns in iter_range:
        with timer() as elapsed:
            prg, stats = synth_n(spec_solver, n_insns, **args)
            all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
            if not prg is None:
                return prg, all_stats
    return None, all_stats

class Bl:
    w, x, y, z = Bools('w x y z')
    i2 = [x, y]
    i3 = i2 + [z]
    i4 = [w] + i3
    not1  = Func('not',     Not(x))          #7404
    nand2 = Func('nand2',   Not(And(i2)))    #7400
    nor2  = Func('nor2',    Not(Or(i2)))     #7402
    and2  = Func('and2',    And(i2))         #7408
    or2   = Func('or2',     Or(i2))          #7432
    xor2  = Func('xor2',    Xor(x, y))       #7486

    and3  = Func('and3',    And(i3))         #7408
    or3   = Func('or3',     Or(i3))          #7432

    nand3 = Func('nand3',   Not(And(i3)))    #7410
    nor3  = Func('nor3',    Not(Or(i3)))     #7427
    and3  = Func('and3',    And(i3))         #7411

    nand4 = Func('nand4',   Not(And(i4)))    #7420
    and4  = Func('and4',    And(i4))         #7421
    nor4  = Func('nor4',    Not(Or(i4)))     #7429

    mux2  = Func('mux2',    Or(And(w, x), And(Not(w), y)))
    maj3  = Func('maj3',    Or(And(x, y), And(x, z), And(y, z)))
    eq2   = Func('eq2',     x == y)

class Bv:
    def __init__(self, width):
        self.width = width
        self.ty    = BitVecSort(width)

        x, y = BitVecs('x y', width)
        shift_precond = And([y >= 0, y < width])
        div_precond = y != 0
        z = BitVecVal(0, width)
        o = BitVecVal(1, width)

        l = [
            Func('neg',  -x),
            Func('not',  ~x),
            Func('and',  x & y),
            Func('or' ,  x | y),
            Func('xor',  x ^ y),
            Func('add',  x + y),
            Func('sub',  x - y),
            Func('mul',  x * y),
            Func('div',  x / y),
            Func('udiv', UDiv(x, y), precond=div_precond),
            Func('smod', x % y,      precond=div_precond),
            Func('urem', URem(x, y), precond=div_precond),
            Func('srem', SRem(x, y), precond=div_precond),
            Func('shl',  (x << y),   precond=shift_precond),
            Func('lshr', LShR(x, y), precond=shift_precond),
            Func('ashr', x >> y,     precond=shift_precond),
            Func('uge',  If(UGE(x, y), o, z)),
            Func('ult',  If(ULT(x, y), o, z)),
            Func('sge',  If(x >= y, o, z)),
            Func('slt',  If(x < y, o, z)),
        ]

        for op in l:
            setattr(self, f'{op.name}_', op)

def create_random_formula(inputs, size, ops, seed=0x5aab199e):
    random.seed(a=seed, version=2)
    assert size > 0
    def create(size):
        nonlocal inputs, ops, seed
        assert size > 0
        if size == 1:
            return random.choice(inputs)
        elif size == 2:
            op = random.choice([op for op, n in ops if n == 1])
            return op(create(1))
        else:
            size -= 1
            op, arity = random.choice(ops)
            assert arity <= 2
            if arity == 1:
                return op(create(size))
            else:
                assert arity == 2
                szl = random.choice(range(size - 1)) + 1
                szr = size - szl
                return op(create(szl), create(szr))
    return create(size)

def create_random_dnf(inputs, clause_probability=50, seed=0x5aab199e):
    """Creates a random DNF formula.

    Attributes:
    inputs: List of Z3 variables that determine the number of variables in the formula.
    clause_probability: Probability of a clause being added to the formula.
    seed: Seed for the random number generator.

    This function iterates over *all* clauses, and picks based on the clause_probability if a clause is added to the formula. Therefore, the function's running time is exponential in the number of variables.
    """
    # sample function results
    random.seed(a=seed, version=2)
    clauses = []
    for vals in itertools.product(*[range(2)] * len(inputs)):
        if random.choice(range(100)) < clause_probability:
            clauses += [ And([ inp if pos else Not(inp) for inp, pos in zip(inputs, vals) ]) ]
    return Or(clauses)

class TestBase:
    def __init__(self, maxlen=10, debug=0, stats=False, graph=False, tests=None, write=None):
        self.debug = debug
        self.max_length = maxlen
        self.write_stats = stats
        self.write_graph = graph
        self.tests = tests
        self.write = write

    def do_synth(self, name, spec, ops, desc='', **args):
        desc = f' ({desc})' if len(desc) > 0 else ''
        print(f'{name}{desc}: ', end='', flush=True)
        output_prefix = name if self.write else None
        prg, stats = synth(spec, ops, range(self.max_length), \
                           debug=self.debug, output_prefix=output_prefix, **args)
        total_time = sum(s['time'] for s in stats)
        print(f'{total_time / 1e9:.3f}s')
        if self.write_stats:
            with open(f'{name}.json', 'w') as f:
                json.dump(stats, f, indent=4)
        if self.write_graph:
            with open(f'{name}.dot', 'w') as f:
                prg.print_graphviz(f)
        print(prg)
        return total_time

    def run(self):
        # iterate over all methods in this class that start with 'test_'
        if self.tests is None:
            tests = [ name for name in dir(self) if name.startswith('test_') ]
        else:
            tests = [ 'test_' + s for s in self.tests.split(',') ]
        tests.sort()
        total_time = 0
        for name in tests:
            total_time += getattr(self, name)()
            print('')
        print(f'total time: {total_time / 1e9:.3f}s')

class Tests(TestBase):
    def random_test(self, name, n_vars, create_formula):
        ops  = [ Bl.and2, Bl.or2, Bl.xor2, Bl.not1 ]
        spec = Func('rand', create_formula([ Bool(f'x{i}') for i in range(n_vars) ]))
        return self.do_synth(name, spec, ops, max_const=0)

    def test_rand(self, size=40, n_vars=4):
        ops = [ (And, 2), (Or, 2), (Xor, 2), (Not, 1) ]
        f   = lambda x: create_random_formula(x, size, ops)
        return self.random_test('rand_formula', n_vars, f)

    def test_rand_dnf(self, n_vars=4):
        f = lambda x: create_random_dnf(x)
        return self.random_test('rand_dnf', n_vars, f)

    def test_and(self):
        return self.do_synth('and', Bl.and2, [ Bl.and2 ])

    def test_xor(self):
        ops  = [ Bl.nand2 ]
        return self.do_synth('xor', Bl.xor2, ops)

    def test_mux(self):
        return self.do_synth('mux', Bl.mux2, [ Bl.and2, Bl.xor2 ])

    def test_zero(self):
        spec = Func('zero', Not(Or([ Bool(f'x{i}') for i in range(8) ])))
        ops  = [ Bl.and2, Bl.nand2, Bl.or2, Bl.nor2, Bl.nand3, Bl.nor3, Bl.nand4, Bl.nor4 ]
        return self.do_synth('zero', spec, ops)

    def test_add(self):
        x, y, ci, s, co = Bools('x y ci s co')
        add = And([co == AtLeast(x, y, ci, 2), s == Xor(x, Xor(y, ci))])
        spec = Spec('adder', add, [s, co], [x, y, ci])
        ops = [ Bl.xor2, Bl.and2, Bl.or2 ]
        return self.do_synth('add', spec, ops, desc='1-bit full adder')

    def test_add_apollo(self):
        x, y, ci, s, co = Bools('x y ci s co')
        add = And([co == AtLeast(x, y, ci, 2), s == Xor(x, Xor(y, ci))])
        spec = Spec('adder', add, [s, co], [x, y, ci])
        return self.do_synth('add_nor3', spec, [ Bl.nor3 ], desc='1-bit full adder (nor3)')

    def test_identity(self):
        spec = Func('magic', And(Or(Bool('x'))))
        ops = [ Bl.nand2, Bl.nor2, Bl.and2, Bl.or2, Bl.xor2 ]
        return self.do_synth('identity', spec, ops)

    def test_true(self):
        x, y, z = Bools('x y z')
        spec = Func('magic', Or(Or(x, y, z), Not(x)))
        ops = [ Bl.nand2, Bl.nor2, Bl.and2, Bl.or2, Bl.xor2 ]
        return self.do_synth('true', spec, ops, desc='constant true')

    def test_false(self):
        x, y, z = Bools('x y z')
        spec = Spec('magic', z == Or([]), [z], [x])
        ops = [ Bl.nand2, Bl.nor2, Bl.and2, Bl.or2, Bl.xor2 ]
        return self.do_synth('false', spec, ops, desc='constant false')

    def test_multiple_types(self):
        x = Int('x')
        y = BitVec('y', 8)
        int2bv = Func('int2bv', Int2BV(x, 16))
        bv2int = Func('bv2int', BV2Int(y))
        div2   = Func('div2', x / 2)
        spec   = Func('shr2', LShR(ZeroExt(8, y), 1))
        ops    = [ int2bv, bv2int, div2 ]
        return self.do_synth('multiple_types', spec, ops)

    def test_precond(self):
        x = Int('x')
        b = BitVec('b', 8)
        int2bv = Func('int2bv', Int2BV(x, 8))
        bv2int = Func('bv2int', BV2Int(b))
        mul2   = Func('addadd', b + b)
        spec   = Func('mul2', x * 2, And([x >= 0, x < 128]))
        ops    = [ int2bv, bv2int, mul2 ]
        return self.do_synth('preconditions', spec, ops)

    def test_constant(self):
        x, y  = Ints('x y')
        mul   = Func('mul', x * y)
        spec  = Func('const', x + x)
        return self.do_synth('constant', spec, [ mul ])

    def test_abs(self):
        w = 32
        x, y = BitVecs('x y', w)
        ops = [
            Func('sub', x - y),
            Func('xor', x ^ y),
            Func('shr', x >> y, precond=And([y >= 0, y < w]))
        ]
        spec = Func('spec', If(x >= 0, x, -x))
        return self.do_synth('abs', spec, ops)

    def test_pow(self):
        x, y = Ints('x y')
        expr = x
        for _ in range(29):
            expr = expr * x
        spec = Func('pow', expr, x >= 0)
        ops  = [ Func('mul', x * y) ]
        return self.do_synth('pow', spec, ops, max_const=0)

    def test_poly(self):
        a, b, c, h = Ints('a b c h')
        spec = Func('poly', a * h * h + b * h + c)
        ops  = [ Func('mul', a * b), Func('add', a + b) ]
        return self.do_synth('poly', spec, ops, max_const=0)

    def test_array(self):
        def Arr(name):
            return Array(name, IntSort(), IntSort())

        def permutation(array, perm):
            res = array
            for fr, to in enumerate(perm):
                if fr != to:
                    res = Store(res, to, Select(array, fr))
            return res

        def swap(a, x, y):
            b = Store(a, x, Select(a, y))
            c = Store(b, y, Select(a, x))
            return c

        x = Array('x', IntSort(), IntSort())
        p = Int('p')
        op   = Func('swap', swap(x, p, p + 1))
        spec = Func('rev', permutation(x, [3, 2, 1, 0]))
        return self.do_synth('array', spec, [ op ])

def parse_standard_args():
    import argparse
    parser = argparse.ArgumentParser(prog="synth")
    parser.add_argument('-d', '--debug',  type=int, default=0)
    parser.add_argument('-m', '--maxlen', type=int, default=10)
    parser.add_argument('-s', '--stats',  default=False, action='store_true')
    parser.add_argument('-g', '--graph',  default=False, action='store_true')
    parser.add_argument('-w', '--write',  default=False, action='store_true')
    parser.add_argument('-t', '--tests',  default=None, type=str)
    return parser.parse_args()

# Enable Z3 parallel mode
set_param("parallel.enable", True)

if __name__ == "__main__":
    args = parse_standard_args()
    tests = Tests(**vars(args))
    tests.run()