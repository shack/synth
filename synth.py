#! /usr/bin/env python3

import random
import itertools
import time
import json

from itertools import combinations as comb
from itertools import permutations as perm
from functools import cached_property

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

    def out_types(self):
        return [ v.sort() for v in self.outputs ]

    def in_types(self):
        return [ v.sort() for v in self.inputs ]

    def instantiate(self, outs, ins):
        assert len(outs) == len(self.outputs)
        assert len(ins) == len(self.inputs)
        return substitute(self.phi, list(zip(self.outputs + self.inputs, outs + ins)))


class Func(Spec):
    def __init__(self, name, phi, precond=BoolVal(True), inputs=[]):
        """Creates an Op from a Z3 expression.

        Attributes:
        name: Name of the operator.
        phi: Z3 expression that represents the semantics of the operator.
        precond: Z3 expression that represents the precondition of the operator.

        The order of the parameters of the operator is the alphabetical order
        of the names of the variables that appear in expression phi.
        Other than that, the names of the variables don't matter because when
        used in the synthesis process their names are substituted by internal names.
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
        subst = lambda f, i: substitute(f, list(zip(self.inputs, i)))
        ins = [ Const(f'{self.name}_in_comm_{i}', ty) \
                for i, ty in enumerate(self.in_types()) ]
        fs = [ And([ subst(self.precond, a), subst(self.precond, b), \
                     subst(self.func, a) != subst(self.func, b) ]) \
                for a, b in comb(perm(ins), 2) ]
        s = Solver()
        s.add(Or(fs))
        return s.check() == unsat

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

def take_time(func, *args):
    start = time.perf_counter_ns()
    res = func(*args)
    return res, time.perf_counter_ns() - start

def synth(spec: Spec, ops: list[Func], to_len, from_len=0, debug=0, max_const=None, output_prefix=None):
    """Synthesize a program that computes the given functions.

    Attributes:
    funcs: List of functions that the program has to compute.
        All functions have to have the same number of operands and
        have to agree on their operand types.
    ops: List of operations that can be used in the program.
    to_len: Maximum length of the program.
    from_len: Minimum length of the program.
    debug: Debug level. 0: no debug output, >0 more debug output.

    Returns:
    A tuple (prg, stats) where prg is the synthesized program and stats
    is a list of statistics for each iteration of the synthesis loop.
    """
    vars = {}
    # get types of input operands.
    # all functions need to agree on this.
    in_tys = spec.in_types()
    out_tys = spec.out_types()
    n_inputs = len(in_tys)
    n_outputs = len(out_tys)

    input_names = [ str(v) for v in spec.inputs ]
    assert len(input_names) == n_inputs

    # create map of types to their id
    n_types = 0
    types = {}
    for op in ops:
        for ty in op.out_types() + op.in_types():
            if not ty in types:
                types[ty] = n_types
                n_types += 1

    max_arity = max(op.arity for op in ops)
    out_insn = 0
    length = 0
    arities = []

    bv_sort = lambda n: BitVecSort(len(bin(n)) - 2)
    ty_sort = bv_sort(n_types)
    op_sort = bv_sort(len(ops))
    ln_sort = bv_sort(1 + n_inputs + to_len)

    def d(*args):
        if debug > 0:
            print(*args)

    def dd(*args):
        if debug > 1:
            print(*args)

    def ddd(*args):
        if debug > 2:
            print(*args)

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

    def get_var(ty, name):
        if name in vars:
            v = vars[name]
        else:
            v = Const(name, ty)
            vars[name] = v
        return v

    def ty_name(ty):
        return str(ty).replace(' ', '_') \
                      .replace(',', '_') \
                      .replace('(', '_') \
                      .replace(')', '_')

    def var_insn_op(insn):
        # return get_var(IntSort(), f'insn_{insn}_op')
        return get_var(op_sort, f'insn_{insn}_op')

    def var_insn_opnds_is_const(insn):
        for opnd in range(arities[insn]):
            yield get_var(BoolSort(), f'insn_{insn}_opnd_{opnd}_is_const')

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
                solver.add(ULE(v, insn - 1))

        # for all instructions that get an op
        # add constraints that set the type of an instruction's operands and result type
        for insn in range(n_inputs, length - 1):
            for op_id, op in enumerate(ops):
                # add constraints that set the result type of each instruction
                solver.add(Implies(var_insn_op(insn) == op_id, \
                                   var_insn_res_type(insn) == types[op.res_ty]))
                # add constraints that set the type of each operand
                for op_ty, v in zip(op.in_types(), var_insn_opnds_type(insn)):
                    solver.add(Implies(var_insn_op(insn) == op_id, v == types[op_ty]))

            # constrain the op variable to the number of ops
            o = var_insn_op(insn)
            solver.add(ULE(o, len(ops) - 1))

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

        if not max_const is None:
            solver.add(AtMost(*[ v == True for insn in range(n_inputs, length) \
                               for v in var_insn_opnds_is_const(insn)], max_const))

    def add_constr_opt(solver: Solver):
        for insn in range(n_inputs, out_insn):
            op_var = var_insn_op(insn)
            for op_id, op in enumerate(ops):
                # if operator is commutative, force the operands to be in ascending order
                if op.is_commutative:
                    opnds = list(var_insn_opnds(insn))
                    c = [ ULE(l, u) for l, u in zip(opnds[:op.arity - 1], opnds[1:]) ]
                    solver.add(Implies(op_var == op_id, And(c)))
                # force that at least one operand is not-constant
                # otherwise, the operation is not needed because it would be fully constant
                vars = [ Not(v) for v in var_insn_opnds_is_const(insn) ][:op.arity]
                assert len(vars) > 0
                solver.add(Implies(op_var == op_id, Or(vars)))

            # Computations must not be replicated: If an operation appears again
            # in the program, at least one of the operands must be different from
            # a previous occurrence of the same operation.
            for other in range(n_inputs, insn):
                un_eq = [ p != q for p, q in zip(var_insn_opnds(insn), var_insn_opnds(other)) ]
                assert len(un_eq) > 0
                solver.add(Implies(var_insn_op(insn) == var_insn_op(other), Or(un_eq)))

        # add constraints that says that each produced value is used
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
            for op_id, op in enumerate(ops):
                res = var_insn_res(insn, op.res_ty, instance)
                opnds = list(var_insn_opnds_val(insn, op.in_types(), instance))
                solver.add(Implies(op_var == op_id, op.instantiate([ res ], opnds)))
            # connect values of operands to values of corresponding results
            for op in ops:
                add_constr_conn(solver, insn, op.in_types(), instance)
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
                verif.add(model[v] == v)
                op = model[v].as_long()
                tys = ops[op].in_types()
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
            op     = ops[model[var_insn_op(insn)].as_long()]
            opnds  = [ v for v in prep_opnds(insn, op.in_types()) ]#[:op.arity]
            insns += [ (op, opnds) ]
        outputs = [ v for v in prep_opnds(out_insn, out_tys) ]
        return Prg(input_names, insns, outputs)

    def write_sexpr(solver, *args):
        if not output_prefix is None:
            filename = f'{output_prefix}_{"_".join(str(a) for a in args)}.smt2'
            with open(filename, 'w') as f:
                f.write(solver.sexpr())

    set_param('parallel.enable', True)

    # create the verification solver.
    # For now, it is just able to sample the specification
    verif = Solver()
    # all result variables of the inputs
    eval_ins = [ get_var(ty, f'eval_in_{i}') for i, ty in enumerate(in_tys) ]
    # the operand value variables of the output instruction
    eval_outs = [ get_var(ty, f'eval_out_{i}') for i, ty in enumerate(out_tys) ]
    verif.add(spec.instantiate(eval_outs, eval_ins))

    def synth_len(n_insns):
        nonlocal out_insn, length, arities
        out_insn = len(in_tys) + n_insns
        length   = out_insn + 1
        arities  = [ 0 ] * n_inputs + [ max_arity ] * n_insns + [ len(out_tys) ]

        d('size', n_insns)

        # get the synthesis solver
        synth = Solver()

        # setup the synthesis constraint
        add_constr_wfp(synth)
        add_constr_opt(synth)

        stats = []
        # sample the specification once for an initial set of input samples
        sample = eval_spec([None] * n_inputs)
        i = 0
        while True:
            stat = {}
            stats += [ stat ]

            d('sample', i, sample)
            add_constr_instance(synth, i)
            add_constr_io_sample(synth, i, sample)

            ddd('synth', i, synth)
            write_sexpr(synth, 'synth', n_insns, i)
            res, synth_time = take_time(synth.check)
            dd(f'synth time: {synth_time / 1e9:.3f}')
            stat['synth'] = synth_time

            if res == sat:
                # if sat, we found location variables
                m = synth.model()
                prg = create_prg(m)
                stat['prg'] = str(prg).replace('\n', '; ')

                dd('model: ', m)
                dd('program: ', prg)

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

                ddd('verif', i, verif)
                write_sexpr(verif, 'verif', n_insns, i)
                res, verif_time = take_time(verif.check)
                stat['verif'] = verif_time
                dd(f'verif time {verif_time / 1e9:.3f}')

                if res == sat:
                    # there is a counterexample, reiterate
                    m = verif.model()
                    ddd('verification model', m)
                    verif.pop()
                    sample = eval_spec([ m[e] for e in eval_ins ])
                    i += 1
                else:
                    # clean up the verification solver state
                    verif.pop()
                    # we found no counterexample, the program is therefore correct
                    d('no counter example found')
                    return prg, stats
            else:
                assert res == unsat
                d(f'synthesis failed for size {n_insns}')
                return None, stats

    all_stats = []
    for n_insns in range(from_len, to_len + 1):
        (prg, stats), t = take_time(synth_len, n_insns)
        all_stats += [ { 'time': t, 'iterations': stats } ]
        if not prg is None:
            return prg, all_stats
    return None, all_stats

class Bl:
    w, x, y, z = Bools('w x y z')
    i2 = [x, y]
    i3 = [x, y, z]
    i4 = [w, x, y, z]
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
        prg, stats = synth(spec, ops, self.max_length, \
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
        ops  = [ Bl.and2, Bl.nand2, Bl.or2, Bl.nor2 ]
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

if __name__ == "__main__":
    args = parse_standard_args()
    tests = Tests(**vars(args))
    tests.run()