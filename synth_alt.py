#! /usr/bin/env python3

import random
import itertools
import time

from itertools import combinations as comb
from itertools import permutations as perm

from z3 import *

class Op:
    def __init__(self, name: str, opnd_tys: list, res_ty, phi, \
                 precond=lambda x: True):
        self.name     = name
        self.phi      = phi
        self.precond  = precond
        self.opnd_tys = opnd_tys
        self.res_ty   = res_ty
        self.arity    = len(self.opnd_tys)
        self.comm     = False if self.arity < 2 or len(set(opnd_tys)) > 1 else None

    def __str__(self):
        return self.name

    def is_const(self):
        return False

    def is_commutative(self):
        if self.comm is None:
            ins = [ ty(f'{self.name}_in_comm_{i}') for i, ty in enumerate(self.opnd_tys) ]
            fs = [ Implies(And([self.precond(a), self.precond(b)]), self.phi(a) != self.phi(b)) for a, b in comb(perm(ins), 2) ]
            s = Solver()
            s.add(Or(fs))
            self.comm = s.check() == unsat
        return self.comm

class Const(Op):
    def __init__(self, res_ty):
        name = f'const_{res_ty.__name__}'
        self.var = res_ty(name)
        super().__init__(name, [], res_ty, lambda x: self.var, lambda x: True)

    def is_const(self):
        return True

class Prg:
    def __init__(self, input_names, insns, outputs):
        """Creates a program.

        Attributes:
        input_names: list of names of the inputs
        insns: List of instructions.
            This is a list of triples where each triple consists
            of an Op, an optional attribute, and a list of integers
            where each integer indicates the variable number of the operand.
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
        jv   = lambda args: ', '.join(map(lambda n: self.var_name(n), args))
        rhs  = lambda op, attr, args: f'{op.name}({jv(args)})' if not op.is_const() else str(attr)
        res = '\n'.join(f'x{i + n_inputs} = {rhs(op, attr, args)}' \
                        for i, (op, attr, args) in enumerate(self.insns))
        return res + f'\nreturn({jv(self.outputs)})'

class Synth:
    def __init__(self, n_insns, input_names, funcs: list[Op], ops: list[Op]):
        self.input_names = input_names
        self.n_inputs = len(input_names)
        self.n_insns = n_insns
        self.funcs = funcs
        self.ops = ops
        self.vars = {}

        # get types of input operands.
        # all functions need to agree on this.
        assert len(funcs) > 0
        self.in_tys = funcs[0].opnd_tys
        for s in funcs[1:]:
            assert self.in_tys == s.opnd_tys
        self.length = len(self.in_tys) + n_insns + 1

        # create map of types to their id
        self.n_types = 0
        self.types = {}
        for op in self.ops:
            for ty in op.opnd_tys + [ op.res_ty ]:
                if not ty in self.types:
                    self.types[ty] = self.n_types
                    self.n_types += 1

        max_arity = max(map(lambda op: op.arity, ops))
        self.arities = [ 0 ] * self.n_inputs + [ max_arity ] * n_insns + [ len(funcs) ]
        self.out_tys = [ op.res_ty for op in funcs ]

        # create the verification solver.
        # For now, it is just able to sample the specification
        self.verif = Solver()
        # all result variables of the inputs
        self.verif_inputs = [ self.var_input_res(i, 'eval') for i in range(self.n_inputs) ]
        # the operand value variables of the output instruction
        self.verif_outs = list(self.var_outs_val('eval'))        # constraints that say that the preconditions are satisfied
        for o, s in zip(self.verif_outs, self.funcs):
            self.verif.add(o == s.phi(self.verif_inputs))

    def eval_spec(self, input_vals):
        """Evaluates the specification on the given inputs.
           The list has to be of length n_inputs.
           If you want to not set an input, use None.
        """
        assert len(input_vals) == self.n_inputs
        self.verif.push()
        for i, v in enumerate(input_vals):
            if not v is None:
                self.verif.add(self.var_input_res(i, 'eval') == v)
        res = self.verif.check()
        assert res == sat, 'specification is unsatisfiable'
        m = self.verif.model()
        self.verif.pop()
        return [ m[v] for v in self.verif_inputs ], [ m[v] for v in self.verif_outs ]

    def get_var(self, ty, args):
        if args in self.vars:
            v = self.vars[args]
        elif ty:
            v = ty('_'.join(map(str, args)))
            self.vars[args] = v
        else:
            assert False
        return v

    def var_insn_op(self, insn):
        return self.get_var(Int, ('insn', insn, 'op'))

    def var_insn_opnds(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.get_var(Int, ('insn', insn, 'opnd', opnd))

    def var_insn_opnds_val(self, insn, tys, instance):
        for opnd, ty in enumerate(tys):
            yield self.get_var(ty, ('insn', insn, 'opnd', opnd, ty.__name__, instance))

    def var_outs_val(self, instance):
        for opnd in self.var_insn_opnds_val(self.out_insn(), self.out_tys, instance):
            yield opnd

    def var_insn_opnds_type(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.get_var(Int, ('insn', insn, 'opnd_type', opnd))

    def var_insn_res(self, insn, ty, instance):
        return self.get_var(ty, ('insn', insn, 'res', ty.__name__, instance))

    def var_insn_res_type(self, insn):
        return self.get_var(Int, ('insn', insn, 'res_type'))

    def var_input_res(self, insn, instance):
        return self.var_insn_res(insn, self.in_tys[insn], instance)

    def add_constr_wfp(self, solver: Solver):
        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for insn in range(self.length):
            for v in self.var_insn_opnds(insn):
                solver.add(0 <= v)
                solver.add(v < insn)

        # for all instructions that get an op
        # add constraints that set the type of an instruction's operands and result type
        for insn in range(self.n_inputs, self.length - 1):
            for op_id, op in enumerate(self.ops):
                # add constraints that set the result type of each instruction
                solver.add(Implies(self.var_insn_op(insn) == op_id, self.var_insn_res_type(insn) == self.types[op.res_ty]))
                # add constraints that set the type of each operand
                for op_ty, v in zip(op.opnd_tys, self.var_insn_opnds_type(insn)):
                    solver.add(Implies(self.var_insn_op(insn) == op_id, v == self.types[op_ty]))

            # constrain the op variable to the number of ops
            o = self.var_insn_op(insn)
            solver.add(0 <= o)
            solver.add(o < len(self.ops))
            # if operator is commutative, the operands can be linearly ordered
            # these constraints don't restrict the solution space but might
            # shrink the search space
            op_var = self.var_insn_op(insn)
            for op_id, op in enumerate(self.ops):
                if op.is_commutative():
                    opnds = list(self.var_insn_opnds(insn))
                    c = [ l < u for l, u in zip(opnds[:op.arity - 1], opnds[1:]) ]
                    solver.add(Implies(op_var == op_id, And(c)))

        # define types of inputs
        for inp, ty in enumerate(self.in_tys):
            solver.add(self.var_insn_res_type(inp) == self.types[ty])

        # define types of outputs
        for v, ty in zip(self.var_insn_opnds_type(self.out_insn()), self.out_tys):
            solver.add(v == self.types[ty])

        # constrain types of outputs
        for insn in range(self.n_inputs, self.length):
            for other in range(0, insn):
                for opnd, ty in zip(self.var_insn_opnds(insn), \
                                    self.var_insn_opnds_type(insn)):
                    solver.add(Implies(opnd == other, ty == self.var_insn_res_type(other)))

        # add constraints that says that each produced value is used
        # this is an optimization that might shrink the search space
        for prod in range(self.n_inputs, self.length):
            opnds = [ prod == v for cons in range(prod + 1, self.length) for v in self.var_insn_opnds(cons) ]
            if len(opnds) > 0:
                solver.add(Or(opnds))

    def out_insn(self):
        return self.length - 1

    def is_op_insn(self, insn):
        return insn >= self.n_inputs and insn < self.length - 1

    def add_constr_conn(self, solver, insn, tys, instance):
        for ty, l, v in zip(tys, self.var_insn_opnds(insn), \
                            self.var_insn_opnds_val(insn, tys, instance)):
            # for other each instruction preceding it
            for other in range(insn):
                r = self.var_insn_res(other, ty, instance)
                solver.add(Implies(l == other, v == r))

    def add_constr_instance(self, solver, instance):
        # for all instructions that get an op
        for insn in range(self.n_inputs, self.length - 1):
            # add constraints to select the proper operation
            op_var = self.var_insn_op(insn)
            for op_id, op in enumerate(self.ops):
                res = self.var_insn_res(insn, op.res_ty, instance)
                opnds = list(self.var_insn_opnds_val(insn, op.opnd_tys, instance))
                spec = Implies(op.precond(opnds), res == op.phi(opnds))
                solver.add(Implies(op_var == op_id, spec))
            # connect values of operands to values of corresponding results
            for op in self.ops:
                self.add_constr_conn(solver, insn, op.opnd_tys, instance)
        # add connection constraints for output instruction
        self.add_constr_conn(solver, self.out_insn(), self.out_tys, instance)

    def add_constr_io_sample(self, solver, instance, io_sample):
        # add input value constraints
        in_vals, out_vals = io_sample
        assert len(in_vals) == self.n_inputs and len(out_vals) == len(self.funcs)
        for inp, val in enumerate(in_vals):
            if not val is None:
                res = self.var_input_res(inp, instance)
                solver.add(res == val)
        for out, val in zip(self.var_outs_val(instance), out_vals):
            if not val is None:
                solver.add(out == val)

    def add_constr_sol_for_verif(self, model):
        solver = self.verif
        for insn in range(self.length):
            if self.is_op_insn(insn):
                v = self.var_insn_op(insn)
                solver.add(model[v] == v)
            for opnd in self.var_insn_opnds(insn):
                solver.add(model[opnd] == opnd)
        # set the values of the constants that have been synthesized
        for op in self.ops:
            if op.is_const() and not model[op.var] is None:
                solver.add(op.var == model[op.var])

    def add_constr_spec_verif(self):
        verif_ins = [ self.var_input_res(i, 'verif') for i in range(self.n_inputs) ]
        for inp in range(self.n_inputs):
            self.verif.add(self.var_input_res(inp, 'verif') == \
                           self.var_input_res(inp, 'eval'))
        for f in self.funcs:
            self.verif.add(f.precond(verif_ins))

        self.verif.add(Or([v != e for v, e in zip(self.var_outs_val('verif'), \
                                                  self.var_outs_val('eval'))]))

    def __call__(self, debug=0):
        def d(*args):
            nonlocal debug
            if debug > 0:
                print(*args)

        def dd(*args):
            nonlocal debug
            if debug > 1:
                print(*args)

        def ddd(*args):
            nonlocal debug
            if debug > 2:
                print(*args)

        d('size', self.n_insns)

        # setup the synthesis constraint
        synth = Solver()
        self.add_constr_wfp(synth)

        stats = []
        # sample the specification once for an initial set of input samples
        sample = self.eval_spec([None] * self.n_inputs)
        i = 0
        while True:
            stat = {}
            stats += [ stat ]

            d('sample', i, sample)
            self.add_constr_instance(synth, i)
            self.add_constr_io_sample(synth, i, sample)

            ddd('synth', i, synth)
            start = time.perf_counter_ns()
            res = synth.check()
            stat['synth'] = time.perf_counter_ns() - start

            if res == sat:
                # if sat, we found location variables
                m = synth.model()
                dd('model: ', m)
                # push a new verification solver state
                self.verif.push()
                # Add constraints that represent the instructions of
                # the synthesized program
                self.add_constr_instance(self.verif, 'verif')
                # Add constraints that relate the specification to
                # the inputs and outputs of the synthesized program
                self.add_constr_spec_verif()
                # add constraints that set the location variables
                # in the verification constraint
                self.add_constr_sol_for_verif(m)
                ddd('verif', i, self.verif)

                start = time.perf_counter_ns()
                res = self.verif.check()
                stat['verif'] = time.perf_counter_ns() - start

                if res == sat:
                    # there is a counterexample, reiterate
                    m = self.verif.model()
                    self.verif.pop()
                    var = lambda inp : m[self.var_input_res(inp, 'verif')]
                    in_vals = [ var(inp) for inp in range(self.n_inputs) ]
                    ddd(in_vals)
                    sample = self.eval_spec(in_vals)
                    i += 1
                else:
                    # clean up the verification solver state
                    self.verif.pop()
                    # we found no counterexample, the program is therefore correct
                    d('no counter example found')
                    insns = []
                    for insn in range(self.n_inputs, self.length - 1):
                        op     = self.ops[m[self.var_insn_op(insn)].as_long()]
                        attr   = m[op.var] if op.is_const() else None
                        opnds  = [ m[v].as_long() for v in self.var_insn_opnds(insn) ][:op.arity]
                        insns += [ (op, attr, opnds) ]
                    out_idx = self.length - 1
                    outputs = [ m[res].as_long() for res in self.var_insn_opnds(out_idx) ]
                    stat['n_counter_examples'] = i
                    prg = Prg(self.input_names, insns, outputs)
                    return prg, stats
            else:
                d('synthesis failed')
                return None, stats

def synth(length, input_names, specs, ops, debug=False):
    """Synthesize a program that implements a given specification.

    Args:
        length: Length of the program.
        input_names (list(str)): A list of names of the input variables
        specs (list(Op)): List of specifications of functions to synthesize
        ops (list(Op)): List of available operators that can be used for instructions.

    Returns:
        A pair (prg, stats) where prg is a program that implements the given
        specification and stats is a list of dictionaries that contain
        statistics about the synthesis process.
    """
    return Synth(length, input_names, specs, ops)(debug)

def synth_smallest(max_length, input_names, specs, ops, debug=False):
    """Synthesize the smallest program that implements a given specification.

    Use like synth except for max_length which gives an upper bound on
    the program length. Internally, this function calls synth for lengths
    from 1 to max_length + 1 and returns the first (smallest) program found.
    """
    for sz in range(0, max_length + 1):
        prg, stats = synth(sz, input_names, specs, ops, debug)
        if prg:
            return prg
    return None

Bool1 = [ Bool ]
Bool2 = [ Bool ] * 2
Bool3 = [ Bool ] * 3
Bool4 = [ Bool ] * 4

true0  = Op('true',   []   , Bool, lambda ins: True)
false0 = Op('false',  []   , Bool, lambda ins: False)
id1    = Op('id',     Bool1, Bool, lambda ins: ins[0])

not1  = Op('not',     Bool2, Bool, lambda ins: Not(ins[0]))         #7404
nand2 = Op('nand2',   Bool2, Bool, lambda ins: Not(And(ins)))       #7400
nor2  = Op('nor2',    Bool2, Bool, lambda ins: Not(Or(ins)))        #7402
and2  = Op('and2',    Bool2, Bool, And)                             #7408
or2   = Op('or2',     Bool2, Bool, Or)                              #7432
xor2  = Op('xor2',    Bool2, Bool, lambda ins: Xor(ins[0], ins[1])) #7486

nand3 = Op('nand3',   Bool3, Bool, lambda ins: Not(And(ins)))       #7410
nor3  = Op('nor3',    Bool3, Bool, lambda ins: Not(Or(ins)))        #7427
and3  = Op('and3',    Bool3, Bool, And)                             #7411

nand4 = Op('nand4',   Bool4, Bool, lambda ins: Not(And(ins)))       #7420
and4  = Op('and4',    Bool4, Bool, And)                             #7421
nor4  = Op('nor4',    Bool4, Bool, lambda ins: Not(Or(ins)))        #7429

mux2  = Op('mux2',    Bool2, Bool, lambda i: Or(And(i[0], i[1]), And(Not(i[0]), i[2])))
eq2   = Op('eq2',     Bool2, Bool, lambda i: i[0] == i[1])

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

def create_random_dnf(inputs, seed=0x5aab199e):
    # sample function results
    random.seed(a=seed, version=2)
    clauses = []
    for vals in itertools.product(*[range(2)] * len(inputs)):
        if random.choice(range(2)):
            clauses += [ And([ inp if pos else Not(inp) for inp, pos in zip(inputs, vals) ]) ]
    return Or(clauses)

def random_test(n_vars, size, create_formula, debug=0):
    ops  = [ and2, or2, xor2, not1 ]
    spec = Op('rand', [ Bool ] * n_vars, Bool, create_formula)
    prg  = synth_smallest(size, [ f'v{i}' for i in range(n_vars)], [spec], ops, debug)
    print(prg)

def test_rand(size=40, n_vars=10, debug=0):
    rops = [ (And, 2), (Or, 2), (Xor, 2), (Not, 1) ]
    f    = lambda x: create_random_formula(x, size, rops)
    random_test(n_vars, size, f, debug)

def test_rand_dnf(size=40, n_vars=10, debug=0):
    f = lambda x: create_random_dnf(x)
    random_test(n_vars, size, f, debug)

def test_and(debug=0):
    spec = Op('and', Bool2, Bool, And)
    print('and:')
    prg = synth_smallest(1, [ 'a', 'b'], [spec], [spec], debug)
    print(prg)

def test_xor(debug=0):
    spec = Op('xor2', Bool2, Bool, lambda i: Xor(i[0], i[1]))
    ops  = [ and2, nand2, or2, nor2 ]
    print('xor:')
    prg = synth_smallest(10, [ 'x', 'y' ], [ spec ], ops, debug)
    print(prg)

def test_mux(debug=0):
    spec = Op('mux2', Bool3, Bool, lambda i: Or(And(i[0], i[1]), And(Not(i[0]), i[2])))
    ops  = [ and2, xor2 ]
    print('mux:')
    prg = synth_smallest(3, [ 's', 'x', 'y' ], [ spec ], ops, debug)
    print(prg)

def test_zero(debug=0):
    spec = Op('zero', [ Bool ] * 8, Bool, lambda i: Not(Or(i)))
    ops  = [ and2, nand2, or2, nor2, nand3, nor3, nand4, nor4 ]
    print('one byte all zero test:')
    prg = synth_smallest(10, [ f'x{i}' for i in range(8) ], [ spec ], ops, debug)
    print(prg)

def test_add(debug=0):
    cy  = Op('cy',  Bool3, Bool, lambda i: Or(And(i[0], i[1]), And(i[1], i[2]), And(i[0], i[2])))
    add = Op('add', Bool3, Bool, lambda i: Xor(i[0], Xor(i[1], i[2])))
    ops = [ nand2, nor2, and2, or2, xor2 ]
    print('1-bit full adder:')
    prg = synth_smallest(10, [ 'x', 'y', 'c' ], [ add, cy ], ops, debug)
    print(prg)

def test_identity(debug=0):
    spec = Op('magic', Bool1, Bool, lambda ins: And(Or(ins[0])))
    ops = [ nand2, nor2, and2, or2, xor2, id1]
    print('identity: ')
    prg = synth_smallest(10, [ 'x' ], [ spec ], ops, debug)
    print(prg)

def test_true(debug=0):
    spec = Op('magic', Bool3, Bool, lambda ins: Or(Or(ins[0], ins[1], ins[2]), Not(ins[0])))
    ops = [ true0, false0, nand2, nor2, and2, or2, xor2, id1]
    print('constant True: ')
    prg = synth_smallest(10, [ 'x', 'y', 'z' ], [ spec ], ops, debug)
    print(prg)

def test_multiple_types(debug=0):
    def Bv(v):
        return BitVec(v, 8)
    def BvLong(v):
        return BitVec(v, 16)
    int2bv = Op('int2bv', [ Int ], BvLong, lambda x: Int2BV(x[0], 16))
    bv2int = Op('bv2int', [ Bv ], Int, lambda x: BV2Int(x[0]))
    div2   = Op('div2', [ Int ], Int, lambda x: x[0] / 2)
    spec   = Op('shr2', [ Bv ], BvLong, lambda x: LShR(ZeroExt(8, x[0]), 1))
    ops    = [ int2bv, bv2int, div2 ]
    print('multiple types:')
    prg    = synth_smallest(10, [ 'x' ], [ spec ], ops, debug)
    print(prg)

def test_precond(debug=0):
    def Bv(v):
        return BitVec(v, 8)
    int2bv = Op('int2bv', [ Int ], Bv, lambda x: Int2BV(x[0], 8))
    bv2int = Op('bv2int', [ Bv ], Int, lambda x: BV2Int(x[0]))
    mul2   = Op('addadd', [ Bv ], Bv, lambda x: x[0] + x[0])
    spec   = Op('mul2', [ Int ], Int, lambda x: x[0] * 2, \
                 precond=lambda x: And([x[0] >= 0, x[0] < 128]))
    ops    = [ int2bv, bv2int, mul2 ]
    print('preconditions:')
    prg    = synth_smallest(10, [ 'x' ], [ spec ], ops, debug)
    print(prg)

def test_constant(debug=0):
    mul    = Op('mul', [ Int, Int ], Int, lambda x: x[0] * x[1])
    spec   = Op('const', [ Int ], Int, lambda x: x[0] + x[0])
    const  = Const(Int)
    ops    = [ mul, const ]
    print('constant:')
    prg    = synth_smallest(10, [ 'x' ], [ spec ], ops, debug)
    print(prg)

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(prog="synth")
    parser.add_argument('-d', '--debug', type=int, default=0)
    args = parser.parse_args()

    test_identity(args.debug)
    test_true(args.debug)
    test_constant(args.debug)
    test_and(args.debug)
    test_mux(args.debug)
    test_xor(args.debug)
    test_zero(args.debug)
    test_add(args.debug)
    test_multiple_types(args.debug)
    test_precond(args.debug)
    test_rand_dnf(40, 4, args.debug)
    test_rand(50, 4, args.debug)
