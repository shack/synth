#! /usr/bin/env python3

import importlib
import random
import itertools
import functools
import json
import re

from enum import Enum

from cegis import Func, Spec, OpFreq
from oplib import Bl, Bv
from util import bv_sort

from z3 import *

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

    This function iterates over *all* clauses, and picks based on the
    clause_probability if a clause is added to the formula.
    Therefore, the function's running time is exponential in the number of variables.
    """
    # sample function results
    random.seed(a=seed, version=2)
    clauses = []
    for vals in itertools.product(*[range(2)] * len(inputs)):
        if random.choice(range(100)) < clause_probability:
            clauses += [ And([ inp if pos else Not(inp) for inp, pos in zip(inputs, vals) ]) ]
    return Or(clauses)

def create_bool_func(func):
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

class ConstMode(Enum):
    NONE = 0        # like free, but take the hint if consts are disabled
    FREE = 1        # no constraint on constants
    COUNT = 2       # give an upper bound on how many constants can be used
    SET = 3         # give the set of constants
    SET_COUNT = 4   # give the set of constants and an upper bound on how many can be used

    def __str__(self):
        return self.name

    @staticmethod
    def from_string(s):
        try:
            return ConstMode[s]
        except KeyError:
            raise ValueError()

class TestBase:
    def __init__(self, list_tests=False, minlen=0, maxlen=10, debug=0, stats=False, graph=False, \
                tests=None, write=None, timeout=None, difficulty=0, exact=False,
                const_mode=ConstMode.FREE, synth='synth_n', check=0):
        def d(level, *args):
            if debug >= level:
                print(*args)

        # Z3 settings
        set_option("sat.random_seed", 0);
        set_option("smt.random_seed", 0);
        set_option("parallel.enable", True);
        set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

        self.debug = d
        self.list_tests = list_tests
        self.min_length = minlen
        self.max_length = maxlen
        self.write_stats = stats
        self.write_graph = graph
        self.tests = tests
        self.write = write
        self.check = check
        self.timeout = timeout
        self.exact = exact
        self.difficulty = difficulty
        self.const_mode = const_mode
        m = importlib.import_module(synth)
        self.synth_func = getattr(m, 'synth')

    def do_synth(self, name, spec, ops, all_ops=None, consts=None, desc='', **args):
        desc = f' ({desc})' if len(desc) > 0 else ''
        print(f'{name}{desc}: ', end='', flush=True)
        output_prefix = name if self.write else None
        if self.exact:
            self.min_length = self.max_length = sum(f for f in ops.values())
        ran = range(self.min_length, self.max_length + 1)

        # if entire library is not specified, use the given operator library
        if all_ops is None:
            all_ops = ops
        # if operator library does not specifcy counts, set all to maximum
        # or if exact operator count is not enabled, set operator count to maximum
        if type(ops) == list or type(ops) == set or not self.exact:
            ops = { op: OpFreq.MAX for op in ops }
        else:
            ops = dict(ops)
        # figure out operator library based on difficulty
        rest_ops = [ op for op in all_ops if op not in ops ]
        for o in rest_ops[:self.difficulty]:
            ops[o] = OpFreq.MAX

        m = lambda: sum(f for f in consts.values())
        s = lambda: { c for c in consts }
        match self.const_mode:
            case ConstMode.NONE:
                max_const = 0 if not consts is None and len(consts) == 0 else None
                const_set = None
            case ConstMode.FREE:
                max_const = None
                const_set = None
            case ConstMode.COUNT:
                max_const = m()
                const_set = None
            case ConstMode.SET:
                max_const = None
                const_set = s()
            case ConstMode.SET_COUNT:
                max_const = m()
                const_set = s()

        prg, stats = self.synth_func(spec, ops, ran, \
                                     debug=self.debug, \
                                     output_prefix=output_prefix, \
                                     timeout=self.timeout, \
                                     max_const=max_const, \
                                     const_set=const_set, \
                                     **args)
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
        if self.list_tests:
            # output all the test names separated by commas
            print(','.join([ name[5:] for name in dir(self) if name.startswith('test_') ]))
            return

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
        return self.do_synth(name, spec, ops, consts={}, theory='QF_BV')

    def test_rand(self, size=40, n_vars=4):
        ops = [ (And, 2), (Or, 2), (Xor, 2), (Not, 1) ]
        f   = lambda x: create_random_formula(x, size, ops)
        return self.random_test('rand_formula', n_vars, f)

    def test_rand_dnf(self, n_vars=4):
        f = lambda x: create_random_dnf(x)
        return self.random_test('rand_dnf', n_vars, f)

    def test_npn4_1789(self):
        ops  = { Bl.xor2: 3, Bl.and2: 2, Bl.or2: 1 }
        name = '1789'
        spec = create_bool_func(name)
        return self.do_synth(f'npn4_{name}', spec, ops, all_ops=Bl.ops,
                             consts={}, n_samples=16, \
                             theory='QF_BV')

    def test_and(self):
        ops = { Bl.nand2: 2 }
        return self.do_synth('and', Bl.and2, ops, Bl.ops)

    def test_xor(self):
        ops = { Bl.nand2: 4 }
        return self.do_synth('xor', Bl.xor2, ops, Bl.ops)

    def test_mux(self):
        ops = { Bl.and2: 1, Bl.xor2: 2 }
        return self.do_synth('mux', Bl.mux2, ops, Bl.ops)

    def test_zero(self):
        spec = Func('zero', Not(Or([ Bool(f'x{i}') for i in range(8) ])))
        ops  = { Bl.and2: 1, Bl.nor4: 2 }
        return self.do_synth('zero', spec, ops, Bl.ops, theory='QF_BV')

    def test_add(self):
        x, y, ci, s, co = Bools('x y ci s co')
        add = And([co == AtLeast(x, y, ci, 2), s == Xor(x, Xor(y, ci))])
        spec = Spec('adder', add, [s, co], [x, y, ci])
        ops  = { Bl.xor2: 2, Bl.and2: 2, Bl.or2: 1 }
        return self.do_synth('add', spec, ops, Bl.ops,
                             desc='1-bit full adder', theory='QF_BV')

    def test_add_apollo(self):
        x, y, ci, s, co = Bools('x y ci s co')
        add = And([co == AtLeast(x, y, ci, 2), s == Xor(x, Xor(y, ci))])
        spec = Spec('adder', add, [s, co], [x, y, ci])
        return self.do_synth('add_nor3', spec, { Bl.nor3: 8 }, Bl.ops, \
                             desc='1-bit full adder (nor3)', theory='QF_BV')

    def test_identity(self):
        spec = Func('magic', And(Or(Bool('x'))))
        return self.do_synth('identity', spec, { }, Bl.ops)

    def test_true(self):
        x, y, z = Bools('x y z')
        spec = Func('magic', Or(Or(x, y, z), Not(x)))
        return self.do_synth('true', spec, { }, Bl.ops, desc='constant true')

    def test_false(self):
        x, y, z = Bools('x y z')
        spec = Spec('magic', z == Or([]), [z], [x])
        return self.do_synth('false', spec, { }, Bl.ops, desc='constant false')

    def test_multiple_types(self):
        x = Int('x')
        y = BitVec('y', 8)
        int2bv = Func('int2bv', Int2BV(x, 16))
        bv2int = Func('bv2int', BV2Int(y, is_signed=False))
        div2   = Func('div2', x / 2)
        spec   = Func('shr2', LShR(ZeroExt(8, y), 1))
        ops    = { int2bv: 1, bv2int: 1, div2: 1 }
        return self.do_synth('multiple_types', spec, ops)

    def test_precond(self):
        x = Int('x')
        b = BitVec('b', 8)
        int2bv = Func('int2bv', Int2BV(x, 8))
        bv2int = Func('bv2int', BV2Int(b))
        mul2   = Func('addadd', b + b)
        spec   = Func('mul2', x * 2, And([x >= 0, x < 128]))
        ops    = { int2bv: 1, bv2int: 1, mul2: 1 }
        return self.do_synth('preconditions', spec, ops)

    def test_constant(self):
        x, y  = Ints('x y')
        mul   = Func('mul', x * y)
        spec  = Func('const', x + x)
        ops   = { mul: 1 }
        return self.do_synth('constant', spec, ops)

    def test_abs(self):
        w = 32
        bv = Bv(w)
        x, y = BitVecs('x y', w)
        ops = { bv.sub_: 1, bv.xor_: 1, bv.ashr_: 1 }
        spec = Func('spec', If(x >= 0, x, -x))
        return self.do_synth('abs', spec, ops, bv.ops, theory='QF_BV')

    def test_pow(self):
        x, y = Ints('x y')
        one  = IntVal(1)
        n = 30
        expr = functools.reduce(lambda a, _: x * a, range(n), one)
        spec = Func('pow', expr)
        ops  = { Func('mul', x * y): 5 }
        return self.do_synth('pow', spec, ops, consts={})

    def test_poly(self):
        a, b, c, h = Ints('a b c h')
        spec = Func('poly', a * h * h + b * h + c)
        ops  = { Func('mul', a * b): 2, Func('add', a + b): 2 }
        return self.do_synth('poly', spec, ops, consts={})

    def test_sort(self):
        n = 3
        s = bv_sort(n)
        x, y = Consts('x y', s)
        p = Bool('p')
        min  = Func('min', If(ULE(x, y), x, y))
        max  = Func('max', If(UGT(x, y), x, y))
        ins  = [ Const(f'i{i}', s) for i in range(n) ]
        outs = [ Const(f'o{i}', s) for i in range(n) ]
        pre  = [ Distinct(*ins) ] \
             + [ ULE(0, i) for i in ins ] \
             + [ ULT(i, n) for i in ins ]
        pre  = And(pre)
        phi  = And([ o == i for i, o in enumerate(outs) ])
        spec = Spec('sort', phi, outs, ins, pre)
        return self.do_synth('sort', spec, [min, max], consts={})

    def test_array(self):
        def permutation(array, perm):
            res = array
            for fr, to in enumerate(perm):
                if fr != to:
                    res = Store(res, to, array[fr])
            return res

        def swap(a, x, y):
            b = Store(a, x, a[y])
            c = Store(b, y, a[x])
            return c

        x = Array('x', IntSort(), IntSort())
        p = Int('p')
        op   = Func('swap', swap(x, p, p + 1))
        spec = Func('rev', permutation(x, [3, 2, 1, 0]))
        return self.do_synth('array', spec, { op: 6 })

def parse_standard_args():
    import argparse
    parser = argparse.ArgumentParser(prog="synth")
    parser.add_argument('-d', '--debug',      type=int, default=0)
    parser.add_argument('-l', '--minlen',     type=int, default=0)
    parser.add_argument('-L', '--maxlen',     type=int, default=10)
    parser.add_argument('-a', '--stats',      default=False, action='store_true')
    parser.add_argument('-g', '--graph',      default=False, action='store_true')
    parser.add_argument('-w', '--write',      default=False, action='store_true')
    parser.add_argument('-t', '--tests',      default=None, type=str)
    parser.add_argument('-s', '--synth',      type=str, default='synth_n')
    parser.add_argument('-m', '--timeout',    help='timeout in ms', type=int, default=None)
    parser.add_argument('-y', '--difficulty', help='difficulty (# of additional operators)', \
                        type=int, default=0)
    parser.add_argument('-x', '--exact',      default=False, action='store_true', \
                        help='respect exact operator count')
    parser.add_argument('-c', '--const_mode', type=ConstMode.from_string, choices=list(ConstMode), default=ConstMode.NONE, \
                        help='(constant mode: NONE = no constraints, but if none specified, use that information, ' \
                                + 'FREE = no constraints, COUNT = bound number of constants, ' \
                                + 'SET = give set of constants, SET_COUNT = bound number and give set)')
    parser.add_argument('-T', '--list_tests', default=False, action='store_true', help='just list all test names comma separated, do not run')

    return parser.parse_known_args()

if __name__ == "__main__":

    args, _ = parse_standard_args()
    tests = Tests(**vars(args))
    tests.run()
