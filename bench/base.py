#! /usr/bin/env python3

import functools

from dataclasses import dataclass
from z3 import *

from synth.spec import Func, Spec, create_bool_func
from synth.oplib import Bl, Bv
from synth.util import bv_sort

from bench.util import Bench

@dataclass
class Base:
    """Base benchmark set to showcase some more sophisticated features such as constants, different theories, preconditions."""
    def test_npn4_1789(self):
        ops  = { Bl.xor2: 3, Bl.and2: 2, Bl.or2: 1 }
        name = '1789'
        spec = create_bool_func(name)
        yield Bench(spec, ops, all_ops=Bl.ops, consts={}, theory='QF_BV', name=f'npn4_{name}')

    def test_and(self):
        ops = { Bl.nand2: 2 }
        yield Bench(Bl.and2, ops, Bl.ops)

    def test_xor(self):
        ops = { Bl.nand2: 4 }
        yield Bench(Bl.xor2, ops, Bl.ops)

    def test_mux(self):
        ops = { Bl.and2: 1, Bl.xor2: 2 }
        yield Bench(Bl.mux2, ops, Bl.ops)

    def test_zero(self):
        spec = Func('zero', Not(Or([ Bool(f'x{i}') for i in range(8) ])))
        ops  = { Bl.and2: 1, Bl.nor4: 2 }
        yield Bench(spec, ops, Bl.ops, theory='QF_BV')

    def test_add(self):
        x, y, ci, s, co = Bools('x y ci s co')
        add = And([co == AtLeast(x, y, ci, 2), s == Xor(x, Xor(y, ci))])
        spec = Spec('add', add, [s, co], [x, y, ci])
        ops  = { Bl.xor2: 2, Bl.and2: 2, Bl.or2: 1 }
        yield Bench(spec, ops, Bl.ops, desc='1-bit full adder', theory='QF_BV')

    def test_add_apollo(self):
        x, y, ci, s, co = Bools('x y ci s co')
        add = And([co == AtLeast(x, y, ci, 2), s == Xor(x, Xor(y, ci))])
        spec = Spec('add_nor3', add, [s, co], [x, y, ci])
        yield Bench(spec, { Bl.nor3: 8 }, Bl.ops, desc='1-bit full adder (nor3)', theory='QF_BV')

    def test_identity(self):
        spec = Func('identity', And(Or(Bool('x'))))
        yield Bench(spec, { }, Bl.ops)

    def test_true(self):
        x, y, z = Bools('x y z')
        spec = Func('true', Or(Or(x, y, z), Not(x)))
        yield Bench(spec, { }, Bl.ops, desc='constant true')

    def test_multiple_types(self):
        x = Int('x')
        y = BitVec('y', 8)
        int2bv = Func('int2bv', Int2BV(x, 16))
        bv2int = Func('bv2int', BV2Int(y, is_signed=False))
        div2   = Func('div2', x / 2)
        spec   = Func('multiple_types', LShR(ZeroExt(8, y), 1))
        ops    = { int2bv: 1, bv2int: 1, div2: 1 }
        yield Bench(spec, ops)

    def test_precond(self):
        x = Int('x')
        b = BitVec('b', 8)
        int2bv = Func('int2bv', Int2BV(x, 8))
        bv2int = Func('bv2int', BV2Int(b))
        mul2   = Func('addadd', b + b)
        spec   = Func('precond_mul2', x * 2, And([x >= 0, x < 128]))
        ops    = { int2bv: 1, bv2int: 1, mul2: 1 }
        yield Bench(spec, ops)

    def test_fp_div(self):
        x, y, z = FPs('x y z', FPSort(3, 4))
        div   = Func('div', x / y)
        spec  = Func('fp_div', (x / y) / z)
        ops   = { div: 2 }
        yield Bench(spec, ops, consts={})

    def test_real_div(self):
        x, y, z = Reals('x y z')
        div   = Func('div', x / y, precond=(y != 0))
        spec  = Func('real_div', (x / y) / z, precond=And([y != 0, z != 0]))
        ops   = { div: 2 }
        yield Bench(spec, ops, consts={})

    def test_constant(self):
        x, y  = Ints('x y')
        mul   = Func('mul', x * y)
        spec  = Func('const', x + x)
        ops   = { mul: 1 }
        yield Bench(spec, ops)

    def test_abs(self):
        w = 32
        bv = Bv(w)
        x = BitVec('x', w)
        ops = { bv.sub_: 1, bv.xor_: 1, bv.ashr_: 1 }
        spec = Func('abs', If(x >= 0, x, -x))
        yield Bench(spec, ops, bv.ops, theory='QF_BV')

    def test_pow(self):
        x, y = Ints('x y')
        n = 24
        expr = functools.reduce(lambda a, _: x * a, range(n), IntVal(1))
        spec = Func('pow', expr)
        ops  = { Func('mul', x * y): 5 }
        yield Bench(spec, ops, consts={})

    def test_poly(self):
        a, b, c, h = Ints('a b c h')
        spec = Func('poly', a * h * h + b * h + c)
        ops  = { Func('mul', a * b): 2, Func('add', a + b): 2 }
        yield Bench(spec, ops, consts={})

    def test_arity_optimal1(self):
        a, b = Bools('a b')
        spec = Func('arity_opt1', a | (b ^ True))
        ops = { Bl.xor2: 1, Bl.or2: 1, Bl.not1: 1}
        yield Bench(spec, ops)

    def test_arity_optimal2(self):
        a, b = Bools('a b')
        spec = Func('arity_opt2', a ^ (a & b))
        ops = { Bl.and2: 1, Bl.xor2: 1, Bl.not1: 1}
        yield Bench(spec, ops)

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
        yield Bench(spec, { min: 3, max: 3 }, consts={})

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
        spec = Func('array_rev', permutation(x, [3, 2, 1, 0]))
        yield Bench(spec, { op: 6 })
