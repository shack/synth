from dataclasses import dataclass

from z3 import *

from synth.spec import Func, Spec
from bench.util import BitVecBenchSet

@dataclass
class HackdelLight(BitVecBenchSet):
    """p01-p18 from the Hacker's Delight benchmarks from the Brahma paper."""

    def test_p01(self):
        x = BitVec('x', self.width)
        spec = Func('p01', x & (x - 1))
        ops = { self.bv.and_: 1, self.bv.sub_: 1 }
        consts = { self.one: 1 }
        yield from self.create_bench('p01', spec, ops, consts, desc='turn off rightmost bit')

    def test_p02(self):
        x = BitVec('x', self.width)
        o = BitVec('o', self.width)
        pt = Or([self.is_power_of_two(x), x == 0])
        spec = Spec('p02', If(pt, o == self.zero, o != self.zero), [ o ], [ x ])
        ops = { self.bv.and_: 1, self.bv.sub_: 1 }
        consts = { self.one: 1 }
        yield from self.create_bench('p02', spec, ops, consts, desc='unsigned test if power of 2')

    def test_p03(self):
        x = BitVec('x', self.width)
        spec = Func('p03', x & -x)
        ops = { self.bv.and_: 1, self.bv.sub_: 1 }
        consts = { self.zero: 1 }
        yield from self.create_bench('p03', spec, ops, consts, desc='isolate rightmost 1-bit')

    def test_p04(self):
        x = BitVec('x', self.width)
        spec = Func('p04', x ^ (x - 1))
        ops = { self.bv.xor_: 1, self.bv.sub_: 1 }
        consts = { self.one: 1 }
        yield from self.create_bench('p04', spec, ops, consts, desc='mask rightmost 1-bits')

    def test_p05(self):
        x = BitVec('x', self.width)
        spec = Func('p05', x | (x - 1))
        ops = { self.bv.or_: 1, self.bv.sub_: 1 }
        consts = { self.one: 1 }
        yield from self.create_bench('p05', spec, ops, consts, desc='right-propagate rightmost 1-bit')

    def test_p06(self):
        x = BitVec('x', self.width)
        spec = Func('p06', x | (x + 1))
        ops = { self.bv.or_: 1, self.bv.add_: 1 }
        consts = { self.one: 1 }
        yield from self.create_bench('p06', spec, ops, consts, desc='turn on rightmost 0-bit')

    def test_p07(self):
        x = BitVec('x', self.width)
        spec = Func('p07', ~x & (x + 1))
        ops = { self.bv.xor_: 1, self.bv.add_: 1, self.bv.and_: 1 }
        consts = { self.one: 1 }
        yield from self.create_bench('p07', spec, ops, consts, desc='isolate rightmost 0-bit')

    def test_p08(self):
        x = BitVec('x', self.width)
        spec = Func('p08', ~x & (x - 1))
        ops = { self.bv.xor_: 1, self.bv.sub_: 1, self.bv.and_: 1 }
        consts = { self.one: 1 }
        yield from self.create_bench('p08', spec, ops, consts, desc='mask for trailing 0s')

    def test_p09(self):
        x = BitVec('x', self.width)
        spec = Func('p09', If(x < 0, -x, x))
        ops = { self.bv.xor_: 1, self.bv.sub_: 1, self.bv.ashr_: 1 }
        consts = { self.const(self.width - 1): 1 }
        yield from self.create_bench('p09', spec, ops, consts, desc='abs function')

    def test_p10(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p10', If(self.nlz(x) == self.nlz(y), self.one, self.zero))
        ops = { self.bv.xor_: 1, self.bv.and_: 1, self.bv.uge_: 1 }
        consts = {}
        yield from self.create_bench('p10', spec, ops, consts, desc='nlz equal')

    def test_p11(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p11', If(self.nlz(x) < self.nlz(y), self.one, self.zero))
        ops = { self.bv.xor_: 1, self.bv.and_: 1, self.bv.ult_: 1 }
        consts = {}
        yield from self.create_bench('p11', spec, ops, consts, desc='nlz less than')

    def test_p12(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p12', If(self.nlz(x) <= self.nlz(y), self.one, self.zero))
        ops = { self.bv.xor_: 1, self.bv.and_: 1, self.bv.uge_: 1 }
        consts = {}
        yield from self.create_bench('p12', spec, ops, consts, desc='nlz less than or equal')

    def test_p13(self):
        x = BitVec('x', self.width)
        m1 = BitVecVal(-1, self.width)
        p1 = BitVecVal(1, self.width)
        spec = Func('p13', If(x < 0, m1, If(x > 0, p1, 0)))
        ops = { self.bv.sub_: 1, self.bv.or_: 1, self.bv.ashr_: 1, self.bv.lshr_: 1 }
        consts = { self.const(self.width - 1): 2 }
        yield from self.create_bench('p13', spec, ops, consts, desc='sign function')

    def test_p14(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p14', LShR(x ^ y, self.one) + (x & y))
        ops = { self.bv.and_: 1, self.bv.xor_: 1, self.bv.lshr_: 1, self.bv.add_: 1 }
        consts = { self.one: 1 }
        yield from self.create_bench('p14', spec, ops, consts, desc='floor of avg of two ints without overflow')

    def test_p15(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p15', (x | y) - LShR(x ^ y, self.one))
        ops = { self.bv.or_: 1, self.bv.xor_: 1, self.bv.lshr_: 1, self.bv.sub_: 1 }
        consts = { self.one: 1 }
        yield from self.create_bench('p15', spec, ops, consts, desc='ceil of avg of two ints without overflow')

    def test_p16(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p16', If(x >= y, x, y))
        ops = { self.bv.and_: 1, self.bv.xor_: 2, self.bv.neg_: 1,  self.bv.slt_: 1 }
        consts = {}
        yield from self.create_bench('p16', spec, ops, consts, desc='max of two ints')

    def test_p17(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p17', (((x - 1) | x) + 1) & x)
        ops = { self.bv.sub_: 1, self.bv.or_: 1, self.bv.add_: 1,  self.bv.and_: 1 }
        consts = { self.one: 2 }
        yield from self.create_bench('p17', spec, ops, consts, desc='turn off the rightmost string of 1-bits')

    def test_p18(self):
        one = BitVecVal(1, self.width)
        zero = BitVecVal(0, self.width)
        x = BitVec('x', self.width)
        spec = Func('p18', If(Or([x == (1 << i) for i in range(self.width)]), zero, one))
        ops = { self.bv.neg_: 1, self.bv.xor_: 1, self.bv.uge_: 1, }
        consts = {}
        yield from self.create_bench('p18', spec, ops, consts, desc='check if power of 2')