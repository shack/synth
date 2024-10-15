#! /usr/bin/env python3

# Specs fully taken from SyGus benchmarks

from z3 import *
from synth.spec import Func, Spec
from bench.util import BitVecBenchSet

class HackdelSygus(BitVecBenchSet):
    """The Hacker's Delight benchmarks with specifications, operators, constants as defined in the SyGuS competition."""

    # def test_p01(self):
    #     x = BitVec('x', self.width)
    #     spec = Func('p01', x & (x - 1))
    #     ops = { self.bv.and_: 1, self.bv.sub_: 1 }
    #     return self.create_bench('p01', spec, ops, desc='turn off rightmost bit')

    def test_p01_d1(self):
        x = BitVec('x', self.width)
        spec = Func('p01', x & (x - 1))
        ops = [self.bv.and_, self.bv.sub_, self.bv.or_, self.bv.add_, self.bv.xor_]
        consts = {self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1, self.const(0x0000000000000001): 1}
        return self.create_bench('p01_d1', spec, ops, consts, desc='turn off rightmost bit')

    def test_p01_d5(self):
        x = BitVec('x', self.width)
        spec = Func('p01', x & (x - 1))
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1, self.const(0x0000000000000001): 1}
        return self.create_bench('p01_d5', spec, ops, consts, desc='turn off rightmost bit')

    # def test_p02(self):
    #     x = BitVec('x', self.width)
    #     o = BitVec('o', self.width)
    #     pt = self.is_power_of_two(x)
    #     spec = Spec('p02', If(pt, o == self.zero, o != self.zero), [ o ], [ x ])
    #     ops = { self.bv.and_: 1, self.bv.sub_: 1 }
    #     return self.create_bench('p02', spec, ops, desc='unsigned test if power of 2')

    def test_p02_d0(self):
        x = BitVec('x', self.width)
        o = BitVec('o', self.width)
        spec = Spec('p02', o == x & (x + 1), [ o ], [ x ])
        ops = [self.bv.and_, self.bv.add_]
        consts = {self.const(0x0000000000000001): 1}
        return self.create_bench('p02_d0', spec, ops, consts, desc='unsigned test if power of 2')

    def test_p02_d1(self):
        x = BitVec('x', self.width)
        o = BitVec('o', self.width)
        spec = Spec('p02', o == x & (x + 1), [ o ], [ x ])
        ops = [self.bv.and_, self.bv.sub_, self.bv.or_, self.bv.add_, self.bv.xor_]
        consts = {self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1, self.const(0x0000000000000001): 1}
        return self.create_bench('p02_d1', spec, ops, consts, desc='unsigned test if power of 2')

    def test_p02_d5(self):
        x = BitVec('x', self.width)
        o = BitVec('o', self.width)
        spec = Spec('p02', o == x & (x + 1), [ o ], [ x ])
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1, self.const(0x0000000000000001): 1}
        return self.create_bench('p02_d5', spec, ops, consts, desc='unsigned test if power of 2')

    # def test_p03(self):
    #     x = BitVec('x', self.width)
    #     spec = Func('p03', x & -x)
    #     ops = { self.bv.and_: 1, self.bv.sub_: 1 }
    #     return self.create_bench('p03', spec, ops, \
    #                          desc='isolate rightmost 1-bit')

    def test_p03_d0(self):
        x = BitVec('x', self.width)
        spec = Func('p03', x & -x)
        ops = [self.bv.neg_, self.bv.and_]
        consts = {}
        return self.create_bench('p03_d0', spec, ops, consts, \
                             desc='isolate rightmost 1-bit')

    def test_p03_d1(self):
        x = BitVec('x', self.width)
        spec = Func('p03', x & -x)
        ops = [self.bv.neg_, self.bv.and_, self.bv.or_, self.bv.add_, self.bv.sub_]
        consts = {self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p03_d1', spec, ops, consts, \
                             desc='isolate rightmost 1-bit')

    def test_p03_d5(self):
        x = BitVec('x', self.width)
        spec = Func('p03', x & -x)
        ops = [self.bv.not_, self.bv.and_, self.bv.xor_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p03_d5', spec, ops, consts, \
                             desc='isolate rightmost 1-bit')

    # def test_p04(self):
    #     x = BitVec('x', self.width)
    #     spec = Func('p04', x ^ (x - 1))
    #     ops = { self.bv.xor_: 1, self.bv.sub_: 1 }
    #     return self.create_bench('p04', spec, ops, \
    #                          desc='mask rightmost 1-bits')

    def test_p04_d0(self):
        x = BitVec('x', self.width)
        spec = Func('p04', x ^ (x - 1))
        ops = [self.bv.sub_, self.bv.xor_]
        consts = {self.const(0x0000000000000001): 1}
        return self.create_bench('p04_d0', spec, ops, consts, \
                             desc='mask rightmost 1-bits')

    def test_p04_d1(self):
        x = BitVec('x', self.width)
        spec = Func('p04', x ^ (x - 1))
        ops = [self.bv.sub_, self.bv.xor_, self.bv.neg_, self.bv.add_, self.bv.or_, self.bv.and_]
        consts = {self.const(0x0000000000000000): 1, self.const(0x0000000000000001): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p04_d1', spec, ops, consts, \
                             desc='mask rightmost 1-bits')

    def test_p04_d5(self):
        x = BitVec('x', self.width)
        spec = Func('p04', x ^ (x - 1))
        ops = [self.bv.not_, self.bv.and_, self.bv.xor_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x0000000000000000): 1, self.const(0x0000000000000001): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p04_d5', spec, ops, consts, \
                             desc='mask rightmost 1-bits')

    # def test_p05(self):
    #     x = BitVec('x', self.width)
    #     spec = Func('p05', x | (x - 1))
    #     ops = { self.bv.or_: 1, self.bv.sub_: 1 }
    #     return self.create_bench('p05', spec, ops, \
    #                          desc='right-propagate rightmost 1-bit')

    def test_p05_d0(self):
        x = BitVec('x', self.width)
        spec = Func('p05', x | (x - 1))
        ops = [self.bv.sub_, self.bv.or_]
        consts = {self.const(0x0000000000000001): 1}
        return self.create_bench('p05_d0', spec, ops, consts, \
                             desc='right-propagate rightmost 1-bit')

    def test_p05_d1(self):
        x = BitVec('x', self.width)
        spec = Func('p05', x | (x - 1))
        ops = [self.bv.sub_, self.bv.neg_, self.bv.add_, self.bv.and_, self.bv.xor_, self.bv.or_]
        consts = {self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p05_d1', spec, ops, consts, \
                             desc='right-propagate rightmost 1-bit')

    def test_p05_d5(self):
        x = BitVec('x', self.width)
        spec = Func('p05', x | (x - 1))
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p05_d5', spec, ops, consts, \
                             desc='right-propagate rightmost 1-bit')

    # def test_p06(self):
    #     x = BitVec('x', self.width)
    #     spec = Func('p06', x | (x + 1))
    #     ops = { self.bv.or_: 1, self.bv.add_: 1 }
    #     return self.create_bench('p06', spec, ops, \
    #                          desc='turn on rightmost 0-bit')

    def test_p06_d0(self):
        x = BitVec('x', self.width)
        spec = Func('p06', x | (x + 1))
        ops = [self.bv.add_, self.bv.or_]
        consts = {self.const(0x0000000000000001): 1}
        return self.create_bench('p06_d0', spec, ops, consts,\
                             desc='turn on rightmost 0-bit')

    def test_p06_d1(self):
        x = BitVec('x', self.width)
        spec = Func('p06', x | (x + 1))
        ops = [self.bv.add_, self.bv.sub_, self.bv.xor_, self.bv.and_, self.bv.neg_, self.bv.or_]
        consts = {self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1, self.const(0x0000000000000001): 1}
        return self.create_bench('p06_d1', spec, ops, consts, \
                             desc='turn on rightmost 0-bit')

    def test_p06_d5(self):
        x = BitVec('x', self.width)
        spec = Func('p06', x | (x + 1))
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1, self.const(0x0000000000000001): 1}
        return self.create_bench('p06_d5', spec, ops, consts, \
                             desc='turn on rightmost 0-bit')

    # def test_p07(self):
    #     x = BitVec('x', self.width)
    #     spec = Func('p07', ~x & (x + 1))
    #     ops = { self.bv.xor_: 1, self.bv.add_: 1, self.bv.and_: 1 }
    #     return self.create_bench('p07', spec, ops, \
    #                          desc='isolate rightmost 0-bit')

    def test_p07_d0(self):
        x = BitVec('x', self.width)
        spec = Func('p07', ~x & (x + 1))
        ops = [self.bv.add_, self.bv.not_, self.bv.and_]
        consts = {self.const(0x0000000000000001): 1}
        return self.create_bench('p07_d0', spec, ops, consts, \
                             desc='isolate rightmost 0-bit')

    def test_p07_d1(self):
        x = BitVec('x', self.width)
        spec = Func('p07', ~x & (x + 1))
        ops = [self.bv.add_, self.bv.sub_, self.bv.not_, self.bv.neg_, self.bv.and_, self.bv.or_, self.bv.xor_]
        consts = {self.const(0x0000000000000000): 1, self.const(0x0000000000000001): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p07_d1', spec, ops, consts, \
                             desc='isolate rightmost 0-bit')

    def test_p07_d5(self):
        x = BitVec('x', self.width)
        spec = Func('p07', ~x & (x + 1))
        ops = [self.bv.not_, self.bv.and_, self.bv.xor_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x0000000000000000): 1, self.const(0x0000000000000001): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p07_d5', spec, ops, consts, \
                             desc='isolate rightmost 0-bit')

    # def test_p08(self):
    #     x = BitVec('x', self.width)
    #     spec = Func('p08', ~x & (x - 1))
    #     ops = { self.bv.xor_: 1, self.bv.sub_: 1, self.bv.and_: 1 }
    #     return self.create_bench('p08', spec, ops, \
    #                          desc='mask for trailing 0s')

    def test_p08_d0(self):
        x = BitVec('x', self.width)
        spec = Func('p08', ~x & (x - 1))
        ops = [self.bv.sub_, self.bv.not_, self.bv.and_]
        consts = {self.const(0x0000000000000001): 1}
        return self.create_bench('p08_d0', spec, ops, consts, \
                             desc='mask for trailing 0s')

    def test_p08_d1(self):
        x = BitVec('x', self.width)
        spec = Func('p08', ~x & (x - 1))
        ops = [self.bv.sub_, self.bv.add_, self.bv.not_, self.bv.neg_, self.bv.and_, self.bv.or_, self.bv.xor_]
        consts = {self.const(0x0000000000000000): 1, self.const(0x0000000000000001): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p08_d1', spec, ops, consts, \
                             desc='mask for trailing 0s')

    def test_p08_d5(self):
        x = BitVec('x', self.width)
        spec = Func('p08', ~x & (x - 1))
        ops = [self.bv.not_, self.bv.and_, self.bv.or_, self.bv.xor_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x0000000000000000): 1, self.const(0x0000000000000001): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p08_d5', spec, ops, consts, \
                             desc='mask for trailing 0s')

    # def test_p09(self):
    #     x = BitVec('x', self.width)
    #     spec = Func('p09', If(x < 0, -x, x))
    #     ops = { self.bv.xor_: 1, self.bv.sub_: 1, self.bv.ashr_: 1 }
    #     return self.create_bench('p09', spec, ops, desc='abs function')

    def test_p09_d0(self):
        r = self.width - 1
        x = BitVec('x', self.width)
        spec = Func('p09', (x ^ (x >> r)) - (x >> r))
        ops = [self.bv.sub_, self.bv.ashr_, self.bv.xor_]
        consts = {self.const(r): 1}
        return self.create_bench('p09_d0', spec, ops, consts, desc='abs function')

    def test_p09_d1(self):
        r = self.width - 1
        x = BitVec('x', self.width)
        spec = Func('p09', (x ^ (x >> r)) - (x >> r))
        ops = [self.bv.sub_, self.bv.add_, self.bv.ashr_, self.bv.lshr_, self.bv.xor_, self.bv.and_, self.bv.or_]
        consts = {self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(r): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p09_d1', spec, ops, consts, desc='abs function')

    def test_p09_d5(self):
        r = self.width - 1
        x = BitVec('x', self.width)
        spec = Func('p09', (x ^ (x >> r)) - (x >> r))
        ops = [self.bv.not_, self.bv.and_, self.bv.xor_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(r): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p09_d5', spec, ops, consts, desc='abs function')

    # def test_p10(self):
    #     x, y = BitVecs('x y', self.width)
    #     spec = Func('p10', If(self.nlz(x) == self.nlz(y), self.one, self.zero))
    #     ops = { self.bv.xor_: 1, self.bv.and_: 1, self.bv.uge_: 1 }
    #     return self.create_bench('p10', spec, ops, desc='nlz equal')

    # def test_p11(self):
    #     x, y = BitVecs('x y', self.width)
    #     spec = Func('p11', If(self.nlz(x) < self.nlz(y), self.one, self.zero))
    #     ops = { self.bv.xor_: 1, self.bv.and_: 1, self.bv.ult_: 1 }
    #     return self.create_bench('p11', spec, ops, desc='nlz less than')

    # def test_p12(self):
    #     x, y = BitVecs('x y', self.width)
    #     spec = Func('p12', If(self.nlz(x) <= self.nlz(y), self.one, self.zero))
    #     ops = { self.bv.xor_: 1, self.bv.and_: 1, self.bv.uge_: 1 }
    #     return self.create_bench('p12', spec, ops, desc='nlz less than or equal')

    # def test_p13(self):
    #     x = BitVec('x', self.width)
    #     m1 = BitVecVal(-1, self.width)
    #     p1 = BitVecVal(1, self.width)
    #     spec = Func('p13', If(x < 0, m1, If(x > 0, p1, 0)))
    #     ops = { self.bv.sub_: 1, self.bv.or_: 1, self.bv.ashr_: 1, self.bv.lshr_: 1 }
    #     return self.create_bench('p13', spec, ops, desc='sign function')

    def test_p13_d0(self):
        r = self.width - 1
        x = BitVec('x', self.width)
        spec = Func('p13', (x >> r) | LShR(~x, r))
        ops = [self.bv.lshr_, self.bv.ashr_, self.bv.or_, self.bv.neg_]
        consts = {self.const(r): 1}
        return self.create_bench('p13_d0', spec, ops, consts, desc='sign function')

    def test_p13_d1(self):
        r = self.width - 1
        x = BitVec('x', self.width)
        spec = Func('p13', (x >> r) | LShR(~x, r))
        ops = [self.bv.lshr_, self.bv.ashr_, self.bv.and_, self.bv.xor_, self.bv.or_, self.bv.neg_, self.bv.not_, self.bv.add_, self.bv.sub_]
        consts = {self.const(r): 1, self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p13_d1', spec, ops, consts, desc='sign function')

    def test_p13_d5(self):
        r = self.width - 1
        x = BitVec('x', self.width)
        spec = Func('p13', (x >> r) | LShR(~x, r))
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(r): 1, self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p13_d5', spec, ops, consts, desc='sign function')

    # def test_p14(self):
    #     x, y = BitVecs('x y', self.width)
    #     spec = Func('p14', Int2BV((BV2Int(x) + BV2Int(y)) / 2, self.width))
    #     ops = { self.bv.and_: 1, self.bv.xor_: 1, self.bv.lshr_: 1, self.bv.add_: 1 }
    #     return self.create_bench('p14', spec, ops, \
    #                          desc='floor of avg of two ints without overflow', max_const=1)

    def test_p14_d0(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p14', (x & y) + ((x ^ y) >> 1))
        ops = [self.bv.lshr_, self.bv.xor_, self.bv.add_, self.bv.and_]
        consts = {self.const(0x0000000000000001): 1}
        return self.create_bench('p14_d0', spec, ops, consts, \
                             desc='floor of avg of two ints without overflow')

    def test_p14_d1(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p14', (x & y) + ((x ^ y) >> 1))
        ops = [self.bv.lshr_, self.bv.ashr_, self.bv.xor_, self.bv.or_, self.bv.add_, self.bv.sub_, self.bv.and_, self.bv.neg_, self.bv.not_]
        consts = {self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p14_d1', spec, ops, consts, \
                             desc='floor of avg of two ints without overflow')

    def test_p14_d5(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p14', (x & y) + ((x ^ y) >> 1))
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x000000000000001F): 1, self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p14_d5', spec, ops, consts, \
                             desc='floor of avg of two ints without overflow')

    # def test_p15(self):
    #     x, y = BitVecs('x y', self.width)
    #     spec = Func('p15', Int2BV((BV2Int(x) + BV2Int(y) - 1) / 2 + 1, self.width))
    #     ops = { self.bv.or_: 1, self.bv.xor_: 1, self.bv.lshr_: 1, self.bv.sub_: 1 }
    #     return self.create_bench('p15', spec, ops, \
    #                          desc='ceil of avg of two ints without overflow', max_const=1)

    def test_p15_d0(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p15', (x | y) - (LShR(x ^y, 1)))
        ops = [self.bv.lshr_, self.bv.xor_, self.bv.sub_, self.bv.or_]
        consts = {self.const(0x0000000000000001): 1}
        return self.create_bench('p15_d0', spec, ops, consts, \
                             desc='ceil of avg of two ints without overflow')

    def test_p15_d1(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p15', (x | y) - (LShR(x ^y, 1)))
        ops = [self.bv.lshr_, self.bv.ashr_, self.bv.xor_, self.bv.sub_, self.bv.add_, self.bv.or_, self.bv.and_, self.bv.neg_, self.bv.not_]
        consts = {self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p15_d1', spec, ops, consts, \
                             desc='ceil of avg of two ints without overflow')

    def test_p15_d5(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p15', (x | y) - (LShR(x ^y, 1)))
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x000000000000001F): 1, self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p15_d5', spec, ops, consts, \
                             desc='ceil of avg of two ints without overflow')

    # def test_p16(self):
    #     x, y = BitVecs('x y', self.width)
    #     spec = Func('p16', If(x >= y, x, y))
    #     ops = { self.bv.and_: 1, self.bv.xor_: 2, self.bv.neg_: 1,  self.bv.slt_: 1 }
    #     return self.create_bench('p16', spec, ops, \
    #                          desc='max of two ints', max_const=3)

    # def test_p17(self):
    #     x, y = BitVecs('x y', self.width)
    #     spec = Func('p17', (((x - 1) | x) + 1) & x)
    #     ops = { self.bv.sub_: 1, self.bv.or_: 1, self.bv.add_: 1,  self.bv.and_: 1 }
    #     return self.create_bench('p17', spec, ops, \
    #                          desc='turn off the rightmost string of 1-bits', \
    #                          max_const=2)

    def test_p17_d0(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p17', (((x - 1) | x) + 1) & x)
        ops = [self.bv.and_, self.bv.add_, self.bv.sub_, self.bv.or_]
        consts = {self.const(0x0000000000000001): 1}
        return self.create_bench('p17_d0', spec, ops, consts, \
                             desc='turn off the rightmost string of 1-bits')

    def test_p17_d1(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p17', (((x - 1) | x) + 1) & x)
        ops = [self.bv.and_, self.bv.add_, self.bv.xor_, self.bv.sub_, self.bv.or_, self.bv.not_, self.bv.neg_]
        consts = {self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p17_d1', spec, ops, consts, \
                             desc='turn off the rightmost string of 1-bits')

    def test_p17_d5(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p17', (((x - 1) | x) + 1) & x)
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x000000000000001F): 1, self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p17_d5', spec, ops, consts, \
                             desc='turn off the rightmost string of 1-bits')

    # def test_p18(self):
    #     one = BitVecVal(1, self.width)
    #     zero = BitVecVal(0, self.width)
    #     x = BitVec('x', self.width)
    #     spec = Func('p18', If(Or([x == (1 << i) for i in range(self.width)]), zero, one))
    #     ops = { self.bv.neg_: 1, self.bv.xor_: 1, self.bv.uge_: 1, }
    #     return self.create_bench('p18', spec, ops, \
    #                          desc='check if power of 2')

    # def test_p19(self):
    #     x, e, d, k, m = BitVecs('x e d k m', self.width)
    #     t1  = (x & m) << k
    #     t2  = LShR(x, k) & m
    #     mm  = ~(m | (m << k))
    #     r   = (x & mm) | t1 | t2
    #     pre = And([ \
    #         ULE(d, k), \
    #         ULE(0, k), ULE(k, self.width), \
    #         ULE(0, e), ULE(e, self.width), \
    #         ULE(0, d), ULE(d, self.width), \
    #         ULE(d + k + e, self.width), \
    #         m == ((1 << d) - 1) << e \
    #     ])
    #     spec = Func('p19', r, precond=pre, inputs=[x, e, d, k, m])
    #     ops = { self.bv.and_: 1, self.bv.xor_: 3, self.bv.lshr_: 1, self.bv.shl_: 1 }
    #     return self.create_bench('p19', spec, ops, \
    #                          desc='exchanging two bitfields', \
    #                          max_const=0)

    def test_p19_d0(self):
        x, k, m = BitVecs('x k m', self.width)
        t1  = (LShR(x, k) ^ x) & m
        t2 = t1 << k
        r = x ^ (t2 ^ t1)
        spec = Func('p19', r, inputs=[x, k, m])
        ops = [self.bv.and_, self.bv.xor_, self.bv.shl_, self.bv.lshr_]
        consts = {}
        return self.create_bench('p19_d0', spec, ops, consts, \
                             desc='exchanging two bitfields')

    def test_p19_d1(self):
        x, k, m = BitVecs('x k m', self.width)
        t1  = (LShR(x, k) ^ x) & m
        t2 = t1 << k
        r = x ^ (t2 ^ t1)
        spec = Func('p19', r, inputs=[x, k, m])
        ops = [self.bv.and_, self.bv.sub_, self.bv.xor_, self.bv.or_, self.bv.and_, self.bv.shl_, self.bv.lshr_, self.bv.ashr_, self.bv.not_, self.bv.neg_]
        consts = {}
        return self.create_bench('p19_d1', spec, ops, consts, \
                             desc='exchanging two bitfields')

    def test_p19_d5(self):
        x, k, m = BitVecs('x k m', self.width)
        t1  = (LShR(x, k) ^ x) & m
        t2 = t1 << k
        r = x ^ (t2 ^ t1)
        spec = Func('p19', r, inputs=[x, k, m])
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        # 4 consts: ['#x1F', '#x01', '#x00', '#xff']
        consts = {self.const(0x000000000000001F): 1, self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}

        return self.create_bench('p19_d5', spec, ops, consts, \
                             desc='exchanging two bitfields')

    # def test_p20(self):
    #     x = BitVec('x', self.width)
    #     o1 = -x
    #     o2 = o1 & x
    #     o3 = x + o2
    #     o4 = x ^ o2
    #     o5 = LShR(o4, 2)
    #     o6 = o5 / o2
    #     spec = o6 | o3
    #     spec = Func('p22', spec)
    #     ops = {
    #         self.bv.neg_: 1,
    #         self.bv.and_: 1,
    #         self.bv.add_: 1,
    #         self.bv.xor_: 1,
    #         self.bv.lshr_: 1,
    #         self.bv.udiv_: 1,
    #         self.bv.or_: 1,
    #     }
    #     return self.create_bench('p20', spec, ops, \
    #                          desc='next higher unsigned with same number of 1s', \
    #                          max_const=1)

    def test_p20_d0(self):
        x = BitVec('x', self.width)
        o1 = -x
        o2 = o1 & x
        o3 = x + o2
        o4 = x ^ o2
        o5 = LShR(o4, 2)
        o6 = o5 / o2
        spec = o6 | o3
        spec = Func('p22', spec)
        ops = [self.bv.and_, self.bv.xor_, self.bv.or_, self.bv.add_, self.bv.lshr_, self.bv.neg_, self.bv.udiv_]
        consts = {self.const(0x00000002): 1}
        return self.create_bench('p20_d0', spec, ops, consts, \
                             desc='next higher unsigned with same number of 1s')

    def test_p20_d1(self):
        x = BitVec('x', self.width)
        o1 = -x
        o2 = o1 & x
        o3 = x + o2
        o4 = x ^ o2
        o5 = LShR(o4, 2)
        o6 = o5 / o2
        spec = o6 | o3
        spec = Func('p22', spec)
        ops = [self.bv.and_, self.bv.xor_, self.bv.or_, self.bv.add_, self.bv.sub_, self.bv.lshr_, self.bv.neg_, self.bv.not_, self.bv.udiv_, self.bv.div_]
        consts = {self.const(0x00000002): 1, self.const(0x0000000000000000): 1, self.const(0x0000000000000001): 1}
        return self.create_bench('p20_d1', spec, ops, consts, \
                             desc='next higher unsigned with same number of 1s')

    def test_p20_d5(self):
        x = BitVec('x', self.width)
        o1 = -x
        o2 = o1 & x
        o3 = x + o2
        o4 = x ^ o2
        o5 = LShR(o4, 2)
        o6 = o5 / o2
        spec = o6 | o3
        spec = Func('p22', spec)
        ops = [self.bv.not_, self.bv.xor_, self.bv.and_, self.bv.or_, self.bv.neg_, self.bv.add_, self.bv.mul_, self.bv.udiv_, self.bv.urem_, self.bv.lshr_, self.bv.ashr_, self.bv.shl_, self.bv.div_, self.bv.srem_, self.bv.sub_]
        consts = {self.const(0x000000000000001F): 1, self.const(0x0000000000000001): 1, self.const(0x0000000000000000): 1, self.const(0xFFFFFFFFFFFFFFFF): 1}
        return self.create_bench('p20_d5', spec, ops, consts, \
                             desc='next higher unsigned with same number of 1s')

    # def test_p21(self):
    #     x, a, b, c = BitVecs('x a b c', self.width)
    #     neq = lambda a, b: If(a == b, \
    #                           BitVecVal(-1, self.bv.width), \
    #                           BitVecVal(0, self.bv.width))
    #     o1 = neq(x, c)
    #     o2 = a ^ c
    #     o3 = neq(x, a)
    #     o4 = b ^ c
    #     o5 = o1 & o2
    #     o6 = o3 & o4
    #     o7 = o5 ^ o6
    #     spec = o7 ^ c
    #     spec = Func('p22', spec)
    #     ops = {
    #         Func('neq', neq(a, b)) : 2,
    #         self.bv.and_: 2,
    #         self.bv.xor_: 4,
    #     }
    #     return self.create_bench('p21', spec, ops, \
    #                          desc='Cycling through 3 values a, b, c', \
    #                          max_const=1)

    # def test_p22(self):
    #     x = BitVec('x', self.width)
    #     spec = Func('p22', self.popcount(x) & 1)
    #     ops = { self.bv.mul_: 1, self.bv.xor_: 2, self.bv.and_: 2, self.bv.lshr_: 3 }
    #     return self.create_bench('p22', spec, ops, \
    #                          desc='parity', \
    #                          max_const=5)

    # def test_p23(self):
    #     if self.width < 8 or self.width > 64 \
    #         or not math.log2(self.width).is_integer():
    #         print('p23 only applicable if width is [8, 16, 32, 64] bits')
    #         return

    #     # sample solution from wikipedia
    #     # (https://en.m.wikipedia.org/wiki/Hamming_weight)
    #     # x -= (x >> 1) & m1;             //put count of each 2 bits into those 2 bits
    #     # 1 sub, 1 lshr, 1 and, 0x55555...
    #     # x = (x & m2) + ((x >> 2) & m2); //put count of each 4 bits into those 4 bits
    #     # 2 and, 1 add, 1 lshr, 0x33333...
    #     # x = (x + (x >> 4)) & m4;        //put count of each 8 bits into those 8 bits
    #     # 1 and, 1 add, 1 lshr, 0x0f0f...

    #     # accumulates on 8-bit sub bitstrings
    #     # up to here: 1 sub, 3 and, 3 add, 3 lshr

    #     # each wider bit string: 1 lshr and 1 add
    #     # x += x >>  8;  //put count of each 16 bits into their lowest 8 bits
    #     # x += x >> 16;  //put count of each 32 bits into their lowest 8 bits
    #     # x += x >> 32;  //put count of each 64 bits into their lowest 8 bits
    #     # return x & 0x7f;

    #     l = int(math.log2(self.width))
    #     e = max(0, l - 3)
    #     masks = [
    #         0x5555555555555555,
    #         0x3333333333333333,
    #         0x0f0f0f0f0f0f0f0f,
    #     ]
    #     # masks for 8-bit sub bitstrings
    #     consts = set(BitVecVal(c, self.width) for c in masks)
    #     # shifts for each power of two: 1, 2, 4, ...
    #     consts.update(BitVecVal(1 << i, self.width) for i in range(0, l))
    #     n_consts = len(consts) + 1 + (e > 0)

    #     x = BitVec('x', self.width)
    #     spec = Func('p23', self.popcount(x))
    #     ops = { self.bv.add_: 3 + e, self.bv.lshr_: 3 + e, \
    #             self.bv.and_: 3, self.bv.sub_: 1 }
    #     return self.create_bench('p23', spec, ops, \
    #                          desc='population count', \
    #                          max_const=n_consts, \
    #                          const_set=consts)

    # def test_p24(self):
    #     l = int(math.log2(self.width))
    #     x, y = BitVecs('x y', self.width)
    #     phi = And([ self.is_power_of_two(y), ULE(x, y), ULE(y, 2 * x) ])
    #     pre = ULT(x, 2 ** (self.width - 1))
    #     spec = Spec('p24', phi, [ y ], [ x ], precond=pre)
    #     ops = { self.bv.add_: 1, self.bv.sub_: 1, self.bv.or_: l, self.bv.lshr_: l }
    #     consts = set(BitVecVal(1 << i, self.width) for i in range(0, l))
    #     return self.create_bench('p24', spec, ops, \
    #                          desc='round up to next power of 2', \
    #                          max_const=len(consts) + 2, \
    #                          const_set=consts)