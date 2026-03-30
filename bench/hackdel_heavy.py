import math

from dataclasses import dataclass

from z3 import *

from synth.spec import Func, Spec
from bench.util import BitVecBenchSet

@dataclass
class HackdelHeavy(BitVecBenchSet):
    """p19-p24 from the 24 Hacker's Delight benchmarks from the Brahma paper."""

    def test_p19(self):
        x, e, d, k, m = BitVecs('x e d k m', self.width)
        t1  = (x & m) << k
        t2  = LShR(x, k) & m
        mm  = ~(m | (m << k))
        r   = (x & mm) | t1 | t2
        pre = And([ \
            ULE(d, k), \
            ULE(0, k), ULE(k, self.width), \
            ULE(0, e), ULE(e, self.width), \
            ULE(0, d), ULE(d, self.width), \
            ULE(d + k + e, self.width), \
            m == ((1 << d) - 1) << e \
        ])
        spec = Func('p19', r, precond=pre, inputs=[x, e, d, k, m])
        ops = { self.bv.and_: 1, self.bv.xor_: 3, self.bv.lshr_: 1, self.bv.shl_: 1 }
        consts = {}
        yield from self.create_bench('p19', spec, ops, consts, desc='exchanging two bitfields')

    def test_p20(self):
        x = BitVec('x', self.width)
        o1 = -x
        o2 = o1 & x
        o3 = x + o2
        o4 = x ^ o2
        o5 = LShR(o4, 2)
        o6 = o5 / o2
        spec = o6 | o3
        spec = Func('p20', spec, precond=(x != 0))
        ops = {
            self.bv.neg_: 1,
            self.bv.and_: 1,
            self.bv.add_: 1,
            self.bv.xor_: 1,
            self.bv.lshr_: 1,
            self.bv.udiv_: 1,
            self.bv.or_: 1,
        }
        consts = { self.const(2): 1 }
        yield from self.create_bench('p20', spec, ops, consts, desc='next higher unsigned with same number of 1s')

    def test_p21(self):
        x, a, b, c = BitVecs('x a b c', self.width)
        neq = lambda a, b: If(a == b,
                              BitVecVal(-1, self.bv.width),
                              BitVecVal(0, self.bv.width))
        o1 = neq(x, c)
        o2 = a ^ c
        o3 = neq(x, a)
        o4 = b ^ c
        o5 = o1 & o2
        o6 = o3 & o4
        o7 = o5 ^ o6
        spec = o7 ^ c
        spec = Func('p21', spec)
        ops = {
            Func('neq', neq(a, b)) : 2,
            self.bv.and_: 2,
            self.bv.xor_: 4,
        }
        consts = { }
        yield from self.create_bench('p21', spec, ops, consts, desc='Cycling through 3 values a, b, c')

    def test_p22(self):
        x = BitVec('x', self.width)
        spec = Func('p22', self.popcount(x) & 1)
        ops = { self.bv.mul_: 1, self.bv.xor_: 2, self.bv.and_: 2, self.bv.lshr_: 3 }
        consts = {
            self.one: 2,
            self.const(2): 1,
            self.const(0x1111111111111111): 2,
            self.const(self.width - 4): 1,
        }
        yield from self.create_bench('p22', spec, ops, consts, desc='parity')

    def test_p23(self):
        if self.width < 8 or self.width > 64 \
            or not math.log2(self.width).is_integer():
            print('p23 only applicable if width is [8, 16, 32, 64] bits')
            return

        # sample solution from wikipedia
        # (https://en.m.wikipedia.org/wiki/Hamming_weight)
        # x -= (x >> 1) & m1;             //put count of each 2 bits into those 2 bits
        # 1 sub, 1 lshr, 1 and, 0x55555...
        # x = (x & m2) + ((x >> 2) & m2); //put count of each 4 bits into those 4 bits
        # 2 and, 1 add, 1 lshr, 0x33333...
        # x = (x + (x >> 4)) & m4;        //put count of each 8 bits into those 8 bits
        # 1 and, 1 add, 1 lshr, 0x0f0f...

        # accumulates on 8-bit sub bitstrings
        # up to here: 1 sub, 4 and, 2 add, 3 lshr

        # each wider bit string: 1 lshr and 1 add
        # x += x >>  8;  //put count of each 16 bits into their lowest 8 bits
        # x += x >> 16;  //put count of each 32 bits into their lowest 8 bits
        # x += x >> 32;  //put count of each 64 bits into their lowest 8 bits
        # return x & 0x7f;

        l = int(math.log2(self.width))
        e = max(0, l - 3)
        consts = {
            BitVecVal(0x5555555555555555, self.width): 1,
            BitVecVal(0x3333333333333333, self.width): 2,
            BitVecVal(0x0f0f0f0f0f0f0f0f, self.width): 1,
        }
        # shifts for each power of two: 1, 2, 4, ...
        consts.update({ BitVecVal(1 << i, self.width): 1 for i in range(0, l) })

        x = BitVec('x', self.width)
        spec = Func('p23', self.popcount(x))
        ops = { self.bv.add_: 2 + e, self.bv.lshr_: 3 + e,
                self.bv.and_: 4, self.bv.sub_: 1 }
        yield from self.create_bench('p23', spec, ops, consts, desc='population count')

    def test_p24(self):
        l = int(math.log2(self.width))
        x, y = BitVecs('x y', self.width)
        phi = And([ self.is_power_of_two(y), ULE(x, y), ULE(y, 2 * x) ])
        pre = And([ULT(0, x), ULT(x, 2 ** (self.width - 1))])
        spec = Spec('p24', phi, [ y ], [ x ], precond=pre)
        ops = { self.bv.add_: 1, self.bv.sub_: 1, self.bv.or_: l, self.bv.lshr_: l }
        consts = { self.one: 3 }
        for i in range(1, l):
            consts.update({ self.const(1 << i): 1 })
        yield from self.create_bench('p24', spec, ops, consts, desc='round up to next power of 2')