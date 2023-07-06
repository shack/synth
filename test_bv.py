#! /usr/bin/env python3

from z3 import *
from synth import *

class BvBench(TestBase):
    def __init__(self, width, args):
        super().__init__(**vars(args))
        self.width = width
        self.bv    = Bv(width)
        self.ops = [
            self.bv.add_,
            self.bv.sub_,
            self.bv.and_,
            self.bv.or_,
            self.bv.xor_,
            self.bv.neg_,
            self.bv.not_,
            self.bv.ashr_,
            self.bv.lshr_,
            self.bv.shl_,
            self.bv.ult_,
            self.bv.uge_,
            self.bv.slt_,
            self.bv.sge_,
        ]
        self.one = BitVecVal(1, self.width)
        self.zero = BitVecVal(0, self.width)

    def test_p01(self):
        x = BitVec('x', self.width)
        spec = Func('p1', x & (x - 1))
        return self.do_synth('p1', spec, self.ops, desc='turn off rightmost bit')

    def test_p02(self):
        x = BitVec('x', self.width)
        spec = Func('p02', If(Or([x == (self.one << i) for i in range(self.width - 1)]), self.one, self.zero))
        return self.do_synth('p2', spec, self.ops, desc='unsigned est if power of 2')

    def test_p03(self):
        x = BitVec('x', self.width)
        spec = Func('p2', x & -x)
        return self.do_synth('p2', spec, self.ops, desc='isolate rightmost 1-bit')

    def test_p09(self):
        x = BitVec('x', self.width)
        spec = Func('p09', If(x < 0, -x, x))
        return self.do_synth('p09', spec, self.ops, desc='abs function')

    def test_p13(self):
        x = BitVec('x', self.width)
        m1 = BitVecVal(-1, self.width)
        p1 = BitVecVal(1, self.width)
        spec = Func('p13', If(x < 0, m1, If(x > 0, p1, 0)))
        return self.do_synth('p13', spec, self.ops, desc='sign function')

    def test_p14(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p14', Int2BV((BV2Int(x) + BV2Int(y)) / 2, self.width))
        return self.do_synth('p14', spec, self.ops, \
                             desc='floor of avg of two ints without overflow', max_const=1)

    def test_p15(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p15', Int2BV((BV2Int(x) + BV2Int(y) - 1) / 2 + 1, self.width))
        ops = [ self.bv.or_, self.bv.xor_, self.bv.sub_, self.bv.lshr_ ]
        return self.do_synth('p15', spec, ops, \
                             desc='ceil of avg of two ints without overflow', max_const=1)
    def test_p16(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p16', If(x < y, x, y))
        ops = [ self.bv.or_, self.bv.xor_, self.bv.sub_, self.bv.lshr_ ]
        return self.do_synth('p16', spec, ops, \
                             desc='max of two ints', max_const=0)
    def test_p17(self):
        x, y = BitVecs('x y', self.width)
        spec = Func('p17', (((x - 1) | x) + 1) & x)
        return self.do_synth('p17', spec, self.ops, \
                             desc='turn off the rightmost string of 1-bits', \
                             max_const=2)

    def test_p18(self):
        one = BitVecVal(1, self.width)
        zero = BitVecVal(0, self.width)
        x = BitVec('x', self.width)
        spec = Func('p18', If(Or([x == (one << i) for i in range(self.width)]), one, zero))
        return self.do_synth('p18', spec, self.ops, \
                             desc='check if power of 2')


    def test_p23(self):
        def create_spec(x):
            res = BitVecVal(0, 8)
            for i in range(self.width):
                res = ZeroExt(7, Extract(i, i, x)) + res
            return res

        x = BitVec('x', self.width)
        spec = Func('p23', create_spec(x))
        ops = [ self.bv.add_, self.bv.sub_, self.bv.and_, self.bv.lshr_ ]
        return self.do_synth('p23', spec, ops, \
                             desc='population count', \
                             max_const=7)

if __name__ == '__main__':
    args = parse_standard_args()
    t = BvBench(8, args)
    t.run()