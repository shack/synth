#! /usr/bin/env python3

from z3 import *

import synth

class BvBench(synth.TestBase):
    def __init__(self, width, args):
        super().__init__(**vars(args))
        self.width = width
        self.bv    = synth.Bv(width)
        op_list = 'add,sub,and,or,xor,neg,not,ashr,lshr,shl'
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

    def test_p01(self):
        x = BitVec('x', self.width)
        spec = synth.to_op('p1', x & (x - 1))
        return self.do_synth('p1', [ spec ], self.ops, desc='turn off rightmost bit')

    def test_p02(self):
        x = BitVec('x', self.width)
        spec = synth.to_op('p2', x & (x + 1))
        return self.do_synth('p2', [ spec ], self.ops, desc='test if power of 2')

    def test_p03(self):
        x = BitVec('x', self.width)
        spec = synth.to_op('p2', x & -x)
        return self.do_synth('p2', [ spec ], self.ops, desc='isolate rightmost 1-bit')

    def test_p13(self):
        x = BitVec('x', self.width)
        m1 = BitVecVal(-1, self.width)
        p1 = BitVecVal(1, self.width)
        spec = synth.to_op('p13', If(x < 0, m1, If(x > 0, p1, 0)))
        # ops = [ self.bv.ashr_, self.bv.lshr_, self.bv.or_, self.bv.neg_ ]
        return self.do_synth('p13', [ spec ], self.ops, desc='sign function')

    def test_p14(self):
        x, y = BitVecs('x y', self.width)
        spec = synth.to_op('p14', Int2BV((BV2Int(x) + BV2Int(y)) / 2, self.width))
        # ops = [ self.bv.add_, self.bv.sub_, self.bv.ashr_, self.bv.lshr_, self.bv.and_, self.bv.or_, self.bv.xor_]
        return self.do_synth('p14', [ spec ], self.ops, \
                             desc='floor of avg of two ints without overflow', max_const=1)

    def test_p16(self):
        x, y = BitVecs('x y', self.width)
        spec = synth.to_op('p16', If(x < y, x, y))
        return self.do_synth('p16', [ spec ], self.ops, \
                             desc='max of two ints', max_const=0)
    def test_p17(self):
        x, y = BitVecs('x y', self.width)
        spec = synth.to_op('p17', (((x - 1) | x) + 1) & x)
        return self.do_synth('p17', [ spec ], self.ops, \
                             desc='Turn-off the rightmost contiguous string of 1-bits', \
                            max_const=2)


if __name__ == '__main__':
    args = synth.parse_standard_args()
    t = BvBench(8, args)
    t.run()