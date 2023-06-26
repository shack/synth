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
            self.bv.shl_
        ]

    def test_p1(self):
        x = BitVec('x', self.width)
        spec = synth.to_op('p1', x & (x - 1))
        return self.do_synth('p1', [ spec ], self.ops, desc='turn off rightmost bit')

    def test_p2(self):
        x = BitVec('x', self.width)
        spec = synth.to_op('p2', x & (x + 1))
        return self.do_synth('p2', [ spec ], self.ops, desc='test if power of 2')

    def test_p13(self):
        x = BitVec('x', self.width)
        m1 = BitVecVal(-1, self.width)
        p1 = BitVecVal(1, self.width)
        ops = [ self.bv.or_, self.bv.ashr_, self.bv.lshr_, self.bv.neg_, ]
        spec = synth.to_op('p13', If(x < 0, m1, If(x > 0, p1, 0)))
        return self.do_synth('p13', [ spec ], ops, desc='sign function')

if __name__ == '__main__':
    args = synth.parse_standard_args()
    t = BvBench(32, args)
    t.run()