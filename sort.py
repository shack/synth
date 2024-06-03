#! /usr/bin/env python3

from z3 import *
from cegis import *
from util import bv_sort
from test import TestBase, parse_standard_args

class SortBench(TestBase):
    def __init__(self, length, args):
        super().__init__(**vars(args))
        self.n = length

    def test_sort(self):
        n = self.n
        s = bv_sort(n)
        x, y = Consts('x y', s)
        p = Bool('p')
        cmp  = Func('cmplt', ULT(x, y))
        cmov = Func('ite', If(p, x, y))
        ins  = [ Const(f'i{i}', s) for i in range(n) ]
        outs = [ Const(f'o{i}', s) for i in range(n) ]
        pre  = [ Distinct(*ins) ] \
             + [ ULE(0, i) for i in ins ] \
             + [ ULT(i, n) for i in ins ]
        pre  = And(pre)
        phi  = And([ o == i for i, o in enumerate(outs) ])
        spec = Spec('sort', phi, outs, ins, pre)
        return self.do_synth('sort', spec, [cmp, cmov], max_const=0)

if __name__ == '__main__':
    import argparse
    synth_args, rest = parse_standard_args()
    parser = argparse.ArgumentParser(prog="sort")
    parser.add_argument('-n', '--length', type=int, default=3, \
                        help='Number of elements to sort')
    args = parser.parse_args(rest)
    t = SortBench(args.length, synth_args)
    t.run()