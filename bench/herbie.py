#! /usr/bin/env python3

import tinysexpr

from dataclasses import dataclass
from z3 import *

from synth.oplib import R

from bench.util import Bench, SExprBenchSet

@dataclass
class Herbie(SExprBenchSet):
    a = Real('a')
    b = Real('b')
    c = Real('c')

    all_ops = R.ops
    consts = {0.0, 0.5, 1.0, 2.0}
    ops = {R.neg: None,
           R.add: None,
           R.sub: None,
           R.fabs: None,
           R.mul: None,
           R.div: None}

    op_dict = {
        "~": lambda x: -x,
        "+": lambda x, y: x + y,
        "-": lambda x, y: x - y,
        "fabs": lambda x: If(x >= 0, x, -x),
        "*": lambda x, y: x * y,
        "/": lambda x, y: x / y,
    }

    precond_dict = {
        "/": lambda x, y: y != 0,
    }

    def mk_const(self, s):
        return RealVal(s)

    def test_herbie(self):
        file = open("bench/rulesets/ruler/herbie.txt", "r")
        rules = file.read().splitlines()[1:-1]
        benchs = []
        for rule in rules:
            if '<=>' in rule:
                l, r = rule.split('<=>')
                yield self.to_bench(l)
                yield self.to_bench(r)
            else:
                assert '=>' in rule
                l, _ = rule.split("=>")
                yield self.to_bench(l)