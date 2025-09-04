from dataclasses import dataclass
from z3 import *

from synth.oplib import R

from bench.util import SExprBenchSet

@dataclass
class Herbie(SExprBenchSet):
    a = Real('a')
    b = Real('b')
    c = Real('c')

    all_ops = R.ops
    consts = {0.0, 0.5, 1.0, 2.0}

    op_dict = {
        "~":    (R.neg,  lambda x: -x),
        "+":    (R.fabs, lambda x, y: x + y),
        "-":    (R.sub,  lambda x, y: x - y),
        "fabs": (R.fabs, lambda x: If(x >= 0, x, -x)),
        "*":    (R.mul,  lambda x, y: x * y),
        "/":    (R.div,  lambda x, y: x / y),
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