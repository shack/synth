#! /usr/bin/env python3

import tinysexpr

from dataclasses import dataclass
from z3 import *

from synth.spec import Spec
from synth.oplib import R

from bench.util import Bench

@dataclass
class Herbie:
    a = Real('a')
    b = Real('b')
    c = Real('c')
    ans = Real('ans')
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
        "/": lambda x, y: x / y
    }
    def convert_z3(self, exp):
        if isinstance(exp, list) and len(exp) >= 2:
            args = [self.convert_z3(arg) for arg in exp[1:]]
            func = self.op_dict[str(exp[0])]
            return func(*args)
        else:
            if isinstance(exp, list):
                attr = exp[0]
            else:
                attr = str(exp)
            return getattr(self, attr[1:]) if attr[0] == '?' else RealVal(attr)

    def process(self, name, exp):
        z3_exp = self.convert_z3(exp)
        spec = Spec(name, self.ans == z3_exp, [self.ans], [self.a, self.b, self.c], precond=And(self.a != 0, self.b != 0, self.c != 0))
        return Bench(name, spec, self.ops, all_ops=R.ops, consts={0.0, 0.5, 1.0, 2.0})

    def test_herbie(self):
        file = open("bench/rulesets/ruler/herbie.txt", "r")
        rules = file.read().splitlines()[1:-1]
        benchs = []
        for rule in rules:
            if '<=>' in rule:
                print(rule)
                l, r = rule.split('<=>')
                bs = [ l, r ]
            else:
                assert '=>' in rule
                l, _ = rule.split("=>")
                bs = [ l ]
            for b in bs:
                b = b.strip()
                if b[0] != '(':
                    b = f'({b})'
                exp = tinysexpr.read(io.StringIO(b), {})
                benchs.append(self.process(b, exp))
        return benchs