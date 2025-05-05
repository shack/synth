#! /usr/bin/env python3

import random
import itertools
import functools
import json
import sexpdata

from dataclasses import dataclass
from z3 import *

from synth.spec import Func, Spec, create_bool_func
from synth.oplib import Bl, Bv, Fp
from synth.util import bv_sort

from bench.util import Bench

@dataclass
class Herbie:
    a = Real('a')
    b = Real('b')
    c = Real('c')
    ans = Real('ans')
    ops = {Fp.neg: None,
           Fp.add: None,
           Fp.sub: None,
           Fp.fabs: None,
           Fp.mul: None,
           Fp.div: None}
    op_dict = {
        "~": lambda x: -x,
        "+": lambda x, y: x + y,
        "-": lambda x, y: x - y,
        "fabs": lambda x: If(x >= 0, x, -x),
        "*": lambda x, y: x * y,
        "/": lambda x, y: x / y
    }
    def convert_z3(self, exp):
        if isinstance(exp, list):
            args = [self.convert_z3(arg) for arg in exp[1:]]
            func = self.op_dict[str(exp[0])]
            return func(*args)
        else:
            attr = str(exp)
            if attr[0] == "?":
                return getattr(self, attr[1:])
            else:
                return RealVal(attr)

    def process(self, name, exp):
        z3_exp = self.convert_z3(exp)
        spec = Spec(name, self.ans == z3_exp, [self.ans], [self.a, self.b, self.c], precond=And(self.a != 0, self.b != 0, self.c != 0))
        print(spec)
        return Bench(name, spec, self.ops, all_ops=Fp.ops, consts={0.0, 0.5, 1.0, 2.0})

    def test_herbie(self):
        file = open("bench/rulesets/ruler/herbie.txt", "r")
        rules = file.read().splitlines()[1:-1]
        benchs = []
        for rule in rules:
            if len(rule.split("<=>")) == 2:
                lhs_str = rule.split("<=>")[0]
                rhs_str = rule.split("<=>")[1]
                lhs_exp = sexpdata.loads(lhs_str)
                rhs_exp = sexpdata.loads(rhs_str)

                benchs.append(self.process(lhs_str, lhs_exp))
                benchs.append(self.process(rhs_str, rhs_exp))
            else:
                lhs_str = rule.split("=>")[0]
                rhs_str = rule.split("=>")[1]
                lhs_exp = sexpdata.loads(lhs_str)
                rhs_exp = sexpdata.loads(rhs_str)

                benchs.append(self.process(lhs_str, lhs_exp))

        return benchs