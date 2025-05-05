#! /usr/bin/env python3

import json

from dataclasses import dataclass
from z3 import *

from synth.oplib import Bl

from bench.util import SExprBenchSet, Bench

@dataclass
class Cvc4_bool(SExprBenchSet):
    a, b, c = Bools('a b c')
    ops = { Bl.xor2: None, Bl.and2: None, Bl.or2: None, Bl.not1: None}
    all_ops = Bl.ops
    theory = 'QF_BV'
    op_dict = {
        "&": And,
        "|": Or,
        "^": Xor,
        "~": Not,
    }
    precond_dict = {}

    def mk_const(self, s):
        return BoolVal(s)

    def convert_z3(self, exp):
        if isinstance(exp, list) and len(exp) >= 2:
            args = [self.convert_z3(arg) for arg in exp[1:]]
            func = self.op_dict[str(exp[0])]
            return func(*args)
        else:
            if isinstance(exp, list):
                attr = exp[0]
            else:
                attr = exp
            return getattr(self, attr[1:])

    def create_benchs(self, eqs):
        benchs = []
        for eq in eqs:
            benchs.append(self.to_bench(eq["lhs"]))
            if eq["bidirectional"] == True:
                benchs.append(self.to_bench(eq["rhs"]))
        return benchs

    def test_bool_3v_2i(self):
        file = open("bench/rulesets/cvc4/bool-3vars-2iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        return self.create_benchs(eqs)

    def test_bool_3v_3i(self):
        file = open("bench/rulesets/cvc4/bool-3vars-3iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        return self.create_benchs(eqs)