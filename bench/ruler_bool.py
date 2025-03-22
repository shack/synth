#! /usr/bin/env python3

import random
import itertools
import functools
import json
import sexpdata

from dataclasses import dataclass
from z3 import *

from synth.spec import Func, Spec, create_bool_func
from synth.oplib import Bl, Bv
from synth.util import bv_sort

from bench.util import Bench

@dataclass
class Ruler_bool:
    a, b, c, ans = Bools('a b c ans')
    ops = { Bl.xor2: None, Bl.and2: None, Bl.or2: None, Bl.not1: None}
    op_dict = {
        "&": And,
        "|": Or,
        "^": Xor,
        "~": Not,
    }
   
    def convert_z3(self, exp):
        if isinstance(exp, list):
            args = [self.convert_z3(arg) for arg in exp[1:]]
            func = self.op_dict[str(exp[0])]
            return func(*args)
        else:
            if isinstance(exp, sexpdata.Symbol):
                attr = str(exp)
            else:
                attr = exp
            return getattr(self, attr[1:])
        
    def process(self, name, exp):
        z3_exp = self.convert_z3(exp)
        spec = Spec(name, self.ans == z3_exp, [self.ans], [self.a, self.b, self.c])
        return Bench(name, spec, self.ops, all_ops=Bl.ops, consts = {True, False}, theory='QF_BV')
        
    def test_bool_3v_2i(self):
        file = open("rulesets/ruler/bool-3vars-2iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        benchs = []
        for eq in eqs:
            lhs = sexpdata.loads(eq["lhs"])
            benchs.append(self.process(eq["lhs"], lhs))
            if eq["bidirectional"] == True:
                rhs = sexpdata.loads(eq["rhs"])
                benchs.append(self.process(eq["rhs"], rhs))
        return benchs
    
    def test_bool_3v_3i(self):
        file = open("rulesets/ruler/bool-3vars-3iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        benchs = []
        for eq in eqs:
            lhs = sexpdata.loads(eq["lhs"])
            benchs.append(self.process(eq["lhs"], lhs))
            if eq["bidirectional"] == True:
                rhs = sexpdata.loads(eq["rhs"])
                benchs.append(self.process(eq["rhs"], rhs))
        return benchs