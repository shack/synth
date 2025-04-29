#! /usr/bin/env python3

import random
import itertools
import functools
import json
import tinysexpr

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
        
    def process(self, name, exp):
        z3_exp = self.convert_z3(exp)
        spec = Spec(name, self.ans == z3_exp, [self.ans], [self.a, self.b, self.c])
        return Bench(name, spec, self.ops, all_ops=Bl.ops, consts = {True, False}, theory='QF_BV')
    
    def create_benchs(self, eqs):
        benchs = []
        for eq in eqs:
            lhs_str = eq["lhs"]
            if lhs_str[0] != '(':
                lhs_str = '(' + lhs_str + ')'
            lhs = tinysexpr.read(io.StringIO(lhs_str),{})
            benchs.append(self.process(eq["lhs"], lhs))
            if eq["bidirectional"] == True:
                rhs_str = eq["rhs"]
                if rhs_str[0] != '(':
                    rhs_str = '(' + rhs_str + ')'
                rhs = tinysexpr.read(io.StringIO(rhs_str),{})
                benchs.append(self.process(eq["rhs"], rhs))
        return benchs
        
    def test_bool_3v_2i(self):
        file = open("rulesets/ruler/bool-3vars-2iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        return self.create_benchs(eqs)
    
    def test_bool_3v_3i(self):
        file = open("rulesets/ruler/bool-3vars-3iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        return self.create_benchs(eqs)