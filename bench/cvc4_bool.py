#! /usr/bin/env python3

import json

from dataclasses import dataclass
from z3 import *

from synth.oplib import Bl

from bench.util import RulerBenchSet

@dataclass
class Cvc4_bool(RulerBenchSet):
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

    def test_bool_3v_2i(self):
        yield from self.create_benchs("bench/rulesets/cvc4/bool-3vars-2iters.json")

    def test_bool_3v_2i(self):
        yield from self.create_benchs("bench/rulesets/cvc4/bool-3vars-3iters.json")