#! /usr/bin/env python3

from dataclasses import dataclass
from z3 import *

from synth.oplib import Bl
from bench.util import RulerBenchSet

@dataclass
class Ruler_bool(RulerBenchSet):
    a, b, c = Bools('a b c')
    ops = { Bl.xor2: None, Bl.and2: None, Bl.or2: None, Bl.not1: None}
    all_ops = Bl.ops

    op_dict = {
        "&": And,
        "|": Or,
        "^": Xor,
        "~": Not,
    }

    def test_bool_3v_2i(self):
        yield from self.create_benchs("bench/rulesets/ruler/bool-3vars-2iters.json")

    def test_bool_3v_3i(self):
        yield from self.create_benchs("bench/rulesets/ruler/bool-3vars-3iters.json")