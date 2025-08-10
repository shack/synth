#! /usr/bin/env python3

from dataclasses import dataclass
from z3 import *

from bench.util import RulerBitVecBench

@dataclass
class Cvc4_bv(RulerBitVecBench):

    def test_bv4_3v_2i(self):
        yield from self.create_benchs("bench/rulesets/cvc4/bv4-3vars-2iters.json")

    def test_bv4_3v_3i(self):
        yield from self.create_benchs("bench/rulesets/cvc4/bv4-3vars-3iters.json")