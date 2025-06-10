#! /usr/bin/env python3

import random
import itertools
import functools
import json
import tinysexpr

from dataclasses import dataclass
from z3 import *

from synth.oplib import Bv

from bench.util import RulerBenchSet

@dataclass
class Ruler_bv(RulerBenchSet):

    def test_bv4_3v_2i(self):
        yield from self.create_benchs("bench/rulesets/ruler/bv4-3vars-2iters.json")

    def test_bv4_3v_3i(self):
        yield from self.create_benchs("bench/rulesets/ruler/bv4-3vars-3iters.json")