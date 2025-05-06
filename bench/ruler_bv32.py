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
class Ruler_bv32(RulerBenchSet):
    bv = Bv(32)
    a = BitVec('a', 32)
    b = BitVec('b', 32)
    c = BitVec('c', 32)
    ans = BitVec('ans', 32)
    ops = {bv.neg_: None,
           bv.not_: None,
           bv.and_: None,
           bv.or_: None,
           bv.xor_: None,
           bv.add_: None,
           bv.sub_: None,
           bv.shl_: None,
           bv.ashr_: None,
           bv.mul_: None}
    op_dict = {
        "-": lambda x: -x,
        "~": lambda x: ~x,
        "&": lambda x, y: x & y,
        "|": lambda x, y: x | y,
        "^": lambda x, y: x ^ y,
        "+": lambda x, y: x + y,
        "--": lambda x, y: x - y,
        "<<": lambda x, y: x << y,
        ">>": lambda x, y: x >> y,
        "*": lambda x, y: x * y,
    }

    def test_bv32_3v_2i(self):
        file = open("rulesets/ruler/bv32-3vars-2iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        yield from self.create_benchs(eqs)

    def test_bv32_3v_3i(self):
        file = open("rulesets/ruler/bv32-3vars-3iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        yield from self.create_benchs(eqs)