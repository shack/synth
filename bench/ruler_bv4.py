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
class Ruler_bv4(RulerBenchSet):
    bv = Bv(4)
    a = BitVec('a', 4)
    b = BitVec('b', 4)
    c = BitVec('c', 4)
    ans = BitVec('ans', 4)
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

    def test_bv4_3v_2i(self):
        file = open("rulesets/ruler/bv4-3vars-2iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        yield from self.create_benchs(eqs)

    def test_bv4_3v_3i(self):
        file = open("rulesets/ruler/bv4-3vars-3iters.json", "r")
        data = json.load(file)
        eqs = data["eqs"]
        yield from self.create_benchs(eqs)