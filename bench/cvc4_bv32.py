#! /usr/bin/env python3

import json

from dataclasses import dataclass
from z3 import *

from synth.oplib import Bv
from bench.util import RulerBenchSet

@dataclass
class Cvc4_bv32(RulerBenchSet):
    bv = Bv(32)
    a, b, c = BitVecs('a b c', 32)
    all_ops = bv.ops
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
    precond_dict = {
        "<<": lambda _, y: ULE(y, 32),
        ">>": lambda _, y: ULE(y, 32),
    }

    def test_bv32_3v_2i(self):
        yield from self.create_benchs("bench/rulesets/cvc4/bv32-3vars-2iters.json")

    def test_bv32_3v_3i(self):
        yield from self.create_benchs("bench/rulesets/cvc4/bv32-3vars-3iters.json")