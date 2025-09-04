from dataclasses import dataclass
from z3 import *

from synth.oplib import Bl
from bench.util import RulerBenchSet

@dataclass
class Ruler_bool(RulerBenchSet):
    a, b, c = Bools('a b c')
    all_ops = Bl.ops

    op_dict = {
        "&": (Bl.and2, And),
        "|": (Bl.or2,  Or),
        "^": (Bl.xor2, Xor),
        "~": (Bl.not1, Not),
    }

    def test_bool_3v_2i(self):
        yield from self.create_benchs("bench/rulesets/ruler/bool-3vars-2iters.json")

    def test_bool_3v_3i(self):
        yield from self.create_benchs("bench/rulesets/ruler/bool-3vars-3iters.json")