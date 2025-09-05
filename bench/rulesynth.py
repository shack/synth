from dataclasses import dataclass
from pathlib import Path
from z3 import *

from synth.oplib import Bl
from synth.oplib import R

from bench.util import SExprBenchSet, RulerBenchSet, RulerBitVecBench

class RulerBool(RulerBenchSet):
    a, b, c = Bools('a b c')
    all_ops = Bl.ops
    theory = 'QF_FD'
    op_dict = {
        "&": (Bl.and2, And),
        "|": (Bl.or2,  Or),
        "^": (Bl.xor2, Xor),
        "~": (Bl.not1, Not),
    }
    precond_dict = {}

    def mk_const(self, s):
        return BoolVal(s)

class RulerBitVec(RulerBitVecBench):
    pass

@dataclass
class Herbie(SExprBenchSet):
    file: Path
    """Herbie benchmark set file."""

    a = Real('a')
    b = Real('b')
    c = Real('c')

    all_ops = R.ops
    consts = {0.0, 0.5, 1.0, 2.0}

    op_dict = {
        "~":    (R.neg,  lambda x: -x),
        "+":    (R.fabs, lambda x, y: x + y),
        "-":    (R.sub,  lambda x, y: x - y),
        "fabs": (R.fabs, lambda x: If(x >= 0, x, -x)),
        "*":    (R.mul,  lambda x, y: x * y),
        "/":    (R.div,  lambda x, y: x / y),
    }

    precond_dict = {
        "/": lambda x, y: y != 0,
    }

    def mk_const(self, s):
        return RealVal(s)

    def test_all(self):
        file = open(self.file, "r")
        rules = file.read().splitlines()[1:-1]
        for rule in rules:
            if '<=>' in rule:
                l, r = rule.split('<=>')
                yield self.to_bench(l)
                yield self.to_bench(r)
            else:
                assert '=>' in rule
                l, _ = rule.split("=>")
                yield self.to_bench(l)
