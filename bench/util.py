from typing import Dict, Optional, Iterable
from dataclasses import dataclass
from contextlib import contextmanager
from collections import Counter

from synth.spec import Spec, Func
from synth.oplib import Bv
from z3 import *

import json
import tinysexpr

@contextmanager
def timeout(duration: Optional[int]):
    import signal
    def timeout_handler(signum, frame):
        raise TimeoutError(f'timeout after {duration} seconds')
    if not duration is None:
        signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(duration)
    try:
        yield
    finally:
        if not duration is None:
            signal.alarm(0)

@dataclass(frozen=True)
class Bench:
    spec: Spec
    ops: Dict[Func, Optional[int]]
    all_ops: Optional[Iterable[Func]] = None
    consts: Optional[Dict[ExprRef, Optional[int]]] = None
    desc: Optional[str] = None
    theory: Optional[str] = None
    name: Optional[str]=None

    def get_name(self):
        return self.name if self.name is not None else self.spec.name

@dataclass
class BitVecBenchSet:
    bit_width: int = 8

    def __post_init__(self):
        self.width = self.bit_width
        self.bv    = Bv(self.bit_width)
        self.ops = [
            self.bv.add_, self.bv.sub_,
            self.bv.and_, self.bv.or_, self.bv.xor_, self.bv.neg_, self.bv.not_,
            self.bv.ashr_, self.bv.lshr_, self.bv.shl_,
            self.bv.ult_, self.bv.uge_, self.bv.slt_, self.bv.sge_,
        ]
        self.one = BitVecVal(1, self.width)
        self.zero = BitVecVal(0, self.width)

    def create_bench(self, name, spec, ops, consts=None, desc=''):
        if type(ops) == list or type(ops) == set:
            ops = { op: None for op in ops }
        yield Bench(spec, ops, self.ops, consts, desc, theory="QF_BV", name=name)

    def const(self, n):
        return BitVecVal(n, self.width)

    def popcount(self, x):
        res = BitVecVal(0, self.width)
        for i in range(self.width):
            res = ZeroExt(self.width - 1, Extract(i, i, x)) + res
        return res

    def nlz(self, x):
        w   = self.width
        res = BitVecVal(w, w)
        for i in range(w - 1):
            res = If(And([ Extract(i, i, x) == 1,
                     Extract(w - 1, i + 1, x) == BitVecVal(0, w - 1 - i) ]), w - 1 - i, res)
        return If(Extract(w - 1, w - 1, x) == 1, 0, res)

    def is_power_of_two(self, x):
        # return self.popcount(x) == 1
        # return And([x != 0, (x & (x - 1)) == 0]);
        res = []
        for i in range(self.width):
            res += [ BitVecVal(1 << i, self.width) == x ]
        return Or(res)

@dataclass
class SExprBenchSet:

    consts=None
    theory=None
    precond_dict={}

    def mk_var(self, name):
        return getattr(self, name)

    def to_bench(self, sexp_str):
        ops = { v[0]: 0 for v in self.op_dict.values() }
        def count_ops(sexp):
            match sexp:
                case [op, *args]:
                    res = Counter({ self.op_dict[op][0]: 1})
                    for a in args:
                        res.update(count_ops(a))
                    return res
                case _:
                    return Counter(ops)
        def sexpr_to_z3(sexp):
            match sexp:
                case [a] | str(a):
                    return self.mk_var(a[1:]) if a[0] == '?' else self.mk_const(a), BoolVal(True)
                case [op, *args]:
                    args, preconds = zip(*[ sexpr_to_z3(arg) for arg in args ])
                    if op in self.precond_dict:
                        preconds += (self.precond_dict[op](*args),)
                    _, ctor = self.op_dict[op]
                    return ctor(*args), simplify(And(preconds))
        sexp_str = sexp_str.strip()
        if sexp_str[0] != '(':
            sexp = sexp_str
        else:
            sexp = tinysexpr.read(io.StringIO(sexp_str), {})
        z3_exp, precond = sexpr_to_z3(sexp)
        func = Func(sexp_str, z3_exp, precond=precond)
        return Bench(func, count_ops(sexp), all_ops=self.all_ops, consts=self.consts, theory=self.theory)

@dataclass
class RulerBenchSet(SExprBenchSet):

    def create_benchs(self, filename):
        file = open(filename, "r")
        data = json.load(file)
        for eq in data["eqs"]:
            yield self.to_bench(eq["lhs"])
            if eq["bidirectional"]:
                yield self.to_bench(eq["rhs"])

@dataclass
class RulerBitVecBench(BitVecBenchSet, RulerBenchSet):

    def mk_var(self, name):
        return BitVec(name, self.width)

    def __post_init__(self):
        super().__post_init__()
        bv = self.bv
        self.all_ops = bv.ops

        self.op_dict = {
            "-":  (bv.neg_,  lambda x: -x),
            "~":  (bv.not_,  lambda x: ~x),
            "&":  (bv.and_,  lambda x, y: x & y),
            "|":  (bv.or_,   lambda x, y: x | y),
            "^":  (bv.xor_,  lambda x, y: x ^ y),
            "+":  (bv.add_,  lambda x, y: x + y),
            "--": (bv.sub_,  lambda x, y: x - y),
            "<<": (bv.shl_,  lambda x, y: x << y),
            ">>": (bv.ashr_, lambda x, y: x >> y),
            "*":  (bv.mul_,  lambda x, y: x * y),
        }

        self.precond_dict = {
            ">>": lambda _, y: And([0 <= y, y <= 4]),
            "<<": lambda _, y: And([0 <= y, y <= 4]),
        }
