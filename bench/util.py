from typing import Dict, Optional, Iterable
from dataclasses import dataclass
from contextlib import contextmanager

from synth.spec import Spec, Func
from synth.oplib import Bv
from z3 import *

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
    name: str
    spec: Spec
    ops: Dict[Func, Optional[int]]
    all_ops: Optional[Iterable[Func]] = None
    consts: Optional[Dict[ExprRef, Optional[int]]] = None
    desc: Optional[str] = None
    theory: Optional[str] = None

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
        return Bench(name, spec, ops, self.ops, consts, desc, theory="QF_BV")

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
        return self.popcount(x) == 1
