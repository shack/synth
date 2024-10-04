import time

from contextlib import contextmanager
from dataclasses import dataclass, field

from z3 import BitVecSort

def eval_model(model, vars):
    return [ model.evaluate(v, model_completion=True) for v in vars ]

def bv_sort(max_value, ctx=None):
    return BitVecSort(len(bin(max_value)) - 2, ctx=ctx)

@contextmanager
def timer():
    start = time.perf_counter_ns()
    yield lambda: time.perf_counter_ns() - start

@dataclass
class Debug:
    level: int = 0

    def __call__(self, l, *args):
        if l <= self.level:
            print(*args)

def no_debug(level, *args):
    pass

@dataclass(frozen=True)
class HasDebug:
    debug: Debug = field(default_factory=Debug)
    """Verbosity level."""