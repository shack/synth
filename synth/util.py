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

@dataclass(frozen=True)
class Debug:
    level: int = 0

    def __call__(self, l, *args):
        if l <= self.level:
            print(*args)

def no_debug(level, *args):
    pass

@dataclass(frozen=True)
class HasDebug:
    debug: Debug = field(kw_only=True, default_factory=Debug)
    """Verbosity level."""

def find_start_interval(eval, is_lt, start=1, debug=no_debug):
    l, u = 0, start
    debug(1, f'obj bounds: [{l}, {u}]')
    while not is_lt(eval(u)):
        l, u = u, u * 2
        debug(1, f'obj bounds [{l}, {u}]')
    return l, u

def binary_search(eval, is_lt, l, r, debug=no_debug):
    results = {}
    while l != r:
        debug(1, f'obj bounds [{l}, {r}]')
        m = l + (r - l + 1) // 2
        res = eval(m)
        results[m] = res
        if is_lt(res):
            r = m - 1
        else:
            l = m
    return l, results
