import time
import re
import collections.abc

from contextlib import contextmanager
from dataclasses import dataclass, field

from z3 import BitVecSort

def eval_model(model, vars):
    return [ model.evaluate(v, model_completion=True) for v in vars ]

def bv_width(max_value):
    # return int(log2(max_value)) + 1
    return len(bin(max_value)) - 2

def bv_sort(max_value):
    return BitVecSort(bv_width(max_value))

@contextmanager
def timer():
    start = time.perf_counter_ns()
    yield lambda: time.perf_counter_ns() - start

@dataclass(frozen=True)
class Debug:
    what: str = field(kw_only=True, default='')

    def __call__(self, tag, *args):
        if self.what and re.match(self.what, str(tag)):
            print(*args)

def no_debug(tag, *args):
    pass

class IgnoreList(collections.abc.MutableSequence):
    def __init__(self, *args):
        pass

    def __len__(self):
        return 0

    def __getitem__(self, i):
        raise IndexError()

    def __setitem__(self, i, v):
        pass

    def __delitem__(self, i):
        pass

    def insert(self, i, v):
        pass

@dataclass(frozen=True)
class HasDebug:
    debug: Debug = field(kw_only=True, default_factory=Debug)
    """Verbosity level."""

def find_start_interval(eval, is_lt, start=1, debug=no_debug):
    l, u = 0, start
    debug('opt', f'opt bounds: [{l}, {u}]')
    while not is_lt(eval(u)):
        l, u = u, u * 2
        debug('opt', f'opt bounds [{l}, {u}]')
    return l, u

def binary_search(eval, is_lt, l, r, debug=no_debug):
    results = {}
    while l != r:
        debug('opt', f'obj bounds [{l}, {r}]')
        m = l + (r - l + 1) // 2
        res = eval(m)
        results[m] = res
        if is_lt(res):
            r = m - 1
        else:
            l = m
    return l, results
