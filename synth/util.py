import time
import re
import math
import collections.abc

from contextlib import contextmanager
from dataclasses import dataclass, field

from z3 import *

def eval_model(model, vars):
    return [ model.evaluate(v, model_completion=True) for v in vars ]

def bv_width(max_value):
    return int(math.log2(max(max_value, 1))) + 1

def bv_sort(max_value):
    return BitVecSort(bv_width(max_value))

def is_val(x):
    return is_const(x) and x.decl().kind() != Z3_OP_UNINTERPRETED

def free_vars(expr):
    """Return a list of free (unbound) uninterpreted constants in the Z3 AST `expr`."""
    res = set()
    seen = set()

    def walk(e, bound_names):
        if e in seen:
            return
        seen.add(e)

        if is_quantifier(e):
            n = e.num_vars()
            names = { e.var_name(i) for i in range(n) }
            walk(e.body(), bound_names | names)
            return

        # uninterpreted constants (identifiers)
        if len(e.children()) == 0 and e.decl().kind() == Z3_OP_UNINTERPRETED:
            name = e.decl().name() or str(e)
            if name not in bound_names:
                res.add(e)
            return

        for c in e.children():
            walk(c, bound_names)

    walk(expr, set())
    return res

_NE0_OPS = frozenset({
    Z3_OP_BSDIV,
    Z3_OP_BUDIV,
    Z3_OP_BSREM,
    Z3_OP_BUREM,
    Z3_OP_DIV,
    Z3_OP_MOD,
})

def analyze_precond(e: ExprRef):
    children = e.children()
    res = [ p for c in children for p in analyze_precond(c) ]
    k = e.decl().kind()
    if k in _NE0_OPS:
        res += [ children[1] != 0 ]
    return res

@contextmanager
def timer():
    start = time.perf_counter_ns()
    yield lambda: time.perf_counter_ns() - start

@dataclass(frozen=True)
class Debug:
    what: str = field(kw_only=True, default='')

    def has(self, tag):
        return self.what and re.match(self.what, str(tag)) is not None

    def __call__(self, tag, *args):
        if self.has(tag):
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
