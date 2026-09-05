"""Tests for spurious-program exclusion in synth.abstraction.AbstractLenCegis.

When an abstraction is too coarse, synthesising over the abstract specification
can yield a program whose concretisation does not satisfy the concrete
specification -- a *spurious* program. `AbstractLenCegis.synth_prgs` must then
exclude that program *semantically* (forcing the next candidate to compute a
different function) and keep searching until it finds a correct program.

`test_spurious_program_is_excluded_and_search_converges` builds a problem where
this necessarily happens: synthesise f(x) = 0 over a grammar that contains only
bit-vector addition and no constants, under a lower-2-bits abstraction. The
smallest abstract solution is 4*x -- its low two bits are zero, so it satisfies
the abstract spec -- but 4*x != 0 concretely and there is no constant to repair
it, so it is spurious. Only 16*x (== 0 mod 16) is correct. Without semantic
exclusion the search would re-propose 4*x forever; with it the search converges.

Run as a script:

    python test/test_abstraction_spurious.py
"""
import os
import signal
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from z3 import *
from synth.spec import synth_func_from_ops, Problem, Constraint
from synth.oplib import Bv
from synth.abstraction import AbstractLenCegis
from synth.abstraction.bv import LowerBitsAbstraction


WIDTH = 4


class _CaptureDebug:
    """Duck-typed `Debug` that records messages on the 'abs' channel."""

    def __init__(self):
        self.messages = []

    def has(self, tag):
        return str(tag) == 'abs'

    def __call__(self, tag, *args):
        if self.has(tag):
            self.messages.append(' '.join(str(a) for a in args))


def _with_timeout(seconds, fn):
    """Run `fn` but fail loudly instead of hanging.

    Missing semantic exclusion turns the synthesis loop into an infinite
    re-proposal of the same spurious program, so we bound it and report a
    timeout as a test failure."""
    if not hasattr(signal, 'SIGALRM'):
        return fn()

    def handler(signum, frame):
        raise AssertionError(
            f"synthesis did not finish within {seconds}s "
            "(possible infinite loop -- spurious exclusion regressed?)")

    old = signal.signal(signal.SIGALRM, handler)
    signal.alarm(seconds)
    try:
        return fn()
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)


def _f_equals_zero_problem():
    x, r = BitVecs('x r', WIDTH)
    # grammar: bit-vector addition only, no constants
    func = synth_func_from_ops([x.sort()], [r.sort()], [Bv(WIDTH).add_], const_map={})
    # specification: f(x) = 0 for every x
    spec = Constraint(phi=(r == BitVecVal(0, WIDTH)), params=[x],
                      function_applications={('f', (x,)): (r,)})
    return Problem(constraints=[spec], funcs={'f': func}), x, r


def _is_zero_function(prg, x, r):
    """True iff `prg` computes f(x) = 0 for every x."""
    s = Solver()
    for c in prg.eval_clauses([x], [r]):
        s.add(c)
    s.add(r != 0)
    return s.check() == unsat


def test_spurious_program_is_excluded_and_search_converges():
    problem, x, r = _f_equals_zero_problem()
    debug = _CaptureDebug()
    sy = AbstractLenCegis(abstractions=[LowerBitsAbstraction(bit_width=2)],
                          size_range=(0, 5), debug=debug)

    prgs, _ = _with_timeout(60, lambda: sy.synth_prgs(problem))

    # the abstraction necessarily yields a spurious candidate (4*x) first ...
    spurious = [m for m in debug.messages if 'spurious' in m]
    assert spurious, "expected at least one spurious program to be excluded"

    # ... yet the search must still converge on a concrete-correct program
    assert prgs is not None, "no program found although a correct one exists"
    assert _is_zero_function(prgs['f'], x, r), \
        f"returned program does not compute f(x)=0: {prgs['f']}"


def test_identity_abstraction_produces_no_spurious_programs():
    # With no abstraction (only the identity fallback) the concretisation always
    # equals the abstraction, so no candidate is ever spurious; the problem is
    # solved directly. This is the contrast to the test above.
    problem, x, r = _f_equals_zero_problem()
    debug = _CaptureDebug()
    sy = AbstractLenCegis(abstractions=[], size_range=(0, 5), debug=debug)

    prgs, _ = _with_timeout(60, lambda: sy.synth_prgs(problem))

    assert not [m for m in debug.messages if 'spurious' in m], \
        "identity abstraction should never produce a spurious program"
    assert prgs is not None, "no program found although a correct one exists"
    assert _is_zero_function(prgs['f'], x, r), \
        f"returned program does not compute f(x)=0: {prgs['f']}"


TESTS = [v for k, v in sorted(globals().items()) if k.startswith('test_')]


def main():
    failed = 0
    for t in TESTS:
        name = t.__name__
        try:
            t()
            print(f"[ok]   {name}")
        except AssertionError as e:
            failed += 1
            print(f"[FAIL] {name}: {e}")
    if failed:
        sys.exit(f"\n{failed}/{len(TESTS)} tests failed")
    print(f"\nAll {len(TESTS)} tests passed.")


if __name__ == '__main__':
    main()
