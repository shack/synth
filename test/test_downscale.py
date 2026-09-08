"""End-to-end tests for bit-vector downscaling (synth.transform.driver.Downscale)
and the shared constant re-synthesis (synth.const_synth).

`Downscale` rewrites a problem to a smaller bit width, synthesizes there,
lifts the programs found back to the original productions and re-synthesizes
their constants at full width; a lifted program without suitable constants is
spurious, and if no width yields a program the base synthesizer runs on the
original problem.

Run as a script:

    python test/test_downscale.py
"""
import os
import signal
import sys
from dataclasses import replace
from io import StringIO

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from z3 import *

from synth.const_synth import solve_constants
from synth.oplib import Bv
from synth.spec import Constraint, Problem, Prg, synth_func_from_ops
from synth.synth_n import LenCegis
from synth.transform.driver import Downscale
from util.check import check
from util.sygus import SyGuS, parse_solution, read_problem

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class _CaptureDebug:
    """Duck-typed `Debug` that records messages on the 'downscale' channel."""

    def __init__(self):
        self.messages = []

    def has(self, tag):
        return str(tag) == 'downscale'

    def __call__(self, tag, *args):
        if self.has(tag):
            self.messages.append(' '.join(str(a) for a in args))


def _with_timeout(seconds, fn):
    if not hasattr(signal, 'SIGALRM'):
        return fn()

    def handler(signum, frame):
        raise AssertionError(f'synthesis did not finish within {seconds}s')

    old = signal.signal(signal.SIGALRM, handler)
    signal.alarm(seconds)
    try:
        return fn()
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old)


def _verifies(problem, prgs):
    return prgs is not None and all(c.verify(prgs)[0] is None for c in problem.constraints)


def _downscale(problem, widths, debug=None, size_range=(0, 3)):
    debug = debug or _CaptureDebug()
    sy = Downscale(target_widths=widths, base=LenCegis(size_range=size_range), debug=debug)
    prgs, stats = _with_timeout(120, lambda: sy.synth_prgs(problem))
    return prgs, stats, debug


def _single_func_problem(width, ops, phi_fn, const_map=None):
    x, r = BitVecs('x r', width)
    func = synth_func_from_ops([x.sort()], [r.sort()], ops, const_map=const_map)
    spec = Constraint(phi=phi_fn(x, r), params=[x],
                      function_applications={ ('f', (x,)): (r,) })
    return Problem(constraints=[spec], funcs={ 'f': func })


def _constant_operands(prg):
    return [ v for _, args in prg.insns for is_c, v in args if is_c ] + \
           [ v for is_c, v in prg.outputs if is_c ]


# --- Downscale -------------------------------------------------------------

def test_constant_is_resynthesized_at_full_width():
    # f(x) = x + 0x7F: the 4-bit program is add(x, 15); neither the zero- nor
    # the sign-extension of 15 is right at 8 bits, the constant must be found
    problem = _single_func_problem(8, [ Bv(8).add_, Bv(8).and_ ],
                                   lambda x, r: r == x + BitVecVal(0x7F, 8))
    prgs, stats, debug = _downscale(problem, [ 4 ])
    assert _verifies(problem, prgs), prgs
    assert stats['fallback'] is False
    assert len(stats['iterations']) == 1
    assert stats['iterations'][0]['transform'] == 'downscale(4)'
    assert any(m.startswith('(success') for m in debug.messages), debug.messages
    consts = _constant_operands(prgs['f'])
    assert len(consts) == 1 and consts[0].sort().eq(BitVecSort(8)) and consts[0].as_long() == 0x7F


def test_spurious_candidate_then_fallback():
    # f(x) = x >> 4 (logical): at 4 bits the specification collapses to r == 0,
    # so the shortest 4-bit program is the constant output, which no constant
    # can repair at 8 bits
    problem = _single_func_problem(8, [ Bv(8).lshr_, Bv(8).and_ ],
                                   lambda x, r: r == LShR(x, BitVecVal(4, 8)))
    prgs, stats, debug = _downscale(problem, [ 4 ])
    assert _verifies(problem, prgs), prgs
    assert stats['fallback'] is True
    it, = stats['iterations']
    assert it['spurious'] >= 1
    assert all(not c['success'] for c in it['candidates'])
    assert any(m.startswith('(spurious') for m in debug.messages), debug.messages
    assert any(m.startswith('(fallback') for m in debug.messages), debug.messages


def test_multiple_functions_use_separate_constant_variables():
    # f(x) = x + 0x7F and g(x) = x + 0x3F have the same shape at 4 bits; the
    # constants must be re-synthesized independently
    x, r1, r2 = BitVecs('x r1 r2', 8)
    func = synth_func_from_ops([x.sort()], [x.sort()], [ Bv(8).add_ ])
    spec = Constraint(phi=And(r1 == x + BitVecVal(0x7F, 8), r2 == x + BitVecVal(0x3F, 8)),
                      params=[x],
                      function_applications={ ('f', (x,)): (r1,), ('g', (x,)): (r2,) })
    problem = Problem(constraints=[spec], funcs={ 'f': func, 'g': func })
    prgs, stats, debug = _downscale(problem, [ 4 ], size_range=(0, 4))
    assert _verifies(problem, prgs), prgs
    assert stats['fallback'] is False, debug.messages


def test_width_ladder_stops_at_first_success():
    problem = _single_func_problem(16, [ Bv(16).add_, Bv(16).and_ ],
                                   lambda x, r: r == x + BitVecVal(0x1234, 16))
    prgs, stats, debug = _downscale(problem, [ 4, 8 ])
    assert _verifies(problem, prgs), prgs
    assert stats['fallback'] is False
    assert [ it['transform'] for it in stats['iterations'] ] == [ 'downscale(4)' ]
    consts = _constant_operands(prgs['f'])
    assert [ c.as_long() for c in consts ] == [ 0x1234 ]


def test_default_ladder_is_used_when_no_widths_given():
    problem = _single_func_problem(16, [ Bv(16).add_ ],
                                   lambda x, r: r == x + BitVecVal(0x1234, 16))
    prgs, stats, debug = _downscale(problem, [])
    assert _verifies(problem, prgs), prgs
    assert stats['fallback'] is False
    assert stats['iterations'][0]['transform'] == 'downscale(4)'


def test_non_bitvector_problem_falls_back():
    src = """
(set-logic LIA)
(synth-fun f ((x Int)) Int
  ((Start Int) (C Int))
  ((Start Int (x (+ Start C)))
   (C Int (1 2))))
(declare-var x Int)
(constraint (= (f x) (+ x 2)))
(check-synth)
"""
    problem = SyGuS('test').read_problem(StringIO(src))
    prgs, stats, debug = _downscale(problem, [])
    assert _verifies(problem, prgs), prgs
    assert stats['fallback'] is True
    assert stats['iterations'] == []


def test_explicit_width_not_narrower_is_skipped():
    problem = _single_func_problem(8, [ Bv(8).add_ ],
                                   lambda x, r: r == x + BitVecVal(0x7F, 8))
    prgs, stats, debug = _downscale(problem, [ 8, 16 ])
    assert _verifies(problem, prgs), prgs
    assert stats['fallback'] is True
    assert all(it.get('skipped') == 'not pertinent' for it in stats['iterations'])


def test_sygus_hd01_downscaled():
    # Start ::= (bvand Start Start) | (bvsub Start Start) | x | #x00 | #xff | #x01
    # the constants are a finite set that stays an explicit operand slot;
    # constant re-synthesis must pick from it
    path = os.path.join(ROOT, 'resources', 'sygus', 'bv', 'sygus-hd-8bit', 'hd-01-d0-prog.sl')
    problem = read_problem(path)
    problem = replace(problem, funcs={ n: f.optimize_grammar() for n, f in problem.funcs.items() })
    prgs, stats, debug = _downscale(problem, [ 4 ], size_range=(0, 4))
    assert _verifies(problem, prgs), prgs
    assert stats['fallback'] is False, debug.messages
    printed = '(\n' + '\n'.join(p.copy_propagation().dce().sexpr(n) for n, p in prgs.items()) + '\n)\n'
    res = check(problem, parse_solution(StringIO(printed)))
    assert res, str(res)


# --- solve_constants -------------------------------------------------------

def test_solve_constants_multiple_functions():
    x, r1, r2 = BitVecs('x r1 r2', 8)
    func = synth_func_from_ops([x.sort()], [x.sort()], [ Bv(8).add_ ])
    add  = func.nonterminals[str(x.sort())].productions[0]
    spec = Constraint(phi=And(r1 == x + BitVecVal(0x7F, 8), r2 == x + BitVecVal(0x3F, 8)),
                      params=[x],
                      function_applications={ ('f', (x,)): (r1,), ('g', (x,)): (r2,) })
    problem = Problem(constraints=[spec], funcs={ 'f': func, 'g': func })
    # the same shape for both functions, with 4-bit placeholder constants
    def shape():
        return Prg(func, [ (add, [ (False, 0), (True, BitVecVal(0xF, 4)) ]) ], [ (False, 1) ])
    prgs, stats = solve_constants(problem, { 'f': shape(), 'g': shape() })
    assert prgs is not None
    assert _constant_operands(prgs['f'])[0].as_long() == 0x7F
    assert _constant_operands(prgs['g'])[0].as_long() == 0x3F
    assert 'time' in stats
    assert _verifies(problem, prgs)


def test_solve_constants_respects_finite_constant_set():
    src = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
  ((Start (_ BitVec 8)))
  ((Start (_ BitVec 8) (x (bvadd Start Start) #x05 #x0a))))
(declare-var x (_ BitVec 8))
(constraint (bvule #x01 (bvsub (f x) x)))
(constraint (bvule (bvsub (f x) x) #x07))
(check-synth)
"""
    problem = SyGuS('test').read_problem(StringIO(src))
    func = problem.funcs['f']
    add  = next(p for p in func.nonterminals['Start'].productions if p.op.name == 'bvadd')
    prg  = Prg(func, [ (add, [ (False, 0), (True, BitVecVal(0xF, 4)) ]) ], [ (False, 1) ])
    prgs, _ = solve_constants(problem, { 'f': prg })
    assert prgs is not None
    # any constant in 1..7 satisfies the constraints, only 5 is in the grammar
    assert _constant_operands(prgs['f'])[0].as_long() == 5
    # and the shape is rejected if the constant set admits no solution
    problem2 = SyGuS('test').read_problem(StringIO(src.replace('#x05', '#x09')))
    func2 = problem2.funcs['f']
    add2  = next(p for p in func2.nonterminals['Start'].productions if p.op.name == 'bvadd')
    prg2  = Prg(func2, [ (add2, [ (False, 0), (True, BitVecVal(0xF, 4)) ]) ], [ (False, 1) ])
    prgs2, _ = solve_constants(problem2, { 'f': prg2 })
    assert prgs2 is None


def test_solve_constants_without_constant_slots():
    problem = _single_func_problem(8, [ Bv(8).add_ ], lambda x, r: r == x + x)
    func = problem.funcs['f']
    add  = func.nonterminals[str(BitVecSort(8))].productions[0]
    good = Prg(func, [ (add, [ (False, 0), (False, 0) ]) ], [ (False, 1) ])
    prgs, _ = solve_constants(problem, { 'f': good })
    assert prgs is not None and _verifies(problem, prgs)
    bad = Prg(func, [], [ (False, 0) ])     # f(x) = x
    prgs, _ = solve_constants(problem, { 'f': bad })
    assert prgs is None


TESTS = [ v for k, v in sorted(globals().items()) if k.startswith('test_') ]


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
