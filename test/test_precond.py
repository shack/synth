"""Tests for the treatment of operator preconditions.

Operators can be partial (`Func(..., precond=...)`, e.g. a division whose
divisor must not be zero).  The precondition is a synthesis-time device:
the constraints for a sampled input require it to hold wherever the
operator is applied (`Prg.eval_clauses`, `LenConstraints`), so the
synthesizer proposes no program that applies a partial operator outside
its domain on a sample.  The *meaning* of a program is its total SMT-LIB
semantics, and a program is correct iff it refines the constraint,

    prg(x, y) implies phi(x, y),

which is what `Constraint.verify` checks; a counterexample is an input x
with prg(x, y) and not phi(x, y).  `util.check` judges solutions by the
same property.  A program that violates a precondition is therefore
neither vacuously correct (the bug behind the `(bvudiv x #x00000000)`
solutions that hd-24 once produced) nor wrong because of the
precondition alone.

Run as a script:

    python test/test_precond.py
"""
import os
import sys
from io import StringIO

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from z3 import *

from synth.spec import Constraint, Spec, Prg, Problem, synth_func_from_ops
from synth.oplib import Bv
from synth.synth_n import LenCegis
from util.check import check
from util.sygus import SyGuS, parse_solution

WIDTH = 8
BV    = BitVecSort(WIDTH)
ZERO  = BitVecVal(0, WIDTH)
ONES  = BitVecVal((1 << WIDTH) - 1, WIDTH)

def udiv_func():
    """A synth-fun with the parameter x, the constant 0 and unsigned
       division, whose precondition is a non-zero divisor."""
    udiv = next(op for op in Bv(WIDTH).mul_div if op.name == 'udiv')
    return synth_func_from_ops([BV], [BV], [udiv], const_map={ ZERO: None })

def udiv_prg(func, divisor):
    """The program `udiv x divisor`; divisor is (is_const, value)."""
    prod = next(p for p in func.nonterminals[str(BV)].productions if p.op.name == 'udiv')
    return Prg(func, [ (prod, [ (False, 0), divisor ]) ], [ (False, 1) ])

def constraint(x, r, phi):
    return Constraint(phi=phi, params=(x,), function_applications={ ('f', (x,)): (r,) })

def value_of(prg, x, val):
    """What the program computes for x = val under the SMT-LIB semantics."""
    _, (out,) = prg.to_exp([ x ])
    return simplify(substitute(out, (x, val)))

# ---------------------------------------------------------------------------

def test_verify_is_not_vacuous_for_a_violated_precondition():
    # udiv x 0 is 0xff for every x (SMT-LIB), so it does not refine f(x) = 0;
    # with the precondition as an assumption, the verifier found no
    # counterexample and accepted the program
    x, r = BitVecs('x r', WIDTH)
    func = udiv_func()
    prg  = udiv_prg(func, (True, ZERO))
    cex, stat = constraint(x, r, r == ZERO).verify({ 'f': prg })
    assert cex is not None, stat
    assert value_of(prg, x, cex[0]).as_long() == ONES.as_long(), cex

def test_verify_judges_by_the_total_semantics():
    # the same program refines f(x) = 0xff although the precondition of
    # udiv is violated for every input: the precondition alone is no
    # counterexample
    x, r = BitVecs('x r', WIDTH)
    func = udiv_func()
    prg  = udiv_prg(func, (True, ZERO))
    cex, stat = constraint(x, r, r == ONES).verify({ 'f': prg })
    assert cex is None, (cex, stat)

def test_counterexample_is_an_input_where_phi_fails():
    # udiv x x is 1 for x != 0 and 0xff for x = 0: the only counterexample
    # to f(x) = 1 is x = 0, and it is one because of the value computed
    # there, not because of the precondition
    x, r = BitVecs('x r', WIDTH)
    func = udiv_func()
    prg  = udiv_prg(func, (False, 0))
    cex, stat = constraint(x, r, r == BitVecVal(1, WIDTH)).verify({ 'f': prg })
    assert cex is not None and cex[0].as_long() == 0, (cex, stat)
    cex, stat = constraint(x, r, If(x == ZERO, r == ONES, r == BitVecVal(1, WIDTH))).verify({ 'f': prg })
    assert cex is None, (cex, stat)

def test_spec_precondition_marks_dont_care_inputs():
    # a precondition of a *specification* (Spec(..., precond=...)) is
    # folded into phi as an implication: outside of it the program may
    # compute anything, in contrast to an operator precondition
    x, r = BitVecs('x r', WIDTH)
    func = udiv_func()
    spec = Spec('f', r == BitVecVal(1, WIDTH), (r,), (x,), precond=(x != ZERO))
    cex, stat = spec.verify({ 'f': udiv_prg(func, (False, 0)) })
    assert cex is None, (cex, stat)
    cex, stat = spec.verify({ 'f': udiv_prg(func, (True, ZERO)) })
    assert cex is not None and cex[0].as_long() != 0, (cex, stat)

# ---------------------------------------------------------------------------

def test_synthesis_constraints_require_the_precondition():
    x, r = BitVecs('x r', WIDTH)
    func = udiv_func()
    prg  = udiv_prg(func, (True, ZERO))
    # the clauses for a sample (the default of eval_clauses) assert the
    # precondition, which udiv x 0 cannot satisfy ...
    s = Solver()
    s.add(list(prg.eval_clauses([ x ], [ r ])))
    assert s.check() == unsat
    # ... the relation the program denotes (the default of eval_term) is
    # its total semantics
    s = Solver()
    s.add(prg.eval_term([ x ], [ r ]))
    s.add(r != ONES)
    assert s.check() == unsat
    s = Solver()
    s.add(prg.eval_term([ x ], [ r ]))
    assert s.check() == sat

def test_synthesizer_does_not_apply_partial_operators_outside_their_domain():
    # f(x) = 0xff with x, 0 and udiv: udiv x 0 is the only program with one
    # instruction that refines the constraint, and it is exactly the one
    # the synthesizer must not propose since it divides by 0 on every
    # sample
    x, r = BitVecs('x r', WIDTH)
    func = udiv_func()
    problem = Problem(constraints=[ constraint(x, r, r == ONES) ], funcs={ 'f': func })
    prgs, _ = LenCegis(size_range=(1, 1)).synth_prgs(problem)
    assert prgs is None, prgs
    # the checker, which only knows the meaning of a solution, accepts it
    res = check(read_problem(UDIV_SYGUS.format(rhs='#xff')),
                parse_solution(StringIO(SOL_UDIV_ZERO)))
    assert res, res

# ---------------------------------------------------------------------------

UDIV_SYGUS = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8)
  ((S (_ BitVec 8)))
  ((S (_ BitVec 8) (x #x00 (bvudiv S S)))))
(declare-var x (_ BitVec 8))
(constraint (= (f x) {rhs}))
(check-synth)
"""

SOL_UDIV_ZERO = '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvudiv x #x00))'
# bvand is not in the grammar: the constraints are checked with the
# SyGuS parser instead of the derivation
SOL_UDIV_ZERO_NO_GRAMMAR = '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvudiv x (bvand x #x00)))'

def read_problem(text):
    return SyGuS('test').read_problem(StringIO(text))

def test_checker_uses_the_same_refinement_property():
    for sol, grammar in ((SOL_UDIV_ZERO, True), (SOL_UDIV_ZERO_NO_GRAMMAR, False)):
        res = check(read_problem(UDIV_SYGUS.format(rhs='#xff')), parse_solution(StringIO(sol)))
        assert res.follows_grammar == grammar and res.satisfies_constraints, res
        res = check(read_problem(UDIV_SYGUS.format(rhs='#x00')), parse_solution(StringIO(sol)))
        assert res.follows_grammar == grammar and not res.satisfies_constraints, res
        c = res.constraints[0]
        assert c.result == 'violated' and c.counterexample is not None, res

# ---------------------------------------------------------------------------

def test_verify_does_not_pass_an_undecided_query():
    # x^3 + y^3 != z^3 for positive x, y, z is beyond z3 (cf. test_check);
    # an undecided verification must not count as "no counterexample"
    x, y, z, r = Ints('x y z r')
    cube = lambda v: v * v * v
    c = Constraint(phi=Implies(And(x > 0, y > 0, z > 0), r != cube(z)), params=(x, y, z),
                   function_applications={ ('f', (x, y, z)): (r,) })
    class Sum:
        def eval_term(self, ins, outs, add_precond=False):
            a, b, _ = ins
            return outs[0] == cube(a) + cube(b)
    old = get_param('timeout')
    set_param('timeout', 2000)
    try:
        try:
            c.verify({ 'f': Sum() })
        except AssertionError as e:
            assert 'unknown' in str(e), e
        else:
            raise AssertionError('undecided verification passed')
        cex, stat = c.verify({ 'f': Sum() }, allow_unknown=True)
        assert cex is None and stat['verif_result'] == 'unknown', stat
    finally:
        set_param('timeout', old)

def test_initial_samples_are_counterexamples_to_the_empty_program():
    # the empty program computes anything, so its counterexamples are the
    # inputs for which some output violates phi: here only x = 0
    x, r = BitVecs('x r', WIDTH)
    c = constraint(x, r, Implies(x == ZERO, r == ZERO))
    samples = c.counterexample_eval.sample_n(3)
    assert [ [ v.as_long() for v in s ] for s in samples ] == [ [ 0 ] ], samples
    # running out of inputs leaves the sampler usable
    again = c.counterexample_eval.sample_n(3)
    assert [ [ v.as_long() for v in s ] for s in again ] == [ [ 0 ] ], again

# ---------------------------------------------------------------------------

def main():
    tests = [ (n, f) for n, f in sorted(globals().items()) if n.startswith('test_') and callable(f) ]
    for name, f in tests:
        print(name)
        f()
    print(f'{len(tests)} tests passed')

if __name__ == '__main__':
    main()
