"""Tests for `synth_all_prgs`, which enumerates all programs of one size.

`_Session.synth_all_prgs` reuses one solver: after every program it adds
the negation of `LenConstraints.prg_constraints` and synthesizes again.
Two things have gone wrong here before and are pinned by these tests:

- the exclusion has to describe the found program exactly, including the
  parameter operands of productions and the output operands; otherwise the
  same program is found again or unrelated programs are excluded;
- the CEGIS instances of all rounds have to live side by side in the
  solver; otherwise a later round pins the instance variables of an
  earlier round to new counterexamples and the enumeration stops early.

The oracle is `LenCegis.synth_prgs` with a fresh solver per program and
the exclusions of the programs found so far passed as additional
constraints.  It shares the exclusion encoding with `synth_all_prgs` but
none of the solver state.  test_len_fa.py reuses the grammars and helpers
to hold the forall synthesizer to the same results.

Run as a script:

    python test/test_synth_all_prgs.py
"""
import itertools
import os
import sys
from io import StringIO

from z3 import And, Not

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from synth.synth_n import LenCegis
from util.sygus import SyGuS

# A program that is found twice makes `synth_all_prgs` loop forever, so
# every enumeration is cut off here and asserted to end before the cut.
LIMIT = 100

# f(x, y) = x + y with a production that has the parameter x as operand:
# the only 1-instruction program is (bvadd x y).
PARAM_OPERAND = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 4)) (y (_ BitVec 4))) (_ BitVec 4)
  ((Start (_ BitVec 4)))
  ((Start (_ BitVec 4) (x y (bvadd x Start) (bvsub Start Start)))))
(declare-var x (_ BitVec 4))
(declare-var y (_ BitVec 4))
(constraint (= (f x y) (bvadd x y)))
(check-synth)
"""

# f(x, y) is x or is y: the two 0-instruction programs differ only in the
# output operand.
OUTPUTS = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 4)) (y (_ BitVec 4))) (_ BitVec 4)
  ((Start (_ BitVec 4)))
  ((Start (_ BitVec 4) (x y (bvadd Start Start)))))
(declare-var x (_ BitVec 4))
(declare-var y (_ BitVec 4))
(constraint (or (= (f x y) x) (= (f x y) y)))
(check-synth)
"""

# 2-instruction programs computing the identity: rejecting the many
# non-solutions takes several CEGIS rounds with new counterexamples.
IDENTITY = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 4))) (_ BitVec 4)
  ((Start (_ BitVec 4)))
  ((Start (_ BitVec 4) (x (bvneg Start) (bvnot Start) (bvand Start Start)
     (bvor Start Start) (bvxor Start Start) (bvadd Start Start) (bvsub Start Start)))))
(declare-var x (_ BitVec 4))
(constraint (= (f x) x))
(check-synth)
"""

# Two identity functions with 2 instructions in total.  One of them is
# (bvneg (bvneg x)) or (bvnot (bvnot x)), the other one is x.
TWO_FUNCS = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 4))) (_ BitVec 4)
  ((Start (_ BitVec 4)))
  ((Start (_ BitVec 4) (x (bvneg Start) (bvnot Start)))))
(synth-fun g ((x (_ BitVec 4))) (_ BitVec 4)
  ((Start (_ BitVec 4)))
  ((Start (_ BitVec 4) (x (bvneg Start) (bvnot Start)))))
(declare-var x (_ BitVec 4))
(constraint (= (f x) x))
(constraint (= (g x) x))
(check-synth)
"""

def read(src):
    return SyGuS('test').read_problem(StringIO(src))

def key(prgs):
    return tuple((name, str(prgs[name])) for name in sorted(prgs))

def check(problem, found):
    """Every program satisfies the specification and none is found twice."""
    assert len(found) < LIMIT, 'enumeration did not terminate'
    for prgs in found:
        for c in problem.constraints:
            cex, _ = c.verify(prgs)
            assert cex is None, f'{key(prgs)} is wrong for {cex}'
    keys = [ key(prgs) for prgs in found ]
    assert len(set(keys)) == len(keys), 'a program was enumerated twice'
    return set(keys)

def all_prgs(src, size, synth_cls=LenCegis, **options):
    problem = read(src)
    synth = synth_cls(size_range=(size, size), **options)
    found = [ prgs for prgs, _ in itertools.islice(synth.synth_all_prgs(problem), LIMIT) ]
    return check(problem, found)

def oracle(src, size):
    problem = read(src)
    found = []
    def exclude(constr, n_insns):
        for prgs in found:
            yield Not(And([ c for name, s in constr.items()
                              for c in s.prg_constraints(prgs[name]) ]))
    while len(found) < LIMIT:
        prgs, _ = LenCegis(size_range=(size, size)).synth_prgs(problem, exclude)
        if prgs is None:
            break
        found.append(prgs)
    return check(problem, found)

def test_parameter_operand_is_excluded_exactly():
    found = all_prgs(PARAM_OPERAND, 1)
    assert len(found) == 1, found
    assert found == oracle(PARAM_OPERAND, 1)

def test_outputs_are_part_of_the_program():
    found = all_prgs(OUTPUTS, 0)
    assert len(found) == 2, found
    assert found == oracle(OUTPUTS, 0)

def test_counterexamples_accumulate_across_rounds():
    expected = oracle(IDENTITY, 2)
    assert len(expected) > 1, expected
    assert all_prgs(IDENTITY, 2) == expected
    assert all_prgs(IDENTITY, 2, keep_samples=True) == expected

def test_multiple_functions():
    expected = oracle(TWO_FUNCS, 2)
    assert len(expected) == 4, expected
    assert all_prgs(TWO_FUNCS, 2) == expected

def main():
    tests = [ (n, f) for n, f in sorted(globals().items())
                if n.startswith('test_') and callable(f) ]
    for name, f in tests:
        print(name)
        f()
        print('  ok')
    print(f'{len(tests)} tests passed')

if __name__ == '__main__':
    main()
