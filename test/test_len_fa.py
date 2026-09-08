"""Tests for the forall synthesizer `LenFA`.

`LenFA` encodes the specification as one forall/exists formula over
instances of the synthesized functions instead of running CEGIS (see
`_FASession.create_synth`).  The tests hold it to the results of
`LenCegis`: the shortest program has the same length, and enumerating
all programs of one size gives the same set as the fresh-solver oracle
of test_synth_all_prgs.py, whose grammars and helpers are reused.
Problems with several constraints are fused by `Problem.fuse_constraints`
first, which has its own test here.

Run as a script:

    python test/test_len_fa.py
"""
import os
import sys

from z3 import And, Ints, Solver, unsat

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from synth.spec import Constraint, Problem
from synth.synth_n import LenCegis, LenFA
from test_synth_all_prgs import (PARAM_OPERAND, OUTPUTS, IDENTITY, TWO_FUNCS,
                                 all_prgs, oracle, read)

def n_insns(prgs):
    return sum(len(prg.insns) for prg in prgs.values())

def test_shortest_program_has_the_length_cegis_finds():
    # x + y needs one instruction; the identity is x itself.
    for src, expected in ((PARAM_OPERAND, 1), (IDENTITY, 0), (TWO_FUNCS, None)):
        problem = read(src)
        fa, _ = LenFA(size_range=(0, 3)).synth_prgs(problem)
        assert fa is not None, src
        for c in problem.constraints:
            cex, _ = c.verify(fa)
            assert cex is None, f'{fa} is wrong for {cex}'
        cegis, _ = LenCegis(size_range=(0, 3)).synth_prgs(problem)
        assert n_insns(fa) == n_insns(cegis), (fa, cegis)
        if expected is not None:
            assert n_insns(fa) == expected, fa

def test_enumerates_the_same_programs_as_cegis():
    for src, size in ((PARAM_OPERAND, 1), (OUTPUTS, 0), (IDENTITY, 2)):
        assert all_prgs(src, size, LenFA) == oracle(src, size), (src, size)

def test_multiple_functions():
    """Two constraints are fused into one specification and the shorter
       function is padded with nops, as in `LenCegis`."""
    expected = oracle(TWO_FUNCS, 2)
    assert len(expected) == 4, expected
    assert all_prgs(TWO_FUNCS, 2, LenFA) == expected

def test_fuse_constraints_unites_params():
    """Two constraints over different parameters, as the invariant reader
       produces them, fuse to the union of the parameters; an application
       both of them contain keeps a single tuple of output variables."""
    x, y, o1, o2, o3 = Ints('x y o1 o2 o3')
    c1 = Constraint(o1 > x, (x,), { ('f', (x,)): (o1,) })
    c2 = Constraint(And(o2 < y, o3 == x), (y, x),
                    { ('f', (x,)): (o2,), ('f', (y,)): (o3,) })
    c, = Problem(constraints=[ c1, c2 ], funcs={}).fuse_constraints().constraints
    assert [ str(p) for p in c.params ] == [ 'x', 'y' ], c.params
    apps = c.function_applications
    assert set(apps) == { ('f', (x,)), ('f', (y,)) }, apps
    assert apps[('f', (x,))][0].eq(o1) and apps[('f', (y,))][0].eq(o3), apps
    # the second constraint now speaks about o1 where it used o2
    s = Solver()
    s.add(c.phi != And(o1 > x, o1 < y, o3 == x))
    assert s.check() == unsat, c.phi

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
