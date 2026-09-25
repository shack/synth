"""Tests for the forall synthesizer `LenFA`.

`LenFA` encodes the specification as one forall/exists formula over
instances of the synthesized functions instead of running CEGIS (see
`_FASession.create_synth`).  The tests hold it to the results of
`LenCegis`: the shortest program has the same length, and enumerating
all programs of one size gives the same set as the fresh-solver oracle
of test_synth_all_prgs.py, whose grammars and helpers are reused.
Problems with several constraints are fused by `Problem.fuse_constraints`
first, which has its own test here.  Like `Constraint.verify`, `LenFA`
judges programs by the total semantics of their operators (the
refinement rule, see test_precond.py); programs that satisfy the
constraints only under the interpretation the model picked for an
operator z3 leaves unspecified are excluded.

Run as a script:

    python test/test_len_fa.py
"""
import os
import sys

from z3 import *

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from synth.spec import Constraint, Func, Problem, synth_func_from_ops
from synth.oplib import Bv
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

def test_refinement_semantics():
    """LenFA accepts exactly the programs `Constraint.verify` accepts.
       `udiv x x` refines f(x) = ite(x = 0, 0xf, 1) with the SMT-LIB
       semantics although it divides by zero at x = 0; with the operator
       preconditions in the forall formula it was rejected."""
    # small width: z3's quantified solving over bvudiv is slow at 8 bits
    W = 4
    udiv = next(op for op in Bv(W).mul_div if op.name == 'udiv')
    func = synth_func_from_ops([ BitVecSort(W) ], [ BitVecSort(W) ], [ udiv ], const_map={})
    x, r = BitVecs('x r', W)
    phi  = If(x == 0, r == BitVecVal((1 << W) - 1, W), r == BitVecVal(1, W))
    c    = Constraint(phi, (x,), { ('f', (x,)): (r,) })
    problem = Problem(constraints=[ c ], funcs={ 'f': func })
    prgs, _ = LenFA(size_range=(1, 1)).synth_prgs(problem)
    assert prgs is not None
    (prod, opnds), = prgs['f'].insns
    assert prod.op.name == 'udiv' and opnds == [ (False, 0), (False, 0) ], prgs['f']
    assert c.verify(prgs)[0] is None

def test_unspecified_operator_is_rechecked():
    """An uninterpreted function stands in for an operator z3 leaves
       unspecified (Int division by zero, on which the quantified solving
       does not terminate).  The forall formula is satisfiable for `u x`
       against f(x) = x, but only under the interpretation the model picks
       for u; `Constraint.verify` rejects the program, so LenFA must not
       return it."""
    W = 4
    BV = BitVecSort(W)
    u  = Function('u', BV, BV)
    x, r = BitVecs('x r', W)
    func = synth_func_from_ops([ BV ], [ BV ], [ Func('u', u(x)) ], const_map={})
    c    = Constraint(r == x, (x,), { ('f', (x,)): (r,) })
    problem = Problem(constraints=[ c ], funcs={ 'f': func })
    prgs, _ = LenFA(size_range=(1, 1)).synth_prgs(problem)
    assert prgs is None, prgs

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
