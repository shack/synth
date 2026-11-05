"""Tests for trying program sizes in parallel (synth.parallel).

`parallel.search` runs one forked worker per program size and decides,
depending on `ParMode`, which size the programs are taken from.  The
policy is tested with fake workers that sleep instead of solving.  The
programs travel back through `Transport`, which sends z3 terms as SMT-LIB
text and the productions of the problem as references; the nop
instruction of problems with several functions travels by value.  With
the synthesizers, the parallel search (MIN) is held to the sequential one:
the shortest program has the same length and enumerating all programs of
the shortest size gives the same set.  Grammars and helpers come from
test_synth_all_prgs.py.

Run as a script:

    python test/test_parallel.py
"""
import itertools
import multiprocessing
import os
import sys
import time
from contextlib import closing

from z3 import *

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from synth import parallel, util
from synth.oplib import Bv
from synth.parallel import ParMode
from synth.spec import Constraint, Problem, synth_func_from_ops
from synth.synth_n import LenCegis, LenFA, SolverUnknown
from synth.transform.driver import Downscale
from test_synth_all_prgs import (PARAM_OPERAND, OUTPUTS, IDENTITY, TWO_FUNCS,
                                 LIMIT, check, read)

# f(x) = (x + 1) & ~x needs three instructions.
THREE = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 4))) (_ BitVec 4)
  ((Start (_ BitVec 4)))
  ((Start (_ BitVec 4) (x #x1 (bvadd Start Start) (bvnot Start)
     (bvand Start Start) (bvor Start Start)))))
(declare-var x (_ BitVec 4))
(constraint (= (f x) (bvand (bvadd x #x1) (bvnot x))))
(check-synth)
"""

# --- scheduling policy ------------------------------------------------------

def fake(plan, default=(0, 0)):
    """A `gen_fn` for `parallel.search`.  `plan` maps a size to (delay in s,
       outcome); the outcome is the number of programs, an exception to
       raise, or 'crash'."""
    def gen(n_insns):
        delay, outcome = plan.get(n_insns, default)
        time.sleep(delay)
        if outcome == 'crash':
            os._exit(3)
        if isinstance(outcome, Exception):
            raise outcome
        if outcome == 0:
            yield None, { 'n': n_insns }
        for i in range(outcome):
            yield { 'f': (n_insns, i) }, { 'n': n_insns, 'i': i }
    return gen

TRANSPORT = parallel.Transport(read(PARAM_OPERAND))

def search(plan, lo=0, hi=8, workers=4, mode=ParMode.MIN, default=(0, 0)):
    stats = {}
    with util.timer() as elapsed:
        res = list(parallel.search(fake(plan, default), lo, hi, workers, mode,
                                   TRANSPORT, stats=stats))
        t = elapsed() / 1e9
    assert multiprocessing.active_children() == []
    status = { r['n_insns']: r['status'] for r in stats['lengths'] }
    return res, status, stats, t

def programs(res):
    return [ prgs for prgs, _ in res if prgs is not None ]

def unsat(res):
    return [ stats['n'] for prgs, stats in res if prgs is None ]

def test_min_waits_for_the_shorter_size():
    res, status, _, _ = search({ 3: (1.0, 1), 5: (0, 1) }, workers=6)
    assert programs(res) == [ { 'f': (3, 0) } ], res
    assert status[3] == 'prg' and status[5] == 'killed', status
    # the sizes without programs come first, in increasing order
    assert unsat(res) == sorted(unsat(res)) and unsat(res)[:3] == [ 0, 1, 2 ], res

def test_first_takes_the_first_program():
    res, status, _, _ = search({ 3: (1.0, 1), 5: (0, 1) }, workers=6, mode=ParMode.FIRST)
    assert programs(res) == [ { 'f': (5, 0) } ], res
    assert status[5] == 'prg' and status[3] == 'killed', status

def test_sizes_above_a_program_are_killed():
    plan = { 0: (0, 0), 1: (0, 0), 2: (1.0, 1), 4: (0, 1) }
    res, status, _, t = search(plan, default=(30, 0))
    assert programs(res) == [ { 'f': (2, 0) } ], res
    assert all(status[n] == 'killed' for n in (3, 4, 5)), status
    assert t < 10, t

def test_a_finished_size_frees_its_slot():
    res, status, stats, _ = search({ 5: (0.3, 1) }, workers=2, default=(0.3, 0))
    assert programs(res) == [ { 'f': (5, 0) } ], res
    assert unsat(res) == [ 0, 1, 2, 3, 4 ], res
    records = stats['lengths']
    for r in records:
        overlapping = [ o for o in records
                        if o['start'] <= r['start'] < o['start'] + o['time'] ]
        assert len(overlapping) <= 2, records

def test_all_programs_of_the_chosen_size():
    res, _, _, _ = search({ 2: (0, 5) })
    assert programs(res) == [ { 'f': (2, i) } for i in range(5) ], res

def test_no_program():
    res, status, _, _ = search({}, hi=5, workers=3)
    assert res == [ (None, { 'n': n }) for n in range(6) ], res
    assert all(s == 'unsat' for s in status.values()), status

def test_solver_unknown_is_raised_in_the_parent():
    plan = { 0: (0, 0), 1: (0, SolverUnknown(1, 'test')) }
    try:
        search(plan, default=(30, 0))
    except SolverUnknown as e:
        assert e.n_insns == 1 and e.reason == 'test', e
        assert any('in the worker for 1 instructions' in n for n in e.__notes__), e.__notes__
    else:
        assert False, 'SolverUnknown expected'
    assert multiprocessing.active_children() == []

def test_crashing_worker():
    try:
        search({ 1: (0, 'crash') }, default=(30, 0))
    except RuntimeError as e:
        assert 'died' in str(e), e
    else:
        assert False, 'RuntimeError expected'
    assert multiprocessing.active_children() == []

def test_caller_stops_early():
    stats = {}
    gen = parallel.search(fake({ 1: (0, 1000) }, default=(30, 0)), 0, 8, 3,
                          ParMode.FIRST, TRANSPORT, stats=stats)
    with closing(gen):
        prgs, _ = next(gen)
    assert prgs == { 'f': (1, 0) }, prgs
    assert multiprocessing.active_children() == []
    status = { r['n_insns']: r['status'] for r in stats['lengths'] }
    assert status == { 0: 'killed', 1: 'prg', 2: 'killed' }, status

# --- transport ----------------------------------------------------------------

def test_values_round_trip():
    vals = [ BitVecVal(3, 8), IntVal(-5), RealVal('1/3'), StringVal('a"b'),
             BoolVal(False), FPVal(1.5, Float32()) ]
    for v in vals:
        w = TRANSPORT.loads(TRANSPORT.dumps(v))
        assert v.eq(w), (v, w)

def test_programs_round_trip():
    # the programs of TWO_FUNCS have nop instructions (sent by value), the
    # one of THREE has a constant operand
    for src, size, feature in ((TWO_FUNCS, 2, 'nop'), (THREE, 3, 'const')):
        problem = read(src)
        transport = parallel.Transport(problem)
        found = list(itertools.islice(LenCegis(size_range=(size, size)).synth_all_prgs(problem), LIMIT))
        insns = [ i for prgs, _ in found for prg in prgs.values() for i in prg.insns ]
        if feature == 'nop':
            assert any(prod.op.name == '$nop' for prod, _ in insns), found
        else:
            assert any(is_const for _, opnds in insns for is_const, _ in opnds), found
        for prgs, stats in found:
            loaded, loaded_stats = transport.loads(transport.dumps((prgs, stats)))
            assert loaded_stats == stats
            for name, prg in prgs.items():
                assert loaded[name] == prg, (loaded[name], prg)
                assert loaded[name].sexpr(name) == prg.sexpr(name)
                assert loaded[name].sig is prg.sig

# --- synthesizers -------------------------------------------------------------

def n_insns(prgs):
    return sum(len(prg.insns) for prg in prgs.values())

def verifies(problem, prgs):
    return prgs is not None and all(c.verify(prgs)[0] is None for c in problem.constraints)

def test_min_has_the_length_of_the_sequential_search():
    for src in (PARAM_OPERAND, OUTPUTS, IDENTITY, TWO_FUNCS, THREE):
        problem = read(src)
        seq, _ = LenCegis(size_range=(0, 5)).synth_prgs(problem)
        assert verifies(problem, seq), src
        for options in ({ 'par_workers': 3 }, { 'par_workers': 2, 'par_start': 2 }):
            options['par_mode'] = ParMode.MIN
            par, stats = LenCegis(size_range=(0, 5), **options).synth_prgs(problem)
            assert verifies(problem, par), (src, options)
            assert n_insns(par) == n_insns(seq), (src, options, par, seq)
            if n_insns(seq) >= options.get('par_start', 0):
                assert 'parallel' in stats, stats
    assert n_insns(seq) >= 3, seq

def test_first_is_the_default_and_finds_a_correct_program():
    problem = read(THREE)
    seq, _ = LenCegis(size_range=(0, 6)).synth_prgs(problem)
    par, stats = LenCegis(size_range=(0, 6), par_workers=4).synth_prgs(problem)
    assert verifies(problem, par), par
    assert n_insns(par) >= n_insns(seq), (par, seq)
    assert stats['parallel']['mode'] == 'FIRST', stats

def test_no_program_in_the_size_range():
    problem = read(THREE)
    prgs, stats = LenCegis(size_range=(0, 2), par_workers=2).synth_prgs(problem)
    assert prgs is None, prgs
    assert len(stats['iterations']) == 3, stats
    assert [ r['status'] for r in stats['parallel']['lengths'] ] == [ 'unsat' ] * 3, stats

def test_all_programs_like_the_sequential_search():
    for src, lo in ((OUTPUTS, 0), (IDENTITY, 2), (TWO_FUNCS, 2)):
        problem = read(src)
        def enumerate_with(**options):
            synth = LenCegis(size_range=(lo, lo + 2), **options)
            found = [ prgs for prgs, _ in itertools.islice(synth.synth_all_prgs(problem), LIMIT) ]
            return check(problem, found)
        expected = enumerate_with()
        assert len(expected) > 0, src
        assert enumerate_with(par_workers=3, par_mode=ParMode.MIN) == expected, src
        assert multiprocessing.active_children() == []

def test_len_fa():
    problem = read(PARAM_OPERAND)
    prgs, _ = LenFA(size_range=(0, 3), par_workers=2, par_mode=ParMode.MIN).synth_prgs(problem)
    assert verifies(problem, prgs) and n_insns(prgs) == 1, prgs

def test_downscale_with_a_parallel_base():
    # f(x) = x + 0x7F, see test_downscale.py
    x, r = BitVecs('x r', 8)
    func = synth_func_from_ops([x.sort()], [r.sort()], [ Bv(8).add_, Bv(8).and_ ])
    spec = Constraint(phi=r == x + BitVecVal(0x7F, 8), params=[x],
                      function_applications={ ('f', (x,)): (r,) })
    problem = Problem(constraints=[spec], funcs={ 'f': func })
    sy = Downscale(target_widths=[ 4 ], base=LenCegis(size_range=(0, 3), par_workers=2))
    prgs, stats = sy.synth_prgs(problem)
    assert verifies(problem, prgs), prgs
    assert stats['fallback'] is False, stats
    assert multiprocessing.active_children() == []

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
