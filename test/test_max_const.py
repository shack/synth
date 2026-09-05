"""Tests that `max_const` counts constants identically with and without
grammar optimization.

`--opt-grammar` inlines bounded constant sets into productions
(`Production._inline`): the constant then no longer occupies an operand
slot with an is-const flag, so a bound over the flags alone would let
inlined constants escape the budget.  The synthesizer charges
`Production.n_inlined_consts` to the instruction that selects the
production instead; these tests pin that count and the end-to-end
semantics.

The SyGuS format cannot express `max_const`, so the tests set it through
the library API.

Run as a script:

    python test/test_max_const.py
"""
import os
import sys
from dataclasses import replace
from io import StringIO

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from synth.synth_n import LenCegis
from util.sygus import SyGuS

# f(x) = x + c1 + c2 + ... with every ci drawn from {1, 2}: reaching x+2
# takes one constant, x+3 takes two.
GRAMMAR = """
(set-logic LIA)
(synth-fun f ((x Int)) Int
  ((Start Int) (C Int))
  ((Start Int (x (+ Start C)))
   (C Int (1 2))))
(declare-var x Int)
(constraint (= (f x) (+ x {offset})))
(check-synth)
"""

def problem(offset, max_const, optimize):
    p = SyGuS('test').read_problem(StringIO(GRAMMAR.format(offset=offset)))
    funcs = {}
    for name, f in p.funcs.items():
        if optimize:
            f = f.optimize_grammar()
        funcs[name] = replace(f, max_const=max_const)
    return replace(p, funcs=funcs)

def synth(offset, max_const, optimize):
    prgs, _ = LenCegis(size_range=(0, 4)).synth_prgs(
        problem(offset, max_const, optimize))
    return prgs

def test_inlined_constants_are_counted():
    for optimize in (False, True):
        prgs = synth(3, 1, optimize)
        assert prgs is None, \
            f'x+3 needs two constants but max_const=1 (optimize={optimize}): ' \
            f'{ {n: str(p) for n, p in prgs.items()} }'

def test_budget_admits_one_constant():
    for optimize in (False, True):
        assert synth(2, 1, optimize) is not None, \
            f'x+2 uses one constant (optimize={optimize})'

def test_two_constants_fit_budget_two():
    for optimize in (False, True):
        assert synth(3, 2, optimize) is not None, \
            f'x+3 fits max_const=2 (optimize={optimize})'

def test_clone_carries_inlined_count():
    f = problem(3, None, optimize=True).funcs['f']
    prods = f.nonterminals['Start'].productions
    assert sorted(p.sexpr for p in prods) == ['(+ {0} 1)', '(+ {0} 2)'], \
        [p.sexpr for p in prods]
    assert all(p.n_inlined_consts == 1 for p in prods), \
        [(p.sexpr, p.n_inlined_consts) for p in prods]

def test_stock_production_carries_no_count():
    f = problem(3, None, optimize=False).funcs['f']
    prods = f.nonterminals['Start'].productions
    assert all(p.n_inlined_consts == 0 for p in prods), \
        [(p.sexpr, p.n_inlined_consts) for p in prods]

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
