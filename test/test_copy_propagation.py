"""Tests for `Prg.copy_propagation` on the solution-emitting path.

A `Prg` whose instructions are grammar productions is a derivation, and
`Prg.sexpr` prints the derived term.  Every `Prg -> Prg` rewrite that
`sygus.py` applies before printing (`copy_propagation().dce()`) therefore
has to preserve the printed term modulo let-inlining, or the emitted
define-fun leaves the language of the grammar.

Run as a script:

    python test/test_copy_propagation.py
"""
import os
import sys
from io import StringIO

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from util.sygus import SyGuS, parse_solution
from util.check import check, follows_grammar

def problem(text):
    return SyGuS('test').read_problem(StringIO(text))

def solution(text):
    return parse_solution(StringIO(text))

def emit(prg, name):
    """Print a program the way sygus.py does."""
    return prg.copy_propagation().dce().sexpr(name)

def roundtrip(prob, sol_text, fun='f', optimize=True):
    """Reproduce the pipeline of `sygus.py synth`: derive the solution over
       the *optimized* grammar (which is what the synthesizer searches), put
       the resulting program through the emit path, then check the printed
       define-fun against the grammar as *written*, the way `sygus.py check`
       and any other SyGuS reader does."""
    f = prob.funcs[fun]
    if optimize:
        f = f.optimize_grammar()
    res = follows_grammar(f, solution(sol_text)[fun])
    assert res.follows_grammar, res.error
    printed = emit(res.prgs[0], fun)
    return check(prob, solution(f'(\n{printed}\n)'))

# ---------------------------------------------------------------------------
# The grammar of resources/sygus/collection/general/inv_gen_ex23.sl: `Sign`
# holds three constants, so `Production.optimize` inlines it into
# `Term ::= (* Sign Var)` and `_inline`'s `simplify` turns `(* 1 {0})` into a
# production whose *semantics* is the identity while its *syntax* is still
# required.  Eliding it used to drop the `(* 1 ...)` wrapper.

COEFF = """
(set-logic LIA)
(synth-fun f ((x Int) (y Int)) Int
  ((Sum Int) (Term Int) (Sign Int) (Var Int))
  ((Sum Int ((+ Term Term)))
   (Term Int ((* Sign Var)))
   (Sign Int (0 1 (- 1)))
   (Var Int (x y))))
(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (- x y)))
(check-synth)
"""

SOL = '(\n(define-fun f ((x Int) (y Int)) Int (+ (* 1 x) (* (- 1) y)))\n)\n'

def test_emit_keeps_unit_coefficient():
    """`(* 1 x)` must survive the emit path: it is not a unit production.

       This is the regression test for the emitted define-fun of
       inv_gen_ex23.sl containing `(+ z ...)` instead of `(+ (* 1 z) ...)`."""
    prob = problem(COEFF)
    res = roundtrip(prob, SOL)
    assert res.follows_grammar, f'emitted solution left the grammar:\n{res}'
    assert res.satisfies_constraints, res

def test_emit_keeps_unit_coefficient_unoptimized():
    """The same solution over the grammar as written stays conforming too."""
    prob = problem(COEFF)
    res = roundtrip(prob, SOL, optimize=False)
    assert res.follows_grammar and res.satisfies_constraints, res

def test_emit_keeps_unit_coefficient_after_grammar_optimization():
    """Same, but through the optimized grammar, which is what `synth` uses."""
    prob = problem(COEFF)
    opt = prob.funcs['f'].optimize_grammar()
    ident = [ p for nt in opt.nonterminals.values() for p in nt.productions
              if p.op.is_identity ]
    # the optimizer really does manufacture the hazardous production ...
    assert [ p.sexpr for p in ident ] == [ '(* 1 {0})' ], [ p.sexpr for p in ident ]
    # ... but it is not a unit production, so it must not be propagated away
    assert not any(p.is_unit() for p in ident)

def test_is_unit_rejects_semantic_identities():
    """`is_unit` is syntactic: an identity-semantics production is not a unit."""
    opt = problem(COEFF).funcs['f'].optimize_grammar()
    for nt in opt.nonterminals.values():
        for p in nt.productions:
            if p.is_unit():
                assert p.sexpr.strip() == '{0}', p.sexpr

# ---------------------------------------------------------------------------
# A genuine unit production must still be propagated through, otherwise the
# fix would just disable copy propagation.  The parser merges plain chain
# productions away, but an annotated one survives.

UNIT = """
(set-logic LIA)
(synth-fun f ((x Int)) Int
  ((Start Int) (T Int))
  ((Start Int ((! T :max 3)))
   (T Int (x (+ T T)))))
(declare-var x Int)
(constraint (= (f x) (+ x x)))
(check-synth)
"""

def test_unit_production_is_recognized():
    prob = problem(UNIT)
    units = [ p for nt in prob.funcs['f'].nonterminals.values()
                for p in nt.productions if p.is_unit() ]
    assert units, 'expected a unit production in the grammar'
    for p in units:
        assert p.sexpr.strip() == '{0}'

def test_unit_production_is_propagated():
    """Propagating through a unit production keeps the term unchanged."""
    prob = problem(UNIT)
    sol = '(\n(define-fun f ((x Int)) Int (+ x x))\n)\n'
    res = follows_grammar(prob.funcs['f'], solution(sol)['f'])
    assert res.follows_grammar, res.error
    prg = res.prgs[0]
    assert len(prg.copy_propagation().dce()) <= len(prg)
    out = check(prob, solution(f'(\n{emit(prg, "f")}\n)'))
    assert out.follows_grammar and out.satisfies_constraints, out

# ---------------------------------------------------------------------------

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
