"""Tests for `Production._inline`, the inlining that `--opt-grammar` performs.

`Production.sexpr` numbers its `{k}` placeholders over the *non-terminal*
operands only (see `Production.nonterminal_operands`).  Inlining a
constants-only non-terminal removes some of those operands, so the constant
has to go into the placeholder of the operand it replaces and the surviving
operands have to be renumbered.  Getting the index space wrong corrupts the
printed term without touching the semantics of the production, so the
resulting define-fun is silently wrong.

Run as a script:

    python test/test_inline.py
"""
import os
import re
import sys
from io import StringIO

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from z3 import *
from util.sygus import SyGuS

def problem(text):
    return SyGuS('test').read_problem(StringIO(text))

def optimized(text, fun='g'):
    return problem(text).funcs[fun].optimize_grammar()

def productions(grammar, nt):
    return list(grammar.nonterminals[nt].productions)

def sexprs(grammar, nt):
    return sorted(str(p.sexpr) for p in productions(grammar, nt))

def placeholders(prod):
    return sorted(set(int(m) for m in re.findall(r'\{(\d+)\}', prod.sexpr)))

def check_convention(grammar, where=''):
    """Every production's placeholders must be exactly {0}..{n-1} for
       n non-terminal operands -- what util/check.py:269 requires."""
    for name, nt in grammar.nonterminals.items():
        for p in nt.productions:
            assert placeholders(p) == list(range(p.nonterminal_arity())), \
                f'{where}{name}: sexpr {p.sexpr!r} has placeholders ' \
                f'{placeholders(p)} but {p.nonterminal_arity()} non-terminal operands'

# ---------------------------------------------------------------------------
# A parameter operand that precedes the inlined non-terminal operand.  The
# raw operand index of C is 1, its non-terminal index is 0.

PARAM_FIRST = """
(set-logic LIA)
(synth-fun g ((x Int)) Int
  ((Start Int) (C Int))
  ((Start Int ((+ x C)))
   (C Int (1 2 3))))
(declare-var x Int)
(constraint (= (g 0) 2))
(check-synth)
"""

def test_param_before_nonterminal():
    g = optimized(PARAM_FIRST)
    assert sexprs(g, 'Start') == ['(+ x 1)', '(+ x 2)', '(+ x 3)'], sexprs(g, 'Start')
    check_convention(g)

def test_param_before_nonterminal_semantics_matches_sexpr():
    """The printed term and the production's function must agree."""
    g = optimized(PARAM_FIRST)
    for p in productions(g, 'Start'):
        const = int(re.search(r'\(\+ x (\d+)\)', str(p.sexpr)).group(1))
        # op.func is `x + const` over the single remaining input
        v, = p.op.inputs
        assert is_true(simplify(p.op.func == v + const)), (p.sexpr, p.op.func)

# ---------------------------------------------------------------------------
# Two non-terminal operands, only one of them inlined, with a parameter in
# front.  Operand order is (x, C, A): C has raw index 1 / non-terminal index
# 0, A has raw index 2 / non-terminal index 1.  After inlining C, A must be
# renumbered from {1} to {0}.

TWO_NONTERMINALS = """
(set-logic LIA)
(synth-fun g ((x Int)) Int
  ((Start Int) (A Int) (C Int))
  ((Start Int ((+ (* x C) A)))
   (A Int (x 7))
   (C Int (1 2 3))))
(declare-var x Int)
(constraint (= (g 3) 13))
(check-synth)
"""

def test_surviving_nonterminal_is_renumbered():
    g = optimized(TWO_NONTERMINALS)
    assert sexprs(g, 'Start') == ['(+ (* x 1) {0})', '(+ (* x 2) {0})', '(+ (* x 3) {0})'], \
        sexprs(g, 'Start')
    check_convention(g)

def test_surviving_nonterminal_operand_is_kept():
    """The subterm for A must not be dropped: one non-terminal operand stays."""
    g = optimized(TWO_NONTERMINALS)
    for p in productions(g, 'Start'):
        assert p.nonterminal_arity() == 1, (p.sexpr, p.operands, p.operand_is_nt)
        assert [ n for _, n in p.nonterminal_operands() ] == ['A'], p.operands

# ---------------------------------------------------------------------------
# All operands are non-terminals -- the shape that already worked, because
# raw and non-terminal index spaces coincide.  Guards against a regression.

ALL_NONTERMINALS = """
(set-logic LIA)
(synth-fun g ((x Int) (y Int)) Int
  ((Term Int) (Sign Int) (Var Int))
  ((Term Int ((* Sign Var)))
   (Sign Int (0 1 (- 1)))
   (Var Int (x y))))
(declare-var x Int)
(declare-var y Int)
(constraint (= (g x y) x))
(check-synth)
"""

def test_all_nonterminal_operands_unchanged():
    g = optimized(ALL_NONTERMINALS)
    assert sexprs(g, 'Term') == ['(* (- 1) {0})', '(* 0 {0})', '(* 1 {0})'], sexprs(g, 'Term')
    check_convention(g)

# ---------------------------------------------------------------------------
# Inlining must not drop the operator's precondition.

# `mod` is one of the operators `synth.util.analyze_precond` guards against a
# zero right operand (`Z3_OP_MOD` in `_NE0_OPS`; note integer `div` is
# `Z3_OP_IDIV` and is *not* in that set, so it carries no precondition).

MOD_BY_CONST = """
(set-logic LIA)
(synth-fun g ((x Int)) Int
  ((Start Int) (C Int))
  ((Start Int ((mod x C)))
   (C Int (0 1 2))))
(declare-var x Int)
(constraint (= (g 5) 1))
(check-synth)
"""

def test_precondition_survives_inlining():
    g = optimized(MOD_BY_CONST)
    by_const = { str(p.sexpr): p for p in productions(g, 'Start') }
    assert '(mod x 0)' in by_const, sorted(by_const)
    # taking the modulus of the inlined 0 must stay guarded, i.e. unsatisfiable
    p = by_const['(mod x 0)']
    s = Solver()
    s.add(p.op.precond)
    assert s.check() == unsat, f'precondition of (mod x 0) is satisfiable: {p.op.precond}'
    # a non-zero constant must stay usable
    q = by_const['(mod x 2)']
    s = Solver()
    s.add(q.op.precond)
    assert s.check() == sat, f'precondition of (mod x 2) is unsatisfiable: {q.op.precond}'

# ---------------------------------------------------------------------------
# `lhs.constants is None` (the non-terminal allows any constant) must not
# raise.  The membership test is only reached when the inlined production
# folds to a value, so `(* A B)` has to have *both* operands inlined.

UNBOUNDED_LHS = """
(set-logic LIA)
(synth-fun g ((x Int)) Int
  ((Start Int) (A Int) (B Int))
  ((Start Int ((Constant Int) (+ x Start) (* A B)))
   (A Int (2 3))
   (B Int (5 7))))
(declare-var x Int)
(constraint (= (g 0) 10))
(check-synth)
"""

def test_unbounded_constants_on_lhs_does_not_raise():
    assert problem(UNBOUNDED_LHS).funcs['g'].nonterminals['Start'].constants is None
    g = optimized(UNBOUNDED_LHS)
    check_convention(g)

def test_unbounded_constants_keep_the_uninlined_production():
    """Every folded value is already available as a constant, so all inlined
       variants are dropped and the original production survives."""
    g = optimized(UNBOUNDED_LHS)
    assert sexprs(g, 'Start') == ['(* {0} {1})', '(+ x {0})'], sexprs(g, 'Start')

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
