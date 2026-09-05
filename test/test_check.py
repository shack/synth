"""Tests for util.check.check.

Run as a script:

    python test/test_check.py
"""
import os
import sys
from io import StringIO

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from z3 import *
from util.sygus import SyGuS, parse_solution
from util.check import check

def problem(text):
    return SyGuS('test').read_problem(StringIO(text))

def solution(text):
    return parse_solution(StringIO(text))

def weight_values(res, prob, fun, weight):
    """The values of weight `weight` of synth-fun `fun` in the programs of the result."""
    _, var = prob.funcs[fun].weights[weight]
    return sorted(p.weights[var].as_long() for p in res.funcs[fun].prgs)

def run(name, prob, sol, grammar=True, constraints=True, note=None):
    if isinstance(prob, str):
        prob = problem(prob)
    res = check(prob, solution(sol))
    if res.follows_grammar != grammar:
        raise AssertionError(f'{name}: expected follows_grammar={grammar}\n{res}')
    if res.satisfies_constraints != constraints:
        raise AssertionError(f'{name}: expected satisfies_constraints={constraints}\n{res}')
    if bool(res) != (grammar and constraints):
        raise AssertionError(f'{name}: bool(res) inconsistent\n{res}')
    if note is not None and not any(note in n for n in res.notes):
        raise AssertionError(f'{name}: expected note {note!r}\n{res}')
    print(f'  ok  {name}')
    return res

# ---------------------------------------------------------------------------

LIA = """
(set-logic LIA)
(synth-fun f ((x Int) (y Int)) Int
  ((I Int) (Ic Int))
  ((I Int (0 1 x y (+ I I) (* Ic I)))
   (Ic Int (0 1 2 (- 1) (- 2)))))
(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (* 2 (+ x y))))
(check-synth)
"""

def test_lia_correct():
    run('lia_correct', LIA, '(define-fun f ((x Int) (y Int)) Int (+ (+ x x) (+ y y)))')

def test_lia_constant_from_other_nonterminal():
    run('lia_const_nt', LIA, '(define-fun f ((x Int) (y Int)) Int (* 2 (+ x y)))')

def test_lia_wrapped_and_let():
    # the output format of `sygus.py synth`
    run('lia_let', LIA, """(
(define-fun f ((x Int) (y Int)) Int
    (let ((x2 (+ x y)))
    (let ((res (+ x2 x2)))
    res)))
)""")

def test_lia_renamed_parameters():
    run('lia_rename', LIA, '(define-fun f ((a Int) (b Int)) Int (+ (+ a a) (+ b b)))')
    # swapped names: the solution's x is the synth-fun's y
    run('lia_swapped', LIA, '(define-fun f ((y Int) (x Int)) Int (+ (+ y y) (+ x x)))')

def test_lia_negative_constants():
    # (- 1) and -1 both denote the constant -1 of Ic; (* Ic I) is a production
    run('lia_neg_compound', LIA, '(define-fun f ((x Int) (y Int)) Int (* (- 1) (* (- 2) (+ x y))))')
    run('lia_neg_atom', LIA, '(define-fun f ((x Int) (y Int)) Int (* -1 (* -2 (+ x y))))')

def test_lia_grammar_violations():
    # 3 is not a constant of Ic
    res = run('lia_bad_const', LIA, '(define-fun f ((x Int) (y Int)) Int (* 3 (+ x y)))',
              grammar=False, constraints=False)
    assert '3 is not derivable from Ic' in res.funcs['f'].error, res.funcs['f'].error
    # there is no subtraction
    res = run('lia_bad_op', LIA, '(define-fun f ((x Int) (y Int)) Int (- (+ (+ x x) (+ y y)) 0))',
              grammar=False, constraints=True, note='without the grammar')
    assert '(- (+ (+ x x) (+ y y)) 0) is not derivable from I' in res.funcs['f'].error, res.funcs['f'].error
    # constants of I are 0 and 1 only, but the multiplication takes Ic first
    run('lia_wrong_position', LIA, '(define-fun f ((x Int) (y Int)) Int (* (+ x y) 2))',
        grammar=False, constraints=True)

def test_lia_constraint_violation():
    res = run('lia_wrong', LIA, '(define-fun f ((x Int) (y Int)) Int (+ x y))',
              grammar=True, constraints=False)
    c = res.constraints[0]
    assert c.result == 'violated' and c.counterexample is not None and len(c.counterexample) == 2, c

def test_signature_mismatch():
    # a define-fun with the wrong signature is not evaluated against the constraints
    res = run('sig_arity', LIA, '(define-fun f ((x Int)) Int (+ x x))', grammar=False, constraints=False,
              note='constraints not checked')
    assert res.constraints is None, res
    run('sig_sort', LIA, '(define-fun f ((x Int) (y Int)) Bool true)', grammar=False, constraints=False,
        note='constraints not checked')
    run('sig_missing', LIA, '(define-fun g ((x Int) (y Int)) Int x)', grammar=False, constraints=False,
        note='no define-fun for f')
    run('sig_malformed', LIA, '(define-fun f (x y) Int x)', grammar=False, constraints=False,
        note='constraints not checked')
    run('sig_malformed_body', LIA, '(define-fun f ((x Int) (y Int)) Int (ite (< x y)))', grammar=False,
        constraints=False, note='constraints not checked')

def test_unbound_identifiers():
    # y is not a parameter of the define-fun although the synth-fun has one
    res = run('unbound', LIA, '(define-fun f ((a Int) (b Int)) Int (+ (+ a a) (+ y y)))', grammar=False, constraints=False)
    assert 'unbound identifiers: y' in res.funcs['f'].error, res

def test_let_shadowing():
    run('let_swap', LIA, '(define-fun f ((a Int) (b Int)) Int (let ((x b) (y a)) (+ (+ x x) (+ y y))))')
    run('let_nested_shadow', LIA, '(define-fun f ((a Int) (b Int)) Int (let ((y a)) (let ((a b)) (+ (+ y y) (+ a a)))))')
    # parallel let: x and y are swapped simultaneously
    run('let_parallel', MIXED, '(define-fun f ((x Int) (y Int)) Int (let ((x y) (y x)) (+ y (+ y x))))')

def test_annotations_in_solution():
    run('annotated', LIA, '(define-fun f ((x Int) (y Int)) Int (! (+ (! (+ x x) :named a) (+ y y)) :named b))')

def test_deep_nesting():
    # `check` must cope with deeply nested solutions; note that tinysexpr's
    # own parser needs a raised recursion limit for such a term, too
    body = 'x'
    for i in range(500):
        body = f'(let ((v{i} (+ {body} 1))) v{i})'
    sol = f'(define-fun f ((x Int) (y Int)) Int {body})'
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(20000)
    try:
        parsed = solution(sol)
    finally:
        sys.setrecursionlimit(old)
    # the matching itself runs at the default recursion limit
    res = check(problem(LIA), parsed)
    assert res.follows_grammar and res.constraints is not None, res
    print('  ok  deep_nesting')

# ---------------------------------------------------------------------------

BV = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 32))) (_ BitVec 32)
  ((BV32 (_ BitVec 32)) (BV16 (_ BitVec 16)))
  ((BV32 (_ BitVec 32) (#x00000000 #x00000001 #xFFFFFFFF x
                        (bvand BV32 BV32) (bvor BV32 BV32) (bvnot BV32) (concat BV16 BV16)))
   (BV16 (_ BitVec 16) (#x0000 #x0001 #xFFFF
                        (bvand BV16 BV16) (bvor BV16 BV16) (bvnot BV16)
                        ((_ extract 31 16) BV32) ((_ extract 15 0) BV32)))))
(constraint (= (f #x0782ECAD) #xECAD0000))
(constraint (= (f #xFFFF008E) #x008E0000))
(constraint (= (f #x00000000) #x00000000))
(check-synth)
"""

def test_bv_correct():
    run('bv_correct', BV, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (concat ((_ extract 15 0) x) #x0000))')
    # alternative notations for the same constant
    run('bv_bin_const', BV, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (concat ((_ extract 15 0) x) #b0000000000000000))')
    run('bv_indexed_const', BV, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (concat ((_ extract 15 0) x) (_ bv0 16)))')

def test_bv_violations():
    # a 32-bit constant where a 16-bit one is needed
    run('bv_wrong_width', BV, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (concat ((_ extract 15 0) x) #x00000000))',
        grammar=False, constraints=False)
    # bvadd is not in the grammar
    run('bv_wrong_op', BV, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (bvadd (concat ((_ extract 15 0) x) #x0000) #x00000000))',
        grammar=False, constraints=True)
    # decimal numerals are not bit-vector literals (strict SMT-LIB)
    run('bv_decimal_const', BV, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (concat ((_ extract 15 0) x) 0))',
        grammar=False, constraints=False, note='constraints not checked')
    # wrong semantics
    run('bv_wrong_sem', BV, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (concat ((_ extract 31 16) x) #x0000))',
        grammar=True, constraints=False)

BV_DECIMAL = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8) ((B (_ BitVec 8))) ((B (_ BitVec 8) (x 0 1 (bvadd B #x01) (bvadd B B)))))
(declare-var x (_ BitVec 8))
(constraint (= (f x) (bvadd x #x01)))
(check-synth)
"""

def test_bv_grammar_constants():
    # the grammar writes the constants as numerals; embedded literals of a
    # production match any notation
    run('bv_grammar_decimal', BV_DECIMAL, '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvadd x #x01))')
    run('bv_embedded_indexed', BV_DECIMAL, '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvadd x (_ bv1 8)))')
    run('bv_embedded_bin', BV_DECIMAL, '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvadd x #b00000001))')
    run('bv_embedded_wrong', BV_DECIMAL, '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvadd x #x02))',
        grammar=False, constraints=False)
    run('bv_embedded_wrong_width', BV_DECIMAL, '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvadd x (_ bv1 16)))',
        grammar=False, constraints=False)

BV_NO_GRAMMAR = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8))
(declare-var x (_ BitVec 8))
(constraint (= (f x) (bvadd x x)))
(check-synth)
"""

def test_bv_default_grammar():
    run('bv_default', BV_NO_GRAMMAR, '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvadd x x))')
    run('bv_default_wrong', BV_NO_GRAMMAR, '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvor x x))', grammar=True, constraints=False)

# ---------------------------------------------------------------------------

MAX2 = """
(set-logic LIA)
(synth-fun max2 ((x Int) (y Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (x y 0 1 (+ Start Start) (- Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool)
                     (<= Start Start) (= Start Start) (>= Start Start)))))
(declare-var x Int)
(declare-var y Int)
(constraint (>= (max2 x y) x))
(constraint (>= (max2 x y) y))
(constraint (or (= x (max2 x y)) (= y (max2 x y))))
(check-synth)
"""

def test_max2_cvc5_output():
    run('max2_cvc5', MAX2, '(\n(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))\n)\n')
    run('max2_wrong', MAX2, '(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) x y))',
        grammar=True, constraints=False)
    # the leading result of some solvers is ignored
    run('max2_unsat_prefix', MAX2, 'unsat\n(define-fun max2 ((x Int) (y Int)) Int (ite (>= x y) x y))')

# ---------------------------------------------------------------------------

FIVE = """
(set-logic LIA)
(synth-fun f1 ((p1 Int) (P1 Int)) Int ((Start Int)) ((Start Int (p1 P1 (- Start Start) (+ Start Start)))))
(synth-fun f2 ((p1 Int) (P1 Int)) Int ((Start Int)) ((Start Int (p1 P1 (+ Start Start)))))
(declare-var x Int)
(declare-var y Int)
(constraint (= (+ (f1 x y) (f1 x y)) (f2 x y)))
(check-synth)
"""

def test_multiple_functions():
    run('multi_ok', FIVE, """(
(define-fun f1 ((p1 Int) (P1 Int)) Int (let ((res P1)) res))
(define-fun f2 ((p1 Int) (P1 Int)) Int (let ((res (+ P1 P1))) res))
)""")
    run('multi_missing', FIVE, '(define-fun f1 ((p1 Int) (P1 Int)) Int P1)', grammar=False, constraints=False)
    run('multi_wrong', FIVE, """(
(define-fun f1 ((p1 Int) (P1 Int)) Int P1)
(define-fun f2 ((p1 Int) (P1 Int)) Int (+ P1 p1))
)""", grammar=True, constraints=False)
    # f2 has no subtraction in its grammar, but the semantics is right
    run('multi_grammar', FIVE, """(
(define-fun f1 ((p1 Int) (P1 Int)) Int P1)
(define-fun f2 ((p1 Int) (P1 Int)) Int (- (+ P1 P1) 0))
)""", grammar=False, constraints=True, note='without the grammar')

# ---------------------------------------------------------------------------

CONSTANT = """
(set-logic LIA)
(synth-fun constant ((x Int)) Int ((Start Int)) ((Start Int (x 0 1 (+ Start Start) (- Start Start)))))
(declare-var x Int)
(declare-var y Int)
(constraint (= (constant x) (constant y)))
(check-synth)
"""

def test_constant_body():
    run('const_body', CONSTANT, '(define-fun constant ((x Int)) Int 1)')
    run('const_param_body', CONSTANT, '(define-fun constant ((x Int)) Int x)', grammar=True, constraints=False)
    run('const_bad', CONSTANT, '(define-fun constant ((x Int)) Int 2)', grammar=False, constraints=True)

# ---------------------------------------------------------------------------

DEFINED = """
(set-logic BV)
(define-fun hd01 ((x (_ BitVec 32))) (_ BitVec 32) (bvand x (bvsub x #x00000001)))
(define-fun dec ((x (_ BitVec 32))) (_ BitVec 32) (bvsub x #x00000001))
(synth-fun f ((x (_ BitVec 32))) (_ BitVec 32)
    ((Start (_ BitVec 32)))
    ((Start (_ BitVec 32) ((bvand Start Start) (dec Start) x #x00000000 #x00000001))))
(declare-var x (_ BitVec 32))
(constraint (= (hd01 x) (f x)))
(check-synth)
"""

TWO_DEFINED = """
(set-logic BV)
(define-fun dec ((x (_ BitVec 8))) (_ BitVec 8) (bvsub x #x01))
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8) ((S (_ BitVec 8))) ((S (_ BitVec 8) ((dec S) x))))
(synth-fun g ((x (_ BitVec 8))) (_ BitVec 8) ((S (_ BitVec 8))) ((S (_ BitVec 8) ((bvadd S S) x #x01))))
(declare-var x (_ BitVec 8))
(constraint (= (bvadd (f x) (g x)) (bvadd x x)))
(check-synth)
"""

def test_mixed_conformance():
    # f follows its grammar (and needs it, dec is defined in the problem); g does not
    run('mixed_conf', TWO_DEFINED, '((define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (dec x)) (define-fun g ((x (_ BitVec 8))) (_ BitVec 8) (bvsub x #xff)))',
        grammar=False, constraints=True, note='without the grammar for g')
    run('mixed_conf_wrong', TWO_DEFINED, '((define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (dec x)) (define-fun g ((x (_ BitVec 8))) (_ BitVec 8) (bvsub x #xfe)))',
        grammar=False, constraints=False)

def test_defined_functions():
    # the grammar uses a function defined in the problem file; its semantics
    # is known from the production
    run('defined_ok', DEFINED, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (bvand x (dec x)))')
    run('defined_wrong', DEFINED, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (bvand x (dec (dec x))))',
        grammar=True, constraints=False)
    # not in the grammar and refers to a defined function: constraints cannot be checked
    run('defined_unparsable', DEFINED, '(define-fun f ((x (_ BitVec 32))) (_ BitVec 32) (bvor x (dec x)))',
        grammar=False, constraints=False, note='constraints not checked')

# ---------------------------------------------------------------------------

NO_GRAMMAR = """
(set-logic LIA)
(synth-fun f ((x Int) (y Int)) Int)
(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (+ x (* 2 y))))
(check-synth)
"""

def test_default_grammar():
    # the default component set of the logic, no constants
    run('default_ok', NO_GRAMMAR, '(define-fun f ((x Int) (y Int)) Int (+ x (+ y y)))')
    run('default_const', NO_GRAMMAR, '(define-fun f ((x Int) (y Int)) Int (+ x (* 2 y)))',
        grammar=False, constraints=True)
    # binary and unary minus: (x + y) - (-y) = x + 2y
    run('default_binary_minus', NO_GRAMMAR, '(define-fun f ((x Int) (y Int)) Int (- (+ x y) (- y)))')

NO_GRAMMAR_DIV = """
(set-logic LIA)
(synth-fun f ((x Int) (y Int)) Int)
(declare-var x Int)
(declare-var y Int)
(constraint (=> (> y 0) (= (f x y) (ite (< x y) (div x y) (mod x y)))))
(check-synth)
"""

def test_default_grammar_operand_order():
    run('default_div', NO_GRAMMAR_DIV, '(define-fun f ((x Int) (y Int)) Int (ite (< x y) (div x y) (mod x y)))')
    run('default_div_swapped', NO_GRAMMAR_DIV, '(define-fun f ((x Int) (y Int)) Int (ite (< y x) (div y x) (mod x y)))',
        grammar=True, constraints=False)

# ---------------------------------------------------------------------------

WEIGHTS = """
(set-logic NIA)
(set-feature :weights true)
(declare-weight numX 0)
(synth-fun f ((x Int)) Int
  ((I Int))
  ((I Int (0 1 (! x :numX 1) (+ I I) (! (* x x) :numX 2)))))
(declare-var x Int)
(constraint (= (_ numX f) 3))
(constraint (>= (f x) (* x x)))
(check-synth)
"""

def test_weights():
    res = run('weights_ok', WEIGHTS, '(define-fun f ((x Int)) Int (+ (* x x) x))', grammar=True, constraints=False)
    # weight is 3, but f(x) >= x*x is violated for negative x
    assert res.constraints[0].valid and not res.constraints[1].valid, res
    res = run('weights_ok2', WEIGHTS, '(define-fun f ((x Int)) Int (+ (+ (* x x) x) (+ 1 1)))', grammar=True, constraints=False)
    assert res.constraints[0].valid and not res.constraints[1].valid, res
    prob = problem(WEIGHTS)
    res = run('weights_wrong', prob, '(define-fun f ((x Int)) Int (+ (* x x) (* x x)))', grammar=True, constraints=False)
    assert not res.constraints[0].valid and res.constraints[1].valid, res
    assert weight_values(res, prob, 'f', 'numX') == [4], res.funcs['f'].prgs[0].weights

def test_weights_without_grammar():
    res = run('weights_no_grammar', WEIGHTS, '(define-fun f ((x Int)) Int (- (* x x) x))',
              grammar=False, constraints=False, note='refer to weights')
    assert res.constraints is None, res

BV_WEIGHTS = """
(set-logic BV)
(set-feature :weights true)
(declare-weight w 0)
(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8) ((S (_ BitVec 8))) ((S (_ BitVec 8) (x #x01 (! (bvadd S S) :w 1)))))
(declare-var x (_ BitVec 8))
(constraint (= (f x) (bvadd x x)))
(check-synth)
"""

def test_weights_bv_without_grammar():
    # the constraints do not refer to the weights, so they can be checked without a derivation
    run('bv_weights_no_grammar', BV_WEIGHTS, '(define-fun f ((x (_ BitVec 8))) (_ BitVec 8) (bvmul x #x02))',
        grammar=False, constraints=True, note='without the grammar')

def unit_cycle(prod):
    return f"""
(set-logic LIA)
(set-feature :weights true)
(declare-weight w 0)
(synth-fun f ((x Int)) Int
  ((I Int) (J Int))
  ((I Int (x (! J :w 1) {prod}))
   (J Int ((! I :w 1) (- I I)))))
(declare-var x Int)
(constraint (= (f x) (* x x)))
(constraint (= (_ w f) 1))
(check-synth)
"""

def test_unit_cycle():
    # I -> J -> I is a cycle of unit productions.  It is cut, and which
    # derivations are found must not depend on the order in which the
    # subterms of the solution are derived.
    for name, prod in [ ('unit_cycle_ji', '(* J I)'), ('unit_cycle_ij', '(* I J)') ]:
        prob = problem(unit_cycle(prod))
        res = run(name, prob, '(define-fun f ((x Int)) Int (* x x))')
        assert weight_values(res, prob, 'f', 'w') == [1], weight_values(res, prob, 'f', 'w')

ANNOTATED_PROD = """
(set-logic LIA)
(set-feature :weights true)
(declare-weight w 0)
(synth-fun f ((x Int)) Int
  ((I Int))
  ((I Int (x 0 (+ (! I :w 1) I) (let ((a I)) (* a a))))))
(declare-var x Int)
(constraint (= (f x) (+ (* x x) (* x x))))
(check-synth)
"""

def test_annotated_and_let_productions():
    # annotations inside a production and lets in productions do not appear in solutions
    run('let_prod', ANNOTATED_PROD, '(define-fun f ((x Int)) Int (+ (* x x) (* x x)))')
    run('let_prod_unequal', ANNOTATED_PROD, '(define-fun f ((x Int)) Int (+ (* x x) (* x 0)))', grammar=False, constraints=False)

AMBIGUOUS_WEIGHTS = """
(set-logic LIA)
(set-feature :weights true)
(declare-weight w 0)
(synth-fun f ((x Int)) Int
  ((I Int))
  ((I Int (x (! x :w 1) (+ I I)))))
(declare-var x Int)
(constraint (= (_ w f) 1))
(constraint (= (f x) (+ x x)))
(check-synth)
"""

def test_ambiguous_weights():
    # x can be derived with weight 0 or 1: (+ x x) has weights 0, 1, 2
    prob = problem(AMBIGUOUS_WEIGHTS)
    res = run('weights_ambiguous', prob, '(define-fun f ((x Int)) Int (+ x x))')
    assert weight_values(res, prob, 'f', 'w') == [0, 1, 2], weight_values(res, prob, 'f', 'w')

UNIT = """
(set-logic LIA)
(set-feature :weights true)
(declare-weight w 0)
(synth-fun f ((x Int)) Int
  ((I Int) (J Int))
  ((I Int (x (! J :w 1) (+ I I)))
   (J Int ((- I I)))))
(declare-var x Int)
(constraint (= (f x) 0))
(constraint (= (_ w f) 1))
(check-synth)
"""

def test_unit_production():
    # (- x x) is derived from I through the unit production J (weight 1)
    res = run('unit_prod', UNIT, '(define-fun f ((x Int)) Int (- x x))')
    prod, _ = res.funcs['f'].prgs[0].insns[-1]
    assert prod.op.name == 'J' and prod.sexpr == '{0}', prod
    run('unit_prod_weight', UNIT, '(define-fun f ((x Int)) Int (+ (- x x) (- x x)))', grammar=True, constraints=False)

def test_weight_assignment_cap():
    prob = problem(AMBIGUOUS_WEIGHTS)
    sol = solution('(define-fun f ((x Int)) Int (+ x x))')
    # only the first derivation (weight 0) is tried
    res = check(prob, sol, max_weight_assignments=1)
    assert not res.satisfies_constraints and any('only 1 of 3' in n for n in res.notes), res
    res = check(prob, sol, max_weight_assignments=2)
    assert res.satisfies_constraints and any('only 2 of 3' in n for n in res.notes), res
    print('  ok  weight_cap')

def test_extra_function():
    run('extra_fun', LIA, '((define-fun f ((x Int) (y Int)) Int (* 2 (+ x y))) (define-fun g ((x Int)) Int x))',
        note='not synth-funs: g')

NO_CONSTRAINTS = """
(set-logic LIA)
(synth-fun f ((x Int)) Int ((I Int)) ((I Int (x 0 1 (+ I I)))))
(check-synth)
"""

def test_no_constraints():
    # every grammar-conforming function is a solution
    run('no_constraints', NO_CONSTRAINTS, '(define-fun f ((x Int)) Int (+ x 1))')
    run('no_constraints_grammar', NO_CONSTRAINTS, '(define-fun f ((x Int)) Int (- x 1))',
        grammar=False, constraints=True, note='without the grammar')

NESTED = """
(set-logic LIA)
(synth-fun f ((x Int)) Int ((I Int)) ((I Int (0 1 x (+ I I)))))
(declare-var x Int)
(constraint (= (f (f x)) (+ x (+ x (+ x x)))))
(check-synth)
"""

def test_nested_applications():
    # the inner application only occurs in the arguments of the outer one
    run('nested_ok', NESTED, '(define-fun f ((x Int)) Int (+ x x))')
    run('nested_wrong', NESTED, '(define-fun f ((x Int)) Int (+ x 1))', grammar=True, constraints=False)

# ---------------------------------------------------------------------------

INV = """
(set-logic LIA)
(synth-inv inv ((x Int) (y Int)))
(define-fun pre ((x Int) (y Int)) Bool (and (= x 0) (= y 0)))
(define-fun trans ((x Int) (y Int) (x! Int) (y! Int)) Bool (and (= x! (+ x 1)) (= y! (+ y 1))))
(define-fun post ((x Int) (y Int)) Bool (= x y))
(inv-constraint inv pre trans post)
(check-synth)
"""

def test_invariant():
    run('inv_ok', INV, '(define-fun inv ((x Int) (y Int)) Bool (= x y))')
    run('inv_wrong', INV, '(define-fun inv ((x Int) (y Int)) Bool (<= x y))', grammar=True, constraints=False)

# ---------------------------------------------------------------------------

ANY_CONST = """
(set-logic LIA)
(synth-fun f ((x Int) (y Int)) Int
  ((I Int) (B Bool))
  ((I Int ((Constant Int) (Variable Int) (+ I I) (ite B I I)))
   (B Bool (true false (<= I I)))))
(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (+ x (+ y 17))))
(check-synth)
"""

def test_any_constant_and_variable():
    run('any_const', ANY_CONST, '(define-fun f ((x Int) (y Int)) Int (+ x (+ y 17)))')
    run('any_const_neg', ANY_CONST, '(define-fun f ((x Int) (y Int)) Int (+ x (+ y (- -17))))')
    run('bool_const', ANY_CONST, '(define-fun f ((x Int) (y Int)) Int (ite true (+ x (+ y 17)) 0))')
    run('bool_const_wrong_sort', ANY_CONST, '(define-fun f ((x Int) (y Int)) Int (ite 1 (+ x (+ y 17)) 0))',
        grammar=False, constraints=False)
    run('any_const_wrong_sort', ANY_CONST, '(define-fun f ((x Int) (y Int)) Int (+ x (+ y 17.0)))',
        grammar=False, constraints=False)

MIXED = """
(set-logic LIA)
(synth-fun f ((x Int) (y Int)) Int ((I Int)) ((I Int (y 0 1 (+ x I)))))
(declare-var x Int)
(declare-var y Int)
(constraint (= (f x y) (+ x (+ x y))))
(check-synth)
"""

def test_parameter_operand():
    # (+ x I) has a parameter operand and a non-terminal operand
    res = run('mixed_ok', MIXED, '(define-fun f ((a Int) (b Int)) Int (+ a (+ a b)))')
    prg = res.funcs['f'].prgs[0]
    assert len(prg.insns) == 2 and all(args[0] == (False, 0) for _, args in prg.insns), prg.insns
    # semantically fine, but the first operand of + has to be x
    run('mixed_wrong_param', MIXED, '(define-fun f ((x Int) (y Int)) Int (+ y (+ x x)))',
        grammar=False, constraints=True, note='without the grammar')

REAL = """
(set-logic NRA)
(synth-fun f ((x Real)) Real ((R Real)) ((R Real (x 0.1 0.5 1 (+ R R) (* R R)))))
(declare-var x Real)
(constraint (= (f x) (+ x 0.1)))
(check-synth)
"""

def test_real():
    run('real_decimal', REAL, '(define-fun f ((x Real)) Real (+ x 0.1))')
    run('real_rational', REAL, '(define-fun f ((x Real)) Real (+ x (/ 1 10)))')
    # the numeral 1 of the grammar denotes the real 1.0
    run('real_int_numeral', REAL, '(define-fun f ((x Real)) Real (+ x 1.0))', grammar=True, constraints=False)
    run('real_wrong_const', REAL, '(define-fun f ((x Real)) Real (+ x 0.2))', grammar=False, constraints=False)
    # an Int numeral in the solution denotes a real for a Real non-terminal
    run('real_int_in_solution', REAL, '(define-fun f ((x Real)) Real (+ x 1))', grammar=True, constraints=False)
    run('int_vs_real', LIA, '(define-fun f ((x Int) (y Int)) Int (+ x 1.5))', grammar=False, constraints=False)

FERMAT = """
(set-logic NIA)
(synth-fun f ((x Int) (y Int) (z Int)) Int ((I Int)) ((I Int (x y z 0 1 (+ I I) (* I I)))))
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(constraint (=> (and (> x 0) (> y 0) (> z 0)) (distinct (f x y z) (* z (* z z)))))
(check-synth)
"""

def test_unknown():
    # z3 cannot decide x^3 + y^3 != z^3 for positive integers
    old = get_param('timeout')
    set_param('timeout', 2000)
    try:
        res = run('unknown', FERMAT, '(define-fun f ((x Int) (y Int) (z Int)) Int (+ (* x (* x x)) (* y (* y y))))',
                  grammar=True, constraints=False)
    finally:
        set_param('timeout', old)
    c = res.constraints[0]
    assert c.result == 'unknown' and c.counterexample is None and 'unknown' in str(res), res

def test_cli():
    import subprocess, tempfile
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    with tempfile.TemporaryDirectory() as d:
        prob, good, bad = (os.path.join(d, n) for n in ('p.sl', 'good.txt', 'bad.txt'))
        open(prob, 'w').write(MAX2)
        open(good, 'w').write('(\n(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))\n)\n')
        open(bad, 'w').write('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) x y))')
        for sol, code, text in [ (good, 0, 'solution is correct'), (bad, 1, 'constraint 0: violated') ]:
            p = subprocess.run([ sys.executable, os.path.join(root, 'sygus.py'), 'check', '-v', prob, sol ],
                               capture_output=True, text=True, cwd=root)
            assert p.returncode == code and text in p.stdout and 'max2:' in p.stdout, (p.returncode, p.stdout, p.stderr)
        open(bad, 'w').write('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) x y)')
        p = subprocess.run([ sys.executable, os.path.join(root, 'sygus.py'), 'check', prob, bad ],
                           capture_output=True, text=True, cwd=root)
        assert p.returncode == 2 and 'unexpected end of file' in p.stderr, (p.returncode, p.stdout, p.stderr)
    print('  ok  cli')

# ---------------------------------------------------------------------------

def main():
    tests = [ (n, f) for n, f in sorted(globals().items()) if n.startswith('test_') and callable(f) ]
    for name, f in tests:
        print(name)
        f()
    print(f'{len(tests)} tests passed')

if __name__ == '__main__':
    main()
