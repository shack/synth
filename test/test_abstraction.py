"""Tests for synth.abstraction.NLZLSBAbstraction.

The centerpiece is `test_abstract_expr_sound_for_every_op`, which verifies
that the abstract interpreter (`NLZLSBAbstraction.abstract_expr`) is a sound
over-approximation for every operator it handles. Each soundness query
asserts

    gamma(x_i, a_i)  ⇒  gamma(op(x_i...), abstract_expr(op_expr, {x_i: a_i}))

is valid (i.e. the negation is unsat). Run as a script:

    python test/test_abstraction.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from z3 import *
from synth.abstraction.bv import NLZLSBAbstraction
from synth.spec import Func
from synth.abstraction import CannotAbstract


# Small enough that all soundness queries solve quickly.
K, L = 4, 4
W = 1 << K
ABS = NLZLSBAbstraction(log2_concrete_bit_width=K, lower_bits_width=L)
SORT = BitVecSort(W)


def fresh_abs(prefix):
    """Fresh abstract triple (nlz, top, lsb)."""
    return (BitVec(f'{prefix}_nlz', K + 1),
            BitVec(f'{prefix}_top', 1),
            BitVec(f'{prefix}_lsb', L))


def assert_unsat(s, msg):
    res = s.check()
    if res == sat:
        raise AssertionError(f"{msg}\n  counterexample: {s.model()}")
    if res != unsat:
        raise AssertionError(f"{msg}: solver returned {res}")


def as_bv(e):
    """Coerce a Bool expression to its 0/1 BV encoding; pass BVs through."""
    if is_bool(e):
        return If(e, BitVecVal(1, W), BitVecVal(0, W))
    return e


def soundness_query(expr, abs_inputs):
    """Solver populated with the negated soundness implication for `expr`."""
    out = ABS.abstract_expr(expr, abs_inputs, set())
    s = Solver()
    for x, a in abs_inputs.items():
        s.add(ABS.gamma(x, ABS.pack(a)))
    s.add(Not(ABS.gamma(as_bv(expr), ABS.pack(out))))
    return s


# ---------------------------------------------------------------------------
# 1. beta / gamma consistency

def test_beta_gamma_consistency():
    assert ABS.check_beta_gamma_consistency(SORT)


def test_pack_unpack_roundtrip():
    b = ABS.beta(BitVec('c', W))
    triple = ABS.unpack(b)
    assert simplify(ABS.pack(triple) == b)


# ---------------------------------------------------------------------------
# 2. encoding: nlz=W means "exactly zero"; nlz=0 means "no info"

def test_nlz_full_forces_zero():
    abs_full = ABS.pack((BitVecVal(W, K + 1), BitVecVal(0, 1), BitVecVal(0, L)))
    c = BitVec('c', W)
    s = Solver()
    s.add(ABS.gamma(c, abs_full))
    s.add(c != 0)
    assert_unsat(s, "nlz=W did not force c == 0")


def test_nlz_zero_admits_anything():
    abs_none = ABS.pack((BitVecVal(0, K + 1), BitVecVal(1, 1), BitVecVal(0, L)))
    c = BitVec('c', W)
    s = Solver()
    s.add(Not(ABS.gamma(c, abs_none)))
    assert_unsat(s, "nlz=0,top=1 did not admit every concrete value")


def test_nlz_full_distinct_from_nlz_zero():
    abs_full = ABS.pack((BitVecVal(W, K + 1), BitVecVal(0, 1), BitVecVal(0, L)))
    abs_none = ABS.pack((BitVecVal(0, K + 1), BitVecVal(1, 1), BitVecVal(0, L)))
    c = BitVec('c', W)
    s = Solver()
    s.add(ABS.gamma(c, abs_none))
    s.add(Not(ABS.gamma(c, abs_full)))
    assert s.check() == sat, "nlz=W and nlz=0 collapsed to the same set"


# ---------------------------------------------------------------------------
# 3. abstract_expr soundness for every operator it abstracts

def _operator_cases():
    """Yield (name, expr, abs_inputs) for every operator `abstract_expr`
    handles. Covers every Z3_OP_* branch in `abstract_expr.go`, plus the
    constant-folding path and the TOP fallback for unsupported operators."""
    x, y, z       = BitVec('x', W), BitVec('y', W), BitVec('z', W)
    a_x, a_y, a_z = fresh_abs('x'), fresh_abs('y'), fresh_abs('z')
    in2  = {x: a_x, y: a_y}
    in3  = {x: a_x, y: a_y, z: a_z}
    cond = Bool('cond')          # opaque bool, abstracted to TOP

    yield 'bvnot',         ~x,                 {x: a_x}
    yield 'bvneg',         -x,                 {x: a_x}
    yield 'bvand',         x & y,              in2
    yield 'bvor',          x | y,              in2
    yield 'bvxor',         x ^ y,              in2
    yield 'bvadd',         x + y,              in2
    yield 'bvsub',         x - y,              in2
    yield 'bvmul',         x * y,              in2
    yield 'bvshl',         x << y,             in2
    yield 'bvlshr',        LShR(x, y),         in2
    yield 'bvudiv',        UDiv(x, y),         in2
    # division corner cases worth exercising explicitly:
    yield 'bvudiv_by_one',  UDiv(x, BitVecVal(1, W)), {x: a_x}
    yield 'bvudiv_by_zero', UDiv(x, BitVecVal(0, W)), {x: a_x}
    yield 'bvudiv_zero_x',  UDiv(BitVecVal(0, W), y), {y: a_y}
    yield 'bveq',          x == y,             in2   # Bool: as_bv wraps with If
    yield 'bvite_opaque',  If(cond, x, y),     in2
    yield 'bvite_true',    If(BoolVal(True),  x, y), in2
    yield 'bvite_false',   If(BoolVal(False), x, y), in2
    yield 'bvite_via_eq',  If(x == y, z, BitVecVal(0, W)), in3
    # n-ary fold over BADD/BMUL/BAND/BOR/BXOR (>2 args exercises the `fold` helper).
    yield 'bvadd_3ary',    x + y + z,          in3
    yield 'bvmul_3ary',    x * y * z,          in3
    yield 'bvand_3ary',    x & y & z,          in3
    yield 'bvor_3ary',     x | y | z,          in3
    yield 'bvxor_3ary',    x ^ y ^ z,          in3
    # Constant folding via abs_const (the `is_bv_value` branch).
    yield 'bvconst_zero',  BitVecVal(0, W) + x, {x: a_x}
    yield 'bvconst_one',   BitVecVal(1, W) + x, {x: a_x}
    yield 'bvconst_top',   BitVecVal(0xAB, W) ^ x, {x: a_x}
    # Unsupported op (URem) hits the TOP fallback — still must be sound.
    yield 'top_fallback',  URem(x, y),          in2


def test_abstract_expr_sound_for_every_op():
    """Every operator that `abstract_expr` abstracts must yield a sound
    over-approximation. Failures are reported with the offending operator
    name and counterexample."""
    failures = []
    for name, expr, abs_inputs in _operator_cases():
        s = soundness_query(expr, abs_inputs)
        res = s.check()
        if res == sat:
            failures.append(f"{name}: unsound (counterexample: {s.model()})")
        elif res != unsat:
            failures.append(f"{name}: solver returned {res}")
    assert not failures, "unsound operators:\n  " + "\n  ".join(failures)


def test_composite_expression_sound():
    """Recursive walk: (x + y) & (x ^ 0xF) — operators compose soundly."""
    x, y     = BitVec('x', W), BitVec('y', W)
    a_x, a_y = fresh_abs('x'), fresh_abs('y')
    expr     = (x + y) & (x ^ BitVecVal(0xF, W))
    assert_unsat(soundness_query(expr, {x: a_x, y: a_y}),
                 "(x+y)&(x^0xF): abstract_expr is unsound")


def test_constant_folding_matches_beta():
    """abstract_expr on a BV constant matches unpack(beta(v))."""
    for v in [0, 1, 5, 0xF, 0xAB, (1 << (W - 1)), (1 << W) - 1]:
        const = BitVecVal(v, W)
        out   = ABS.abstract_expr(const, {}, set())
        want  = ABS.unpack(simplify(ABS.beta(const)))
        for o, w in zip(out, want):
            assert simplify(o).eq(simplify(w)), \
                f"abstract_expr({v}): {simplify(o)} != {simplify(w)}"


# ---------------------------------------------------------------------------
# 4. precision: zero propagates exactly through ops we special-case

def _eq_triples(a, b):
    return And(*[simplify(x) == simplify(y) for x, y in zip(a, b)])


def test_zero_add_propagates():
    """0 + y must yield exactly y's abstraction."""
    y, a_y = BitVec('y', W), fresh_abs('y')
    out    = ABS.abstract_expr(BitVecVal(0, W) + y, {y: a_y}, set())
    s = Solver()
    s.add(Not(_eq_triples(out, a_y)))
    assert_unsat(s, "0 + y did not propagate y's abstraction")


def test_zero_mul_yields_zero():
    """0 * y must collapse to the precise abstraction of zero."""
    y, a_y = BitVec('y', W), fresh_abs('y')
    out    = ABS.abstract_expr(BitVecVal(0, W) * y, {y: a_y}, set())
    zero_abs = (BitVecVal(W, K + 1), BitVecVal(0, 1), BitVecVal(0, L))
    s = Solver()
    s.add(Not(_eq_triples(out, zero_abs)))
    assert_unsat(s, "0 * y did not collapse to zero")


def test_zero_shl_yields_zero():
    """0 << y must collapse to zero even if y's abstraction is unknown."""
    y, a_y = BitVec('y', W), fresh_abs('y')
    out    = ABS.abstract_expr(BitVecVal(0, W) << y, {y: a_y}, set())
    zero_abs = (BitVecVal(W, K + 1), BitVecVal(0, 1), BitVecVal(0, L))
    s = Solver()
    s.add(Not(_eq_triples(out, zero_abs)))
    assert_unsat(s, "0 << y did not collapse to zero")


def test_neg_zero_is_zero():
    out = ABS.abstract_expr(-BitVecVal(0, W), {}, set())
    zero_abs = ABS.unpack(simplify(ABS.beta(BitVecVal(0, W))))
    for o, z in zip(out, zero_abs):
        assert simplify(o).eq(simplify(z)), f"-0: {simplify(o)} != {simplify(z)}"


# ---------------------------------------------------------------------------
# abstract_func: an operand wider than the packed width is abstracted

def test_abstract_func_succeeds_on_packable_operand():
    wide = BitVecSort(W)                        # W > packed width -> abstracted
    x = Const('x', wide)
    f = Func('id', x, inputs=(x,))
    af = ABS.abstract_func(f, set())            # must not raise
    assert af.out_type.size() == ABS.get_width(), \
        "abstract func output is not in packed form"


# ---------------------------------------------------------------------------

TESTS = [v for k, v in sorted(globals().items()) if k.startswith('test_')]


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
