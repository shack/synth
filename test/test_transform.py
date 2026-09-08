"""Tests for the problem transformation layer (synth.transform) and its
bit-vector downscaling instance (synth.transform.bv.BitVecDownscale).

The transform rewrites a problem over n-bit vectors to k < n bits: sorts,
literals (`scale_literal`), operator bodies and preconditions, grammars and
constraints.  Operator bodies may have been simplified by z3 (the SyGuS parser
and `Production._inline` do that), which turns masks, shifts and extensions
into Concat/Extract shapes, so those are covered explicitly.  All checks on
expressions are semantic (z3 equivalence), not syntactic.

Run as a script:

    python test/test_transform.py
"""
import os
import sys
from dataclasses import replace
from io import StringIO

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from z3 import *

from synth.oplib import Bv
from synth.spec import Constraint, Func, Problem, Prg, Production, synth_func_from_ops
from synth.transform import CannotTransform
from synth.transform.bv import BitVecDownscale, downscale_widths, max_bit_width
from util.sygus import SyGuS


BV32, BV8, BV4 = BitVecSort(32), BitVecSort(8), BitVecSort(4)
T8 = BitVecDownscale(target_width=8)
x, y   = BitVecs('x y', 32)
x8, y8 = BitVecs('x~bv8 y~bv8', 8)
VM     = [ (x, x8), (y, y8) ]


def equiv(a, b):
    s = Solver()
    s.add(a != b)
    return s.check() == unsat


def raises(fn):
    try:
        fn()
    except CannotTransform:
        return True
    return False


# --- sorts and literals ----------------------------------------------------

def test_transform_sort():
    assert T8.transform_sort(BV32).eq(BV8)
    assert T8.transform_sort(BitVecSort(16)).eq(BV8)
    for s in (BV8, BV4, BoolSort(), IntSort(), RealSort()):
        assert T8.transform_sort(s).eq(s), s
        assert not T8.changes_sort(s)
    assert raises(lambda: T8.transform_sort(ArraySort(BV32, BV32)))


def test_scale_literal_table():
    table = { 0: 0, 1: 1, 0x7F: 0x7F, 0xFF: 0x03, 0xFFFF: 0x0F, 0xFFFF0000: 0xF0,
              0xFFFFFF00: 0xFC, 0x80000000: 0x80, 0x7FFFFFFF: 0x7F, 0xFFFFFFFF: 0xFF,
              0xFFFFFFFE: 0xFE, 31: 7, 32: 8, 0x10000: 0x10, 0x12345678: 0x78 }
    for u, expected in table.items():
        got = T8.scale_literal(u, 32, 8) % 256
        assert got == expected, f'{u:#x} -> {got:#x}, expected {expected:#x}'
    # 64 -> 16
    t = BitVecDownscale(target_width=16)
    assert t.scale_literal(63, 64, 16) == 15
    assert t.scale_literal(1 << 63, 64, 16) == 1 << 15
    assert t.scale_literal(0xFFFFFFFF, 64, 16) % (1 << 16) == 0xFF
    # transform_value: sort, unchanged sorts untouched
    v = T8.transform_value(BitVecVal(0xFFFF0000, 32))
    assert v.sort().eq(BV8) and v.as_long() == 0xF0
    for lit in (BitVecVal(3, 4), BitVecVal(200, 8), BoolVal(True), IntVal(7)):
        assert T8.transform_value(lit).eq(lit)


def test_lift_value_placeholders():
    assert T8.lift_value(BitVecVal(0xFF, 8), BV32).as_long() == 0xFFFFFFFF
    assert T8.lift_value(BitVecVal(7, 8), BV32).as_long() == 31
    assert T8.lift_value(BitVecVal(0x80, 8), BV32).as_long() == 0x80000000
    assert T8.lift_value(BitVecVal(5, 8), BV8).as_long() == 5
    assert raises(lambda: T8.lift_value(IntVal(1), BV32))


# --- operator library ------------------------------------------------------

def test_bv32_library_downscales_to_bv8():
    for o32, o8 in zip(Bv(32).ops, Bv(8).ops, strict=True):
        f = T8.transform_func(o32)
        assert len(f.inputs) == len(o8.inputs), o32.name
        assert all(i.sort().eq(BV8) for i in f.inputs), o32.name
        assert f.func.sort().eq(BV8), o32.name
        sub = list(zip(f.inputs, o8.inputs))
        assert equiv(substitute(f.func, sub), o8.func), (o32.name, f.func)
        assert equiv(substitute(f.precond, sub), o8.precond), (o32.name, f.precond)


def test_unused_input_keeps_arity_and_order():
    f = Func('snd', y, inputs=(x, y))
    g = T8.transform_func(f)
    assert len(g.inputs) == 2
    assert g.inputs[0].decl().name() == 'x~bv8' and g.inputs[1].decl().name() == 'y~bv8'
    assert equiv(g.func, g.inputs[1])


# --- simplified shapes -----------------------------------------------------

SHAPES = [
    (x & 0xFFFF0000, x8 & 0xF0),
    (x & 0xFF,       x8 & 0x03),
    (x | 0x80000000, x8 | 0x80),
    (x & 0x7FFFFFFF, x8 & 0x7F),
    (LShR(x, 31),    LShR(x8, 7)),
    (x >> 31,        x8 >> 7),
    (ZeroExt(32, x), x8),
    (SignExt(32, x), x8),
    (Concat(x, y),   Concat(Extract(3, 0, x8), Extract(3, 0, y8))),
    (RotateLeft(x, 31), RotateLeft(x8, 7)),
    (Extract(31, 31, x), Extract(7, 7, x8)),
    (Extract(7, 0, x), ZeroExt(6, Extract(1, 0, x8))),
    (x - y,          x8 - y8),
    (UDiv(x, y),     UDiv(x8, y8)),
    (x * 0x80000000, x8 * 0x80),
    (If(UGE(x, y), BitVecVal(1, 32), BitVecVal(0, 32)),
     If(UGE(x8, y8), BitVecVal(1, 8), BitVecVal(0, 8))),
]

def test_simplified_shapes():
    for e, expected in SHAPES:
        for label, ee in (('raw', e), ('simplified', simplify(e))):
            r = T8.transform_expr(ee, VM)
            assert r.sort().eq(T8.transform_sort(e.sort())), (label, e, r)
            assert equiv(r, expected), f'{label} {e} -> {r}, expected {expected}'


def test_shift_by_literal():
    # unsimplified: the small literal is kept; simplified into Concat form:
    # the shift amount is scaled with the width
    assert equiv(T8.transform_expr(x << 3, VM), x8 << 3)
    assert equiv(T8.transform_expr(simplify(x << 3), VM), x8 << 1)
    assert equiv(T8.transform_expr(simplify(LShR(x, 3)), VM), LShR(x8, 1))


def test_width_literal_in_precondition():
    assert equiv(T8.transform_expr(ULE(y, 32), VM), ULE(y8, 8))
    assert equiv(T8.transform_expr(ULE(y, 31), VM), ULE(y8, 7))


# --- width-dependent operators ---------------------------------------------

def test_extract_policy():
    cases = [
        (Extract(31, 31, x), Extract(7, 7, x8)),
        (Extract(31, 16, x), ZeroExt(4, Extract(7, 4, x8))),   # 16-bit result -> 8 bits
        (Extract(15, 0, x),  ZeroExt(4, Extract(3, 0, x8))),
        (Extract(31, 0, x),  x8),
        (Extract(28, 0, x),  ZeroExt(1, Extract(6, 0, x8))),
        (Extract(31, 3, x),  ZeroExt(1, Extract(7, 1, x8))),
        (Extract(0, 0, x),   Extract(0, 0, x8)),
    ]
    for e, expected in cases:
        r = T8.transform_expr(e, VM)
        assert equiv(r, expected), (e, r)
    # Extract on an untouched word is reused unchanged
    z = BitVec('z', 8)
    assert T8.transform_expr(Extract(3, 0, z), []).eq(Extract(3, 0, z))


def test_zero_and_sign_extension():
    z = BitVec('z', 4)
    assert equiv(T8.transform_expr(ZeroExt(28, z), []), ZeroExt(4, z))
    assert equiv(T8.transform_expr(SignExt(28, z), []), SignExt(4, z))
    assert equiv(T8.transform_expr(ZeroExt(4, z), []), ZeroExt(4, z))
    assert equiv(T8.transform_expr(ZeroExt(8, x), VM), x8)
    assert equiv(T8.transform_expr(simplify(SignExt(8, x)), VM), x8)


def test_concat_field_rule():
    # borrowing: the 1-bit top field would vanish
    r = T8.transform_expr(Concat(BitVecVal(1, 1), Extract(30, 0, x)), VM)
    assert equiv(r, x8 | 0x80), r
    # a rotation keeps both halves aligned with the word: rotate right by 3
    # (= left by 29) becomes rotate right by 1
    r = T8.transform_expr(Concat(Extract(2, 0, x), Extract(31, 3, x)), VM)
    assert equiv(r, RotateRight(x8, 1)), r
    # zero extension of a whole word
    assert equiv(T8.transform_expr(Concat(BitVecVal(0, 32), x), VM), x8)
    # too many fields for 8 bits (Concat in the Python API is binary; the
    # simplifier flattens it into the n-ary form that grammars contain)
    nine = simplify(Concat(*[ Extract(i, i, x) for i in range(9) ]))
    assert nine.num_args() == 9
    assert raises(lambda: T8.transform_expr(nine, VM))


def test_repeat():
    z = BitVec('z', 4)
    assert equiv(T8.transform_expr(RepeatBitVec(4, z), []), RepeatBitVec(2, z))
    assert equiv(T8.transform_expr(RepeatBitVec(2, x), VM), x8)
    z3_ = BitVec('z3', 3)
    assert raises(lambda: T8.transform_expr(RepeatBitVec(4, z3_), []))


def test_sort_invariant_over_library_bodies():
    for op in Bv(32).ops:
        for e in (op.func, op.precond, simplify(op.func), simplify(op.precond)):
            vm = [ (i, BitVec(f'{i}~bv8', 8)) for i in op.inputs ]
            r = T8.transform_expr(e, vm)
            assert r.sort().eq(T8.transform_sort(e.sort())), (op.name, e, r)


# --- variables, quantifiers, untouched theories ----------------------------

def test_unmapped_variable_and_quantifier_raise():
    assert raises(lambda: T8.transform_expr(x + 1, []))
    assert raises(lambda: T8.transform_expr(ForAll([x], x == x), []))
    assert raises(lambda: T8.transform_expr(Exists([y], x == y), VM))


def test_unchanged_sorts_pass_through():
    w = Int('weight_w_f')
    b = Bool('b')
    e = And(w <= 3, b, x8 == 3)
    r = T8.transform_expr(e, [])
    assert r.eq(e)
    # mixed: the Int part stays, the BV part is rewritten
    e = And(w <= 3, ULT(x, 5))
    r = T8.transform_expr(e, VM)
    assert equiv(r, And(w <= 3, ULT(x8, 5)))
    assert T8.transform_var(w) is w and T8.transform_var(b) is b


# --- grammar and constraints -----------------------------------------------

def _problem(ops, phi_fn, const_map=None):
    r = BitVec('r', 32)
    func = synth_func_from_ops([BV32], [BV32], ops, const_map=const_map)
    spec = Constraint(phi=phi_fn(r), params=[x],
                      function_applications={ ('f', (x,)): (r,) })
    return Problem(constraints=[spec], funcs={ 'f': func }), r


def test_production_dropped_but_width_kept():
    g   = Function('g', BV32, BV32)
    gop = Func('g', g(x), inputs=(x,))
    problem, r = _problem(Bv(32).ops + [ gop ], lambda r: r == x + 1)
    tp = T8.transform_problem(problem)
    tf = tp.transformed.funcs['f']
    n_orig = sum(len(nt.productions) for nt in problem.funcs['f'].nonterminals.values())
    n_new  = sum(len(nt.productions) for nt in tf.nonterminals.values())
    assert n_new == n_orig - 1
    assert [ p.op.name for p, _ in tp.dropped['f'] ] == [ 'g' ]
    assert 'unsupported operator' in tp.dropped['f'][0][1]
    # every transformed production maps back to an original one
    orig_prods = { p for nt in problem.funcs['f'].nonterminals.values() for p in nt.productions }
    for nt in tf.nonterminals.values():
        for p in nt.productions:
            assert tp.production_map[p] in orig_prods
    # the transformed problem is well-typed
    for c in tp.transformed.constraints:
        c.check_signatures(tp.transformed.funcs)


def test_untransformable_constraint_aborts():
    g = Function('g', BV32, BV32)
    problem, r = _problem(Bv(32).ops, lambda r: r == g(x))
    assert raises(lambda: T8.transform_problem(problem))


def test_all_productions_dropped_aborts():
    g   = Function('g', BV32, BV32)
    gop = Func('g', g(x), inputs=(x,))
    problem, r = _problem([ gop ], lambda r: r == x)
    assert raises(lambda: T8.transform_problem(problem))


def test_not_pertinent_for_narrow_problems():
    problem, _ = _problem(Bv(32).ops, lambda r: r == x)
    assert T8.is_pertinent(problem)
    assert not BitVecDownscale(target_width=32).is_pertinent(problem)
    assert not BitVecDownscale(target_width=64).is_pertinent(problem)


def test_nonterminal_constants():
    consts = { BitVecVal(0xFFFF, 32): None, BitVecVal(0xFFFF0000, 32): None,
               BitVecVal(1, 32): None, BitVecVal(0xFF, 32): 2, BitVecVal(3, 32): 1 }
    problem, _ = _problem([ Bv(32).and_ ], lambda r: r == x, const_map=consts)
    tp = T8.transform_problem(problem)
    nt = tp.transformed.funcs['f'].nonterminals[str(BV32)]
    assert nt.sort.eq(BV8)
    got = { c.as_long(): w for c, w in nt.constants.items() }
    assert got == { 0x0F: None, 0xF0: None, 1: None, 3: 2 }, got
    # unbounded constants stay unbounded
    problem, _ = _problem([ Bv(32).and_ ], lambda r: r == x, const_map=None)
    tp = T8.transform_problem(problem)
    assert tp.transformed.funcs['f'].nonterminals[str(BV32)].constants is None


def test_constraint_translation_nested_applications():
    rf, rg = BitVecs('rf rg', 32)
    f = synth_func_from_ops([BV32], [BV32], [ Bv(32).add_ ])
    c = Constraint(phi=(rf == x + 1), params=(x,),
                   function_applications={ ('g', (x,)): (rg,), ('f', (rg,)): (rf,) })
    problem = Problem(constraints=[c], funcs={ 'f': f, 'g': f })
    tp = T8.transform_problem(problem)
    tc, = tp.transformed.constraints
    assert [ p.sort().eq(BV8) for p in tc.params ] == [ True ]
    assert tc.params[0].decl().name() == 'x~bv8'
    (name_g, ins_g), (name_f, ins_f) = tc.function_applications.keys()
    outs_g, outs_f = tc.function_applications.values()
    assert (name_g, name_f) == ('g', 'f')
    assert ins_g[0].eq(tc.params[0])
    assert ins_f[0].eq(outs_g[0])          # f is applied to g's output
    assert outs_f[0].sort().eq(BV8) and outs_f[0].decl().name() == 'rf~bv8'
    assert equiv(tc.phi, outs_f[0] == tc.params[0] + 1)
    # the constraint and function signatures agree
    tc.check_signatures(tp.transformed.funcs)


def test_shared_params_across_constraints():
    r1, r2 = BitVecs('r1 r2', 32)
    f = synth_func_from_ops([BV32], [BV32], [ Bv(32).add_ ])
    c1 = Constraint(phi=ULE(r1, x), params=(x,), function_applications={ ('f', (x,)): (r1,) })
    c2 = Constraint(phi=UGE(r2, x), params=(x,), function_applications={ ('f', (x,)): (r2,) })
    problem = Problem(constraints=[c1, c2], funcs={ 'f': f })
    tp = T8.transform_problem(problem)
    t1, t2 = tp.transformed.constraints
    assert t1.params[0].eq(t2.params[0])
    fused, = tp.transformed.fuse_constraints().constraints
    assert len(fused.params) == 1 and len(fused.function_applications) == 1


def test_inv_constraints_keep_shared_bool_outputs():
    pre_b, inv_b = Bools('pre inv')
    fpre = synth_func_from_ops([BV32], [BoolSort()], [ Bv(32).ult_, Bv(32).uge_ ])
    finv = synth_func_from_ops([BV32], [BoolSort()], [ Bv(32).ult_, Bv(32).uge_ ])
    c1 = Constraint(phi=Implies(pre_b, inv_b), params=(x,),
                    function_applications={ ('pre', (x,)): (pre_b,), ('inv', (x,)): (inv_b,) })
    c2 = Constraint(phi=Or(inv_b, Not(inv_b)), params=(x,),
                    function_applications={ ('inv', (x,)): (inv_b,) })
    problem = Problem(constraints=[c1, c2], funcs={ 'pre': fpre, 'inv': finv })
    tp = T8.transform_problem(problem)
    t1, t2 = tp.transformed.constraints
    assert t1.function_applications[('inv', t1.params)][0] is inv_b
    assert t2.function_applications[('inv', t2.params)][0] is inv_b


def test_lift_prgs():
    problem, r = _problem([ Bv(32).add_, Bv(32).and_ ], lambda r: r == x + 1)
    tp = T8.transform_problem(problem)
    tf = tp.transformed.funcs['f']
    t_add = next(p for p in tf.nonterminals[str(BV32)].productions if p.op.name == 'add')
    o_add = tp.production_map[t_add]
    nop   = Production(Func('$nop', Const('$nop_y', BV8), inputs=()), (), (), '', {})
    prg   = Prg(tf, [ (t_add, [ (False, 0), (True, BitVecVal(0xF, 8)) ]), (nop, []) ],
                [ (True, BitVecVal(0x80, 8)) ])
    lifted = tp.lift_prgs({ 'f': prg })['f']
    assert lifted.insns[0][0] is o_add
    assert lifted.insns[1][0] is nop
    (_, (is_c, v)) = lifted.insns[0][1]
    assert is_c and v.sort().eq(BV32)
    assert lifted.outputs[0][1].sort().eq(BV32) and lifted.outputs[0][1].as_long() == 0x80000000
    # the lifted program is well-sorted: its clauses can be built at 32 bits
    clauses = list(lifted.eval_clauses([x], [r]))
    assert len(clauses) == 3


def test_optimized_sygus_grammar_transforms_without_drops():
    src = """
(set-logic BV)
(synth-fun f ((x (_ BitVec 32))) (_ BitVec 32)
  ((Start (_ BitVec 32)) (C (_ BitVec 32)))
  ((Start (_ BitVec 32) (x (bvand Start C) (bvor Start C) (bvshl Start C) (bvlshr Start C)))
   (C (_ BitVec 32) (#x00000001 #xffff0000 #x000000ff #x80000000))))
(declare-var x (_ BitVec 32))
(constraint (= (f x) (bvand x #xffff0000)))
(check-synth)
"""
    p = SyGuS('test').read_problem(StringIO(src))
    p = replace(p, funcs={ n: f.optimize_grammar() for n, f in p.funcs.items() })
    # the inlined bodies are simplified into Concat/Extract shapes
    assert all(pr.n_inlined_consts == 1 for pr in p.funcs['f'].nonterminals['Start'].productions)
    tp = T8.transform_problem(p)
    assert tp.dropped == {}, tp.dropped
    tf = tp.transformed.funcs['f']
    assert all(pr.op.func.sort().eq(BV8) for pr in tf.nonterminals['Start'].productions)
    # the spec was rewritten to 8 bits as well
    tc, = tp.transformed.constraints
    (_, ins), outs = next(iter(tc.function_applications.items()))
    assert equiv(tc.phi, outs[0] == ins[0] & 0xF0)


def test_ladder():
    assert downscale_widths(32) == [ 4, 8, 16 ]
    assert downscale_widths(64) == [ 4, 8, 16, 32 ]
    assert downscale_widths(8)  == [ 4 ]
    assert downscale_widths(12) == [ 4, 8 ]
    assert downscale_widths(4)  == []
    assert downscale_widths(0)  == []
    # max_bit_width sees widths that only occur in constraints/signatures
    r = BitVec('r', 8)
    func = synth_func_from_ops([BV8], [BV8], [ Bv(8).add_ ])
    z = BitVec('z', 16)
    spec = Constraint(phi=(ZeroExt(8, r) == z), params=[z],
                      function_applications={ ('f', (Extract(7, 0, z),)): (r,) })
    problem = Problem(constraints=[spec], funcs={ 'f': func })
    assert problem.get_max_used_bit_width() == 8
    assert max_bit_width(problem) == 16
    # not a bit-vector problem
    i = Int('i')
    problem = Problem(constraints=[Constraint(phi=(i == i), params=[i], function_applications={})],
                      funcs={})
    assert max_bit_width(problem) == 0


TESTS = [ v for k, v in sorted(globals().items()) if k.startswith('test_') ]


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
