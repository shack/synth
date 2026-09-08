"""Bit-vector downscaling.

`BitVecDownscale(k)` rewrites every bit vector wider than `k` bits to `k`
bits.  Operators are rebuilt over the narrower sorts, literals are scaled
with a heuristic that preserves their role (small values, width constants,
sign bit, masks, powers of two), and the bit positions of extraction and
concatenation are mapped proportionally so that operator bodies that z3's
simplifier has turned into `Concat`/`Extract` form (masks, shifts, extensions)
keep their shape.
"""
import math
import operator
from dataclasses import dataclass
from typing import ClassVar

from z3 import *

from synth.spec import Problem
from synth.transform import CannotTransform, Handler, ProblemTransform, apply_fn, fold_fn
from synth.util import get_max_used_bit_width


# --- bit positions ---------------------------------------------------------

def pos(p: int, n: int, k: int) -> int:
    """Map bit boundary `p` (0 <= p <= n) of an n-bit word to the k-bit word.
       Monotone with pos(0) = 0 and pos(n) = k."""
    return (p * k + n // 2) // n

def bit(i: int, n: int, k: int) -> int:
    """Map bit index `i` (0 <= i < n) of an n-bit word to the k-bit word.
       bit(n - 1) = k - 1."""
    return max(pos(i + 1, n, k) - 1, 0)

def fit(c: ExprRef, w: int) -> ExprRef:
    """`c` truncated or zero-extended to `w` bits."""
    cw = c.sort().size()
    if cw == w:
        return c
    return Extract(w - 1, 0, c) if cw > w else ZeroExt(w - cw, c)

def concat(parts: list[ExprRef]) -> ExprRef:
    return parts[0] if len(parts) == 1 else Concat(*parts)


# --- handlers of width-dependent operators ---------------------------------
# They are only invoked when the sort of some operand or of the result changes.

def _extract(ctx, e, cs):
    hi, lo = e.params()
    x,     = cs
    n, kx  = e.arg(0).sort().size(), x.sort().size()
    hi2    = bit(hi, n, kx)
    lo2    = min(pos(lo, n, kx), hi2)
    return fit(Extract(hi2, lo2, x), ctx.t.transform_sort(e.sort()).size())

def _ext(mk):
    def h(ctx, e, cs):
        x, = cs
        m  = ctx.t.transform_sort(e.sort()).size() - x.sort().size()
        if m < 0:
            raise CannotTransform(e, 'extension result narrower than operand')
        return x if m == 0 else mk(m, x)
    return h

def _is_top_bit_of(a, z):
    t = z.sort().size() - 1
    return a.decl().kind() == Z3_OP_EXTRACT and a.params() == [t, t] and a.arg(0).eq(z)

def _concat(ctx, e, cs):
    t    = ctx.t
    n    = e.sort().size()
    K    = t.transform_sort(e.sort()).size()
    args = e.children()
    # zero extension: leading zero literals in front of whole values (not
    # in front of a field extracted from a wider word: that is a mask)
    i = 0
    while i < len(args) and is_bv_value(args[i]) and args[i].as_long() == 0:
        i += 1
    def is_field(a):
        return a.decl().kind() == Z3_OP_EXTRACT and t.changes_sort(a.arg(0).sort())
    if 0 < i < len(args) and not any(is_field(a) for a in args[i:]):
        return fit(concat(cs[i:]), K)
    # sign extension: copies of the top bit of the last child
    if all(_is_top_bit_of(a, args[-1]) for a in args[:-1]):
        return _ext(SignExt)(ctx, e, [ cs[-1] ])
    # general case: map the field boundaries proportionally
    widths = [ a.sort().size() for a in args ]
    bounds = []
    acc    = 0
    for w in reversed(widths):
        bounds.append((acc, acc + w))
        acc += w
    bounds.reverse()
    new_w = [ pos(hi, n, K) - pos(lo, n, K) for lo, hi in bounds ]
    # fields that vanish borrow a bit from the widest field
    while 0 in new_w:
        j      = new_w.index(0)
        widest = max(range(len(new_w)), key=lambda i: new_w[i])
        if new_w[widest] <= 1:
            raise CannotTransform(e, 'too many concat fields')
        new_w[widest] -= 1
        new_w[j]      += 1
    assert sum(new_w) == K
    parts = []
    for a, c, w in zip(args, cs, new_w):
        if is_field(a):
            # keep fields extracted from the same word aligned with each
            # other: a field that touches the bottom (top) of the word stays
            # at the bottom (top), e.g. the two halves of a rotation
            hi, lo = a.params()
            z      = ctx.go(a.arg(0))
            nz, kz = a.arg(0).sort().size(), z.sort().size()
            if w > kz:
                raise CannotTransform(e, 'concat field wider than its word')
            if lo == 0:
                lo2 = 0
            elif hi == nz - 1:
                lo2 = kz - w
            else:
                lo2 = min(pos(lo, nz, kz), kz - w)
            parts.append(Extract(lo2 + w - 1, lo2, z))
        else:
            parts.append(fit(c, w))
    return concat(parts)

def _repeat(ctx, e, cs):
    x, = cs
    K  = ctx.t.transform_sort(e.sort()).size()
    w  = x.sort().size()
    if K % w != 0:
        raise CannotTransform(e, 'repeat count does not divide the width')
    return x if K == w else RepeatBitVec(K // w, x)

def _rotate(mk):
    def h(ctx, e, cs):
        a, = e.params()
        x, = cs
        n, k = e.arg(0).sort().size(), x.sort().size()
        return mk(x, ctx.t.scale_literal(a, n, k) % k)
    return h

def _bit2bool(ctx, e, cs):
    i, = e.params()
    x, = cs
    b  = bit(i, e.arg(0).sort().size(), x.sort().size())
    return Extract(b, b, x) == BitVecVal(1, 1)

def _int2bv(ctx, e, cs):
    return Int2BV(cs[0], ctx.t.transform_sort(e.sort()).size())


_BV_OPS: dict[int, Handler] = {
    Z3_OP_BADD:  fold_fn(operator.add),
    Z3_OP_BSUB:  fold_fn(operator.sub),
    Z3_OP_BMUL:  fold_fn(operator.mul),
    Z3_OP_BNEG:  apply_fn(operator.neg),
    Z3_OP_BNOT:  apply_fn(operator.invert),
    Z3_OP_BAND:  fold_fn(operator.and_),
    Z3_OP_BOR:   fold_fn(operator.or_),
    Z3_OP_BXOR:  fold_fn(operator.xor),
    Z3_OP_BNAND: lambda ctx, e, cs: ~(cs[0] & cs[1]),
    Z3_OP_BNOR:  lambda ctx, e, cs: ~(cs[0] | cs[1]),
    Z3_OP_BXNOR: lambda ctx, e, cs: ~(cs[0] ^ cs[1]),
    # z3's simplifier produces the _I variants (division with the
    # SMT-LIB semantics for a zero divisor)
    Z3_OP_BSDIV:   apply_fn(operator.truediv),
    Z3_OP_BSDIV_I: apply_fn(operator.truediv),
    Z3_OP_BUDIV:   apply_fn(UDiv),
    Z3_OP_BUDIV_I: apply_fn(UDiv),
    Z3_OP_BSREM:   apply_fn(SRem),
    Z3_OP_BSREM_I: apply_fn(SRem),
    Z3_OP_BUREM:   apply_fn(URem),
    Z3_OP_BUREM_I: apply_fn(URem),
    Z3_OP_BSMOD:   apply_fn(operator.mod),
    Z3_OP_BSMOD_I: apply_fn(operator.mod),
    Z3_OP_BSHL:  apply_fn(operator.lshift),
    Z3_OP_BLSHR: apply_fn(LShR),
    Z3_OP_BASHR: apply_fn(operator.rshift),
    Z3_OP_ULEQ:  apply_fn(ULE),
    Z3_OP_ULT:   apply_fn(ULT),
    Z3_OP_UGEQ:  apply_fn(UGE),
    Z3_OP_UGT:   apply_fn(UGT),
    Z3_OP_SLEQ:  apply_fn(operator.le),
    Z3_OP_SLT:   apply_fn(operator.lt),
    Z3_OP_SGEQ:  apply_fn(operator.ge),
    Z3_OP_SGT:   apply_fn(operator.gt),
    Z3_OP_BREDOR:  apply_fn(BVRedOr),
    Z3_OP_BREDAND: apply_fn(BVRedAnd),
    Z3_OP_BCOMP:   lambda ctx, e, cs: If(cs[0] == cs[1], BitVecVal(1, 1), BitVecVal(0, 1)),
    Z3_OP_EXT_ROTATE_LEFT:  apply_fn(RotateLeft),
    Z3_OP_EXT_ROTATE_RIGHT: apply_fn(RotateRight),
    Z3_OP_BSMUL_NO_OVFL: lambda ctx, e, cs: BVMulNoOverflow(cs[0], cs[1], True),
    Z3_OP_BUMUL_NO_OVFL: lambda ctx, e, cs: BVMulNoOverflow(cs[0], cs[1], False),
    Z3_OP_BSMUL_NO_UDFL: apply_fn(BVMulNoUnderflow),
    Z3_OP_BV2INT:  apply_fn(BV2Int),
    Z3_OP_SBV2INT: lambda ctx, e, cs: BV2Int(cs[0], is_signed=True),
    Z3_OP_INT2BV:  _int2bv,
    # width dependent
    Z3_OP_EXTRACT:      _extract,
    Z3_OP_ZERO_EXT:     _ext(ZeroExt),
    Z3_OP_SIGN_EXT:     _ext(SignExt),
    Z3_OP_CONCAT:       _concat,
    Z3_OP_REPEAT:       _repeat,
    Z3_OP_ROTATE_LEFT:  _rotate(RotateLeft),
    Z3_OP_ROTATE_RIGHT: _rotate(RotateRight),
    Z3_OP_BIT2BOOL:     _bit2bool,
}


@dataclass(frozen=True)
class BitVecDownscale(ProblemTransform):
    """Rewrite all bit vectors wider than `target_width` to `target_width` bits."""

    target_width: int

    OPS: ClassVar[dict[int, Handler]] = ProblemTransform.OPS | _BV_OPS

    def __post_init__(self):
        assert self.target_width >= 1, 'target width must be positive'

    def __str__(self):
        return f'downscale({self.target_width})'

    @property
    def suffix(self):
        return f'~bv{self.target_width}'

    def transform_sort(self, s: SortRef) -> SortRef:
        if is_bv_sort(s):
            return BitVecSort(self.target_width) if s.size() > self.target_width else s
        if s.kind() == Z3_ARRAY_SORT:
            raise CannotTransform(s, 'array sort')
        return s

    def transform_value(self, v: ExprRef) -> ExprRef:
        if not self.changes_sort(v.sort()):
            return v
        if not is_bv_value(v):
            raise CannotTransform(v, 'not a bit-vector literal')
        n, k = v.sort().size(), self.target_width
        return BitVecVal(self.scale_literal(v.as_long(), n, k) % (1 << k), k)

    def lift_value(self, v: ExprRef, sort: SortRef) -> ExprRef:
        if v.sort().eq(sort):
            return v
        if not (is_bv_sort(sort) and is_bv_value(v)):
            raise CannotTransform(v, f'cannot lift value to sort {sort}')
        n, k = sort.size(), v.sort().size()
        return BitVecVal(self.lift_literal(v.as_long(), k, n) % (1 << n), n)

    def scale_literal(self, u: int, n: int, k: int) -> int:
        """Value of the n-bit literal `u` (unsigned) at width k.  The result
           is reduced modulo 2^k by the caller.  Heuristic; the first
           matching rule wins."""
        full = (1 << k) - 1
        # width constants (shift preconditions, x >> (n-1))
        if u == n:
            return k
        if u == n - 1:
            return k - 1
        # values that fit the signed k-bit range are kept (0, 1, -1, -2, ...)
        s = u - (1 << n) if u >> (n - 1) else u
        if -(1 << (k - 1)) <= s < (1 << (k - 1)):
            return s
        # the sign bit and the largest positive value
        if u == 1 << (n - 1):
            return 1 << (k - 1)
        if u == (1 << (n - 1)) - 1:
            return (1 << (k - 1)) - 1
        # masks: keep them proper masks so that and/or stay meaningful
        def clamp(j):
            return max(1, min(k - 1, j))
        if u & (u + 1) == 0:                          # low mask 2^j - 1
            return (1 << clamp(pos(u.bit_length(), n, k))) - 1
        inv = ((1 << n) - 1) ^ u
        if inv != 0 and inv & (inv + 1) == 0:         # high mask: ~u is a low mask
            return full ^ ((1 << clamp(pos(inv.bit_length(), n, k))) - 1)
        if u & (u - 1) == 0:                          # power of two
            return 1 << min(pos(u.bit_length() - 1, n, k), k - 1)
        return u % (1 << k)

    def lift_literal(self, v: int, k: int, n: int) -> int:
        """Placeholder n-bit value for the k-bit literal `v`.  Best effort
           inverse of `scale_literal`; the constants are re-synthesized anyway."""
        if v == k:
            return n
        if v == k - 1:
            return n - 1
        if v == 1 << (k - 1):
            return 1 << (n - 1)
        if v == (1 << (k - 1)) - 1:
            return (1 << (n - 1)) - 1
        return v - (1 << k) if v >> (k - 1) else v   # sign extension


def max_bit_width(problem: Problem) -> int:
    """Widest bit-vector sort used anywhere in `problem`: signatures,
       non-terminals, operator bodies and preconditions, constraints.
       0 if the problem uses no bit vectors."""
    def sort_width(s):
        return s.size() if is_bv_sort(s) else 0
    res = 0
    for f in problem.funcs.values():
        res = max([ res ] + [ sort_width(s) for _, s in f.inputs + f.outputs ])
        for nt in f.nonterminals.values():
            res = max(res, sort_width(nt.sort))
            for c in nt.constants or ():
                res = max(res, sort_width(c.sort()))
            for p in nt.productions:
                res = max(res, get_max_used_bit_width(p.op.func),
                               get_max_used_bit_width(p.op.precond))
    for c in problem.constraints:
        res = max(res, get_max_used_bit_width(c.phi))
        res = max([ res ] + [ sort_width(p.sort()) for p in c.params ])
        for (_, ins), outs in c.function_applications.items():
            res = max([ res ] + [ get_max_used_bit_width(i) for i in ins ]
                              + [ sort_width(o.sort()) for o in outs ])
    return res

def downscale_widths(n: int, min_log2: int = 2) -> list[int]:
    """Default target widths for a problem of bit width `n`: the powers of
       two from 2^min_log2 up to the largest one below `n`; e.g. [4, 8, 16]
       for n = 32 and [] for n <= 4."""
    if n <= 0:
        return []
    return [ 2 ** i for i in range(min_log2, math.ceil(math.log2(n))) ]
