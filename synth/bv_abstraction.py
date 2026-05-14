from z3 import *
from synth.abstraction import *
from synth.util import bv_nlz, free_vars, get_max_used_bit_width

class BitVectorAbstraction(Abstraction):
    def get_width(self) -> int: ...

    def _name(self) -> str: ...

    @final
    def __str__(self):
        return f'{self._name()}({self.get_width()})'

    def get_sort_for(self, s: SortRef) -> SortRef:
        # Bools are abstracted to the same packed BV (as their 0/1 encoding),
        # matching how the transformer treats Bool sub-expressions.
        is_suitable = is_bv_sort(s) and s.size() > self.get_width()
        return BitVecSort(self.get_width()) if is_suitable else s

class PackedBitVectorAbstraction(BitVectorAbstraction):
    def get_widths(self) -> Iterable[int]: ...

    def get_width(self) -> int:
        return sum(self.get_widths())

    def pack(self, parts: Iterable[ExprRef]) -> ExprRef:
        parts = tuple(parts)
        assert all(is_bv_sort(e.sort()) for e in parts)
        assert sum(e.sort().size() for e in parts) == sum(self.get_widths())
        return Concat(parts)

    def unpack(self, abstract: ExprRef) -> tuple[ExprRef]:
        end = abstract.sort().size()
        assert end == sum(self.get_widths())
        res = []
        for w in self.get_widths():
            res.append(Extract(end - 1, end - w, abstract))
            end -= w
        assert end == 0, f'widths {tuple(self.get_widths())} do not cover {abstract.sort().size()} bits'
        return tuple(res)

    def abstract_expr(self, e: ExprRef, inputs: dict[ExprRef, tuple], topped: set[ExprRef]) -> tuple: ...

    @final
    def abstract_func(self, f: Func, topped: set[ExprRef]) -> Func:
        new_inputs = tuple(self.get_const_for(t) for t in f.inputs)
        inp        = { old: self.unpack(new) for old, new in zip(f.inputs, new_inputs) }
        func       = self.abstract_expr(f.func, inp, topped)
        return Func(name=f'{f.name}#',
                    inputs=new_inputs,
                    phi=self.pack(func))

@dataclass(frozen=True)
class ToppedBitVectorAbstraction(BitVectorAbstraction):
    abstraction: BitVectorAbstraction

    def get_width(self):
        return self.abstraction.get_width() + 1

    def abstracts_from(self, s):
        return super().abstracts_from(s)

    def __str__(self):
        return str(self.abstraction) + 'T'

    def abstract_func(self, f: Func, topped: set[ExprRef]) -> Spec:
        inp = [ self.get_const_for(i) for i in f.inputs ]
        try:
            w   = self.abstraction.get_width()
            af  = self.abstraction.abstract_func(f)
            sub = [ (a, Extract(w - 1, 0, i)) if is_bv_sort(self.get_sort_for(j.sort())) else (a, a)
                        for j, a, i in zip(f.inputs, af.inputs, inp) ]
            phi = substitute(af.func, sub)
            return Func(name=f'{f.name}T', inputs=inp, phi=Concat(BitVecVal(0, 1), phi))
        except CannotAbstract as e:
            topped.add(e.expr)
            w   = self.get_width()
            top = BitVecVal(1 << (w - 1), w)
            return Func(name=f'{f.name}T', inputs=inp, phi=top)

    def beta(self, concrete: ExprRef) -> ExprRef:
        return Concat(BitVecVal(0, 1), self.abstraction.beta(concrete))

    def gamma(self, concrete: ExprRef, abstract: ExprRef) -> ExprRef:
        w = self.get_width() - 1
        return Or(Extract(w, w, abstract) == BitVecVal(1, 1),
                  self.abstraction.gamma(concrete, Extract(w - 1, 0, abstract)))

@dataclass(frozen=True)
class LowerBitsAbstraction(BitVectorAbstraction):
    bit_width: int

    def get_width(self):
        return self.bit_width

    def abstracts_from(self, s: SortRef) -> bool:
        return is_bv_sort(s) and s.size() > self.bit_width

    def _name(self):
        return 'lsb'

    def abstract_func(self, f: Func, topped: set[ExprRef]) -> Func:
        ins = { c: self.get_const_for(c) for c in f.inputs }
        op  = substitute(simplify(self.beta(f.func)), [ (self.beta(i), a) for i, a in ins.items() ])
        if free_vars(op).intersection(ins):
            raise CannotAbstract(f, f.func)
        else:
            return Func(name=f.name + '#', phi=op)

    def beta(self, concrete: ExprRef) -> ExprRef:
        return Extract(self.bit_width - 1, 0, concrete)

    def gamma(self, concrete: ExprRef, abstract: ExprRef) -> bool:
        w = self.bit_width
        return Extract(w - 1, 0, abstract) == Extract(w - 1, 0, concrete)

@dataclass(frozen=True)
class NLZLSBAbstraction(PackedBitVectorAbstraction):
    log2_concrete_bit_width: int
    lower_bits_width: int

    def get_widths(self):
        return (self.log2_concrete_bit_width + 1, 1, self.lower_bits_width)

    def abstracts_from(self, s: SortRef) -> bool:
        return (is_bv_sort(s) and s.size() <= 2 ** self.self.log2_concrete_bit_width) \
            or s == BoolSort()

    def _name(self):
        return 'nlz*lsb'

    def get_sort_for(self, s):
        return BitVecSort(self.get_width()) if s == BoolSort() else super().get_sort_for(s)

    def beta(self, concrete: ExprRef) -> ExprRef:
        return Concat(bv_nlz(concrete, BitVecSort(self.log2_concrete_bit_width + 1)),
                      BitVecVal(0, 1),
                      Extract(self.lower_bits_width - 1, 0, concrete))

    def gamma(self, concrete: ExprRef, abstract: ExprRef) -> bool:
        nlz, top, lsb = self.unpack(abstract)
        W     = 1 << self.log2_concrete_bit_width
        nlz_w = self.log2_concrete_bit_width + 1
        nlz_W = ZeroExt(W - nlz_w, nlz) if W > nlz_w else nlz
        # logical shift: LShR(-1, nlz) = 2^(W-nlz) - 1, the maximum value with
        # at least `nlz` leading zeros (and 0 when nlz = W).
        return And(ULE(concrete, LShR(BitVecVal(-1, W), nlz_W)),
                   Or(top == BitVecVal(1, 1),
                      lsb == Extract(self.lower_bits_width - 1, 0, concrete)))

    def abstract_expr(self, expr: ExprRef,
                      abs_inputs: dict[ExprRef, Any],
                      topped: set[ExprRef]) -> tuple[ExprRef, ExprRef, ExprRef]:
        """Best-effort over-approximation of `expr` in the (nlz, top, lsb)
        domain. `abs_inputs` maps each free bitvector input of `expr` to its
        abstract triple. Concrete sub-bitvectors are folded via `beta`; for
        operators we don't know how to abstract, the result is top."""
        K  = self.log2_concrete_bit_width
        KN = K + 1                          # width of the nlz field (holds 0..W)
        L  = self.lower_bits_width
        W  = 1 << K
        BV1_0    = BitVecVal(0, 1)
        BV1_1    = BitVecVal(1, 1)
        NLZ_NONE = BitVecVal(0, KN)         # nlz = 0 ⇒ no info on magnitude
        NLZ_FULL = BitVecVal(W, KN)         # nlz = W ⇒ value is exactly zero
        LSB_ZERO = BitVecVal(0, L)
        TOP      = (NLZ_NONE, BV1_1, LSB_ZERO)
        ZERO     = (NLZ_FULL, BV1_0, LSB_ZERO)
        # An abstract Bool is the abstraction of the 0/1 BV that encodes it.
        ABS_FALSE    = ZERO
        ABS_TRUE     = (BitVecVal(W - 1, KN), BV1_0, BitVecVal(1, L))
        # Join of beta(0) and beta(1): value in {0,1} but lsb unknown.
        UNKNOWN_BOOL = (BitVecVal(W - 1, KN), BV1_1, LSB_ZERO)

        def umin(x, y): return If(ULE(x, y), x, y)
        def umax(x, y): return If(ULE(x, y), y, x)

        def select(cond, a, b):
            # pointwise If across abstract triples
            return tuple(If(cond, x, y) for x, y in zip(a, b))

        def k_to_KN(k):  # bring an L-bit shift amount into the (K+1)-bit nlz arena
            if KN >= L: return ZeroExt(KN - L, k)
            return Extract(KN - 1, 0, k)

        def shift_known(b):
            # b's value is fully determined by its abstraction iff its lsb is
            # exact and the upper W-L bits are zero (nlz >= W - L).
            n, t, _ = b
            return And(t == BV1_0, UGE(n, BitVecVal(W - L, KN)))

        def abs_const(v):
            return self.unpack(simplify(self.beta(v)))

        def is_zero(a):  # nlz = W exactly identifies the value 0
            return a[0] == NLZ_FULL

        def is_one(a):
            # nlz >= W-1 caps the value at 1; with lsb exact and bit 0 = 1
            # the only possibility is exactly 1.
            n, t, l = a
            return And(UGE(n, BitVecVal(W - 1, KN)),
                       t == BV1_0,
                       Extract(0, 0, l) == BitVecVal(1, 1))

        def is_nonzero(a):
            # Abstraction proves the value is not 0: the low L bits are exact
            # (top = 0) and at least one of them is set.
            _, t, l = a
            return And(t == BV1_0, l != LSB_ZERO)

        # --- per-op transformers --------------------------------------------
        def t_and(a, b):
            n1, t1, l1 = a; n2, t2, l2 = b
            # x & y has at least max(nlz1, nlz2) leading zeros; since nlz=W
            # forces the value to 0, max naturally propagates 0 & y = 0.
            return (umax(n1, n2), t1 | t2, l1 & l2)

        def t_or(a, b):
            n1, t1, l1 = a; n2, t2, l2 = b
            # min handles 0 | y = y (when one operand has nlz = W, min = the other).
            return (umin(n1, n2), t1 | t2, l1 | l2)

        def t_xor(a, b):
            n1, t1, l1 = a; n2, t2, l2 = b
            return (umin(n1, n2), t1 | t2, l1 ^ l2)

        def t_not(a):
            _, t, l = a
            return (NLZ_NONE, t, ~l)

        def t_neg(a):
            _, t, l = a
            gen = (NLZ_NONE, t, -l)
            return select(is_zero(a), ZERO, gen)

        def t_add(a, b):
            n1, t1, l1 = a; n2, t2, l2 = b
            # x + y can be one bit wider than the larger operand, so
            # nlz(x+y) >= min(nlz1, nlz2) - 1 (when the min is at least 1).
            m   = umin(n1, n2)
            gen = (If(UGT(m, NLZ_NONE), m - 1, NLZ_NONE), t1 | t2, l1 + l2)
            # 0 + y = y, x + 0 = x — propagate the other operand exactly.
            return select(is_zero(a), b,
                          select(is_zero(b), a, gen))

        def t_sub(a, b):
            _, t1, l1 = a; _, t2, l2 = b
            # underflow makes the nlz bound useless in general.
            gen = (NLZ_NONE, t1 | t2, l1 - l2)
            # x - 0 = x.
            return select(is_zero(b), a, gen)

        def t_mul(a, b):
            n1, t1, l1 = a; n2, t2, l2 = b
            # x*y < 2^(2W - n1 - n2), so when n1+n2 >= W we get nlz >= n1+n2-W.
            s    = ZeroExt(1, n1) + ZeroExt(1, n2)
            Wbv1 = BitVecVal(W, KN + 1)
            nlz  = If(UGE(s, Wbv1), Extract(KN - 1, 0, s - Wbv1), NLZ_NONE)
            gen  = (nlz, t1 | t2, l1 * l2)
            # 0 * y = x * 0 = 0.
            return select(Or(is_zero(a), is_zero(b)), ZERO, gen)

        def t_shl(a, b):
            n1, t1, l1 = a
            _, _, l2 = b
            known = shift_known(b)
            kKN   = k_to_KN(l2)
            nlz_k = If(UGE(n1, kKN), n1 - kKN, NLZ_NONE)
            gen   = (If(known, nlz_k, NLZ_NONE),
                     If(known, t1,    BV1_1),
                     If(known, l1 << l2, LSB_ZERO))
            # 0 << k = 0 holds for any (even unknown) shift amount.
            return select(is_zero(a), ZERO, gen)

        def t_lshr(a, b):
            n1, _, _ = a
            _, _, l2 = b
            known = shift_known(b)
            kKN   = k_to_KN(l2)
            # nlz(x >> k) >= nlz(x) + k, capped at W (= exactly zero).
            s    = ZeroExt(1, n1) + ZeroExt(1, kKN)
            Wbv1 = BitVecVal(W, KN + 1)
            cap  = If(UGE(s, Wbv1), NLZ_FULL, Extract(KN - 1, 0, s))
            # high bits feed the low ones; lsb is lost in general.
            gen  = (If(known, cap, NLZ_NONE), BV1_1, LSB_ZERO)
            # 0 >> k = 0 holds for any shift amount.
            return select(is_zero(a), ZERO, gen)

        def t_udiv(a, b):
            # Z3/SMT-LIB bvudiv: x / 0 = -1 (all ones). When y >= 1 we have
            # x/y <= x, so nlz(x/y) >= nlz(x); but if y might be 0 the result
            # could be -1 and the nlz bound is lost. The low bits of x/y are
            # generally not determined by x's and y's low bits alone.
            n1, _, _  = a
            minus_one = abs_const(BitVecVal(-1, W))
            nz_b      = is_nonzero(b)
            gen       = (If(nz_b, n1, NLZ_NONE), BV1_1, LSB_ZERO)
            return select(is_zero(b),                    minus_one,  # x / 0 = -1
                          select(is_one(b),              a,          # x / 1 = x
                          select(And(nz_b, is_zero(a)),  ZERO,       # 0 / (y!=0) = 0
                                 gen)))

        def t_join(a, b):  # least upper bound (used for ite)
            n1, t1, l1 = a; n2, t2, l2 = b
            mismatch = If(l1 == l2, BV1_0, BV1_1)
            return (umin(n1, n2), t1 | t2 | mismatch, l1)

        def t_eq(a, b):
            # Result is the abstraction of (x == y ? 1 : 0) viewed as a BV.
            n1, t1, l1 = a; n2, t2, l2 = b
            # Definitely equal: both abstractions force the value to 0.
            both_zero   = And(is_zero(a), is_zero(b))
            # Definitely equal: low L bits are exact on both AND nlz forces the
            # upper W-L bits to zero on both, AND the exact low bits agree.
            tight       = BitVecVal(W - L, KN)
            fully_known = And(t1 == BV1_0, t2 == BV1_0,
                              UGE(n1, tight), UGE(n2, tight))
            full_eq     = And(fully_known, l1 == l2)
            # Definitely not equal: low L bits exact on both but differ.
            lsb_diff    = And(t1 == BV1_0, t2 == BV1_0, l1 != l2)
            return select(Or(both_zero, full_eq), ABS_TRUE,
                          select(lsb_diff, ABS_FALSE, UNKNOWN_BOOL))

        def t_ite(c, a, b):
            # If the condition's abstraction pins it to true/false, pick that
            # branch; otherwise fall back to joining the branches.
            return select(is_one(c), a,
                          select(is_zero(c), b, t_join(a, b)))

        # --- recursive walk -------------------------------------------------
        def fold(f, xs):
            it  = iter(xs)
            acc = next(it)
            for x in it:
                acc = f(acc, x)
            return acc

        def go(e):
            nonlocal topped
            if e in abs_inputs:
                return abs_inputs[e]
            if is_bv_value(e):
                return abs_const(e)
            kind = e.decl().kind()
            ch   = e.children()
            if kind == Z3_OP_BADD:  return fold(t_add, (go(c) for c in ch))
            if kind == Z3_OP_BMUL:  return fold(t_mul, (go(c) for c in ch))
            if kind == Z3_OP_BAND:  return fold(t_and, (go(c) for c in ch))
            if kind == Z3_OP_BOR:   return fold(t_or,  (go(c) for c in ch))
            if kind == Z3_OP_BXOR:  return fold(t_xor, (go(c) for c in ch))
            if kind == Z3_OP_BSUB:  return t_sub (go(ch[0]), go(ch[1]))
            if kind == Z3_OP_BNOT:  return t_not (go(ch[0]))
            if kind == Z3_OP_BNEG:  return t_neg (go(ch[0]))
            if kind == Z3_OP_BSHL:  return t_shl (go(ch[0]), go(ch[1]))
            if kind == Z3_OP_BLSHR: return t_lshr(go(ch[0]), go(ch[1]))
            if kind == Z3_OP_BUDIV: return t_udiv(go(ch[0]), go(ch[1]))
            if kind == Z3_OP_EQ:    return t_eq  (go(ch[0]), go(ch[1]))
            if kind == Z3_OP_ITE:   return t_ite (go(ch[0]), go(ch[1]), go(ch[2]))
            if kind == Z3_OP_TRUE:  return ABS_TRUE
            if kind == Z3_OP_FALSE: return ABS_FALSE
            topped.add(e)
            return TOP

        return go(expr)

def get_lsb_abstraction_profile(e: ExprRef, refinement_steps: int = 4) -> Iterable[Abstraction]:
    max_width = get_max_used_bit_width(e)
    log2_max_width = math.ceil(math.log2(max_width))
    return [ ToppedBitVectorAbstraction(LowerBitsAbstraction(w)) \
             for w in range(log2_max_width, max_width, refinement_steps) ]

def get_nlz_lsb_abstraction_profile(e: ExprRef,
                                    refinement_steps: int = 4) -> Iterable[Abstraction]:
    max_width = get_max_used_bit_width(e)
    log2_max_width = math.ceil(math.log2(max_width))
    return [ NLZLSBAbstraction(log2_max_width, w) \
             for w in range(log2_max_width, max_width, refinement_steps) ]







