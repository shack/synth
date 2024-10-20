from functools import lru_cache
from itertools import chain
from collections import defaultdict
from dataclasses import dataclass
from typing import Tuple

from z3 import *

from synth.util import timer, bv_sort
from synth.cegis import cegis
from synth.spec import Task, Prg
from synth.oplib import Bv
from synth.synth_n import CegisBaseSynth

from synth import util, solvers

class _Brahma(CegisBaseSynth):
    def __init__(self, options, task: Task):
        assert all(insn.ctx == task.spec.ctx for insn in task.ops)
        # each operator must have its frequency specified
        assert all(not f is None for f in task.ops.values()), \
            "exact synthesis only possible if all operator frequencies are fixed."
        # construct operator list with multiple entries per operator
        ops = list(chain.from_iterable([ op ] * cnt for op, cnt in task.ops.items()))

        self.options   = options
        self.ctx       = ctx = Context()
        self.orig_spec = task.spec
        self.spec      = spec = task.spec.translate(ctx)
        self.orig_ops  = ops
        self.ops       = ops = [ op.translate(ctx) for op in ops ]

        self.n_inputs  = len(spec.in_types)
        self.n_outputs = len(spec.out_types)
        self.out_insn  = self.n_inputs + len(self.ops)
        self.length    = self.out_insn + 1
        self.opnds     = [[]] * self.n_inputs \
                       + [ op.inputs for op in ops ] \
                       + [ spec.outputs ]
        self.res_tys   = [ i.sort() for i in spec.inputs ] \
                       + [ op.out_type for op in ops ] \
                       + [ ]

        assert all(o.ctx == ctx for o in self.ops)
        assert all(op.ctx == spec.ctx for op in self.ops)

        # get the sorts for the variables used in synthesis
        self.ln_sort = bv_sort(self.length, ctx)
        self.bl_sort = BoolSort(ctx=ctx)

        # set options
        self.d = options.debug
        self.n_samples = 0
        self.synth = Goal(ctx=ctx)
        self.solve = lambda goal: options.solver.solve(goal, theory=task.theory)
        # add well-formedness, well-typedness, and optimization constraints
        self.add_constr_wfp(task.max_const, task.const_map)

    def sample_n(self, n):
        return self.spec.eval.sample_n(n)

    @lru_cache
    def get_var(self, ty, name):
        assert ty.ctx == self.ctx
        return Const(name, ty)

    def var_insn_pos(self, insn_idx):
        return self.get_var(self.ln_sort, f'insn_{insn_idx}_pos')

    def var_pos_ty(self, pos):
        return self.get_var(self.ty_sort, f'pos_{pos}_ty')

    def var_insn_opnds_is_const(self, insn_idx):
        for opnd, _ in enumerate(self.opnds[insn_idx]):
            yield self.get_var(self.bl_sort, f'insn_{insn_idx}_opnd_{opnd}_is_const')

    def var_insn_op_opnds_const_val(self, insn_idx):
        for opnd, ty in enumerate(i.sort() for i in self.opnds[insn_idx]):
            yield self.get_var(ty, f'insn_{insn_idx}_opnd_{opnd}_const_val')

    def var_insn_opnds(self, insn_idx):
        for opnd, _ in enumerate(self.opnds[insn_idx]):
            yield self.get_var(self.ln_sort, f'insn_{insn_idx}_opnd_{opnd}')

    def var_insn_opnds_val(self, insn_idx, instance):
        for opnd, ty in enumerate(i.sort() for i in self.opnds[insn_idx]):
            yield self.get_var(ty, f'|insn_{insn_idx}_opnd_{opnd}_{instance}|')

    def var_outs_val(self, instance):
        for opnd in self.var_insn_opnds_val(self.out_insn, instance):
            yield opnd

    def var_insn_res(self, insn_idx, instance):
        ty = self.ops[insn_idx - self.n_inputs].out_type \
             if insn_idx >= self.n_inputs else self.spec.in_types[insn_idx]
        return self.get_var(ty, f'|insn_{insn_idx}_res_{instance}|')

    def var_input_res(self, insn_idx, instance):
        return self.var_insn_res(insn_idx, instance)

    def iter_opnd_info(self, insn_idx, instance):
        return zip(self.var_insn_opnds(insn_idx), \
                   self.var_insn_opnds_val(insn_idx, instance), \
                   self.var_insn_opnds_is_const(insn_idx), \
                   self.var_insn_op_opnds_const_val(insn_idx))

    def iter_opnd_info_struct(self, insn_idx):
        return zip(self.var_insn_opnds(insn_idx), \
                   self.var_insn_opnds_is_const(insn_idx), \
                   self.var_insn_op_opnds_const_val(insn_idx))

    def iter_all(self):
        return range(self.length)

    def iter_interior(self):
        for i, op in enumerate(self.ops):
            yield (i + self.n_inputs, op)

    def iter_no_input(self):
        return range(self.n_inputs, self.length)

    def iter_no_output(self):
        return range(self.length - 1)

    def add_constr_wfp(self, max_const, const_map):
        solver = self.synth

        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for i in self.iter_all():
            for v in self.var_insn_opnds(i):
                solver.add(ULT(v, self.var_insn_pos(i)))

        # All instruction positions must be distinct.
        all_pos = [ self.var_insn_pos(i) for i in self.iter_all() ]
        solver.add(Distinct(all_pos))
        for p in all_pos:
            solver.add(ULT(p, self.length))
        for p in range(self.n_inputs):
            solver.add(self.var_insn_pos(p) == p)
        solver.add(self.var_insn_pos(self.out_insn) == self.length - 1)

        # Add a constraint for the maximum amount of constants if specified.
        # The output instruction is exempt because we need to be able
        # to synthesize constant outputs correctly.
        max_const_ran = range(self.n_inputs, self.length - 1)
        if not max_const is None and len(max_const_ran) > 0:
            solver.add(AtMost(*[ v for insn in max_const_ran \
                        for v in self.var_insn_opnds_is_const(insn)], max_const))

        # limit the possible set of constants if desired
        if const_map:
            ty_const_map = defaultdict(list)
            const_constr_map = defaultdict(list)
            for c, n in const_map.items():
                ty_const_map[c.sort()].append((c.translate(self.ctx), n))
            for insn in range(self.n_inputs, self.length):
                for _, c, cv in self.iter_opnd_info_struct(insn):
                    for v, _ in ty_const_map[c.sort()]:
                        const_constr_map[v] += [ And([c, cv == v ]) ]
            for c, constr in const_constr_map.items():
                if not (n := const_map[c]) is None:
                    solver.add(AtMost(*constr, n))

    def add_constr_conn(self, insn_idx, opnd_tys, instance):
        for (l, v, c, cv), ty in zip(self.iter_opnd_info(insn_idx, instance), opnd_tys):
            # if the operand is a constant, its value is the constant value
            self.synth.add(Implies(c, v == cv))
            # else, for other each instruction preceding it ...
            for other in self.iter_no_output():
                d = self.var_insn_pos(other)
                if ty == self.res_tys[other]:
                    # if the operand type is compatible with the result type
                    # the operand is equal to the result of the instruction
                    r = self.var_insn_res(other, instance)
                    self.synth.add(Implies(Not(c), Implies(l == d, v == r)))
                else:
                    self.synth.add(Implies(Not(c), l != d))

    def add_constr_instance(self, instance):
        # for all instructions that get an op
        for insn_idx, op in self.iter_interior():
            # add constraints to select the proper operation
            res = self.var_insn_res(insn_idx, instance)
            opnds = list(self.var_insn_opnds_val(insn_idx, instance))
            precond, phi = op.instantiate([ res ], opnds)
            self.synth.add(precond)
            self.synth.add(phi)
        # connect values of operands to values of corresponding results
        for insn_idx, op in self.iter_interior():
            self.add_constr_conn(insn_idx, op.in_types, instance)
        # add connection constraints for output instruction
        self.add_constr_conn(self.out_insn, self.spec.out_types, instance)

    def add_constr_io_sample(self, instance, in_vals, out_vals):
        # add input value constraints
        assert len(in_vals) == self.n_inputs
        assert len(out_vals) == self.n_outputs
        for inp, val in enumerate(in_vals):
            assert not val is None
            res = self.var_input_res(inp, instance)
            self.synth.add(res == val)
        for out, val in zip(self.var_outs_val(instance), out_vals):
            assert not val is None
            self.synth.add(out == val)

    def add_constr_io_spec(self, instance, in_vals):
        # add input value constraints
        assert len(in_vals) == self.n_inputs
        assert all(not val is None for val in in_vals)
        for inp, val in enumerate(in_vals):
            self.synth.add(val == self.var_input_res(inp, instance))
        outs = [ v for v in self.var_outs_val(instance) ]
        pre, phi = self.spec.instantiate(outs, in_vals)
        self.synth.add(Implies(pre, phi))

    def create_prg(self, model):
        def prep_opnds(insn_idx):
            for opnd, c, cv in self.iter_opnd_info_struct(insn_idx):
                if is_true(model[c]):
                    assert not model[c] is None
                    yield (True, model[cv].translate(self.orig_spec.ctx))
                else:
                    yield (False, model[opnd].as_long())
        insns = [ None ] * len(self.ops)
        for insn_idx, _ in self.iter_interior():
            pos_var = self.var_insn_pos(insn_idx)
            pos     = model[pos_var].as_long() - self.n_inputs
            assert 0 <= pos and pos < len(self.ops)
            opnds   = [ v for v in prep_opnds(insn_idx) ]
            insns[pos] = (self.orig_ops[insn_idx - self.n_inputs], opnds)
        outputs      = [ v for v in prep_opnds(self.out_insn) ]
        s = self.orig_spec
        return Prg(s.ctx, insns, outputs, s.outputs, s.inputs)

@dataclass(frozen=True)
class BrahmaExact(util.HasDebug, solvers.HasSolver):
    """Brahma algorithm that synthesizes with exactly with the given library.
       The synthesized program might contain dead code."""

    init_samples: int = 1
    """Number of initial samples."""

    dump_constr: bool = False
    """Dump synthesis constraints."""

    def _synth_exact(self, task: Task, init_samples):
        with timer() as elapsed:
            s = _Brahma(self, task)
            prg, stats = cegis(task.spec, s, init_samples=init_samples, debug=self.debug)
            all_stats = { 'time': elapsed(), 'iterations': stats }
        return prg, all_stats

    def get_init_samples(self, spec):
        return spec.eval.sample_n(self.init_samples)

    def synth(self, task: Task):
        assert all(not cnt is None for cnt in task.ops.values()), \
            'this synthesizer does not support unbounded operator frequency'
        init_samples = task.spec.eval.sample_n(self.init_samples)
        prg, stats = self._synth_exact(task, init_samples)
        return prg, [ stats ]

def _product_sum_bounded(bounds, lower, upper):
    L = len(bounds)
    def p(n, curr, curr_sum):
        if n == L:
            yield curr
        else:
            for i in range(bounds[n] + 1):
                s = curr_sum + i
                if lower <= s and s <= upper:
                    yield from p(n + 1, curr + [ i ], s)
    return p(0, [], 0)

@dataclass(frozen=True)
class BrahmaIterate(BrahmaExact):
    """Brahma algorithm adapted to finding the shortest program by
       enumerating all possible operator sub-libraries."""
    size_range: Tuple[int, int] = (0, 10)
    """Range of program sizes to try."""

    def synth(self, task: Task):
        all_stats = []
        init_samples = self.get_init_samples(task.spec)
        min_len, max_len = self.size_range
        # put the maximum length of the program as an upper bound for
        # the operator frequency if the operator is specified unbounded
        bounded_ops = { op: (cnt if not cnt is None else max_len) \
                       for op, cnt in task.ops.items() }
        assert all(not cnt is None for cnt in bounded_ops.values())
        # get two lists/tuples with the operators and their frequency upper bound
        ops, freqs = zip(*bounded_ops.items())
        # This iterator creates all combinations of operator frequencies,
        # filters those out whose program length is not in the given range
        # and sorts them by size (sum of the individual frequencies)
        for fs in sorted(_product_sum_bounded(freqs, min_len, max_len)):
            curr_ops = { op: f for op, f in zip(ops, fs) }
            self.debug(1, 'configuration', curr_ops)
            t = task.copy_with_different_ops(curr_ops)
            prg, stats = self._synth_exact(t, init_samples)
            all_stats += [ stats | { 'config': str(curr_ops) } ]
            if prg:
                return prg, all_stats
        return None, all_stats

@dataclass(frozen=True)
class BrahmaPaper(BrahmaExact):
    """The Brahma variant discussed in the original paper.
        Only works with bit-vector libraries."""
    def synth(self, task: Task):
        for o in task.ops:
            assert all(is_bv_sort(i.sort()) for i in o.outputs + o.inputs), \
                'only bit vector operations are supported'
        w = next(iter(task.ops)).inputs[0].sort().size()
        bv = Bv(w)
        initial_ops = {
            bv.neg_, bv.not_, bv.and_, bv.or_, bv.xor_,
            bv.add_, bv.sub_, bv.shl_, bv.lshr_, bv.ashr_,
            bv.uge_, bv.ult_,
        }
        use_ops = { op: 1 for op in initial_ops }
        for o, n in task.ops.items():
            if not n is None:
                cnt = n - 1 if o in initial_ops else n
                use_ops |= { o: cnt }
        library = ', '.join(str(o) for o in use_ops)
        self.debug(1, f'library (#{len(use_ops)}):', library)
        init_samples = self.get_init_samples(task.spec)
        prg, stats = self._synth_exact(task, init_samples)
        return prg, [ stats | {'library': library } ]