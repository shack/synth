from functools import lru_cache
from itertools import chain
from collections import defaultdict
from dataclasses import dataclass
from typing import Tuple

from z3 import *

from synth.util import timer, bv_sort
from synth.cegis import cegis
from synth.spec import Problem, SynthFunc, Prg
from synth.oplib import Bv

from synth import util, solvers

class _Brahma:
    def __init__(self, options, name: str, func: SynthFunc):
        # each operator must have its frequency specified
        assert all(not f is None for f in func.ops.values()), \
            "exact synthesis only possible if all operator frequencies are fixed."
        # construct operator list with multiple entries per operator
        ops = list(chain.from_iterable([ op ] * cnt for op, cnt in func.ops.items()))

        self.options   = options
        self.name      = name
        self.func      = func
        self.ops       = ops

        self.n_inputs  = len(func.inputs)
        self.n_outputs = len(func.outputs)
        self.out_insn  = self.n_inputs + len(self.ops)
        self.length    = self.out_insn + 1
        self.opnd_tys  = [ [] ] * self.n_inputs \
                       + [ op.in_types for op in ops ] \
                       + [ func.out_types ]
        self.res_tys   = func.in_types \
                       + [ op.out_type for op in ops ] \
                       + [ ]

        # get the sorts for the variables used in synthesis
        self.ln_sort = bv_sort(self.length)
        self.bl_sort = BoolSort()

        # set options
        self.d = options.debug
        # add well-formedness, well-typedness, and optimization constraints

    @lru_cache
    def get_var(self, ty, name):
        return Const(f'{self.name}_{name}', ty)

    def var_insn_pos(self, insn_idx):
        return self.get_var(self.ln_sort, f'insn_{insn_idx}_pos')

    def var_pos_ty(self, pos):
        return self.get_var(self.ty_sort, f'pos_{pos}_ty')

    def var_insn_opnds_is_const(self, insn_idx):
        for opnd, _ in enumerate(self.opnd_tys[insn_idx]):
            yield self.get_var(self.bl_sort, f'insn_{insn_idx}_opnd_{opnd}_is_const')

    def var_insn_op_opnds_const_val(self, insn_idx):
        for opnd, ty in enumerate(self.opnd_tys[insn_idx]):
            yield self.get_var(ty, f'insn_{insn_idx}_opnd_{opnd}_const_val')

    def var_insn_opnds(self, insn_idx):
        for opnd, _ in enumerate(self.opnd_tys[insn_idx]):
            yield self.get_var(self.ln_sort, f'insn_{insn_idx}_opnd_{opnd}')

    def var_insn_opnds_val(self, insn_idx, instance):
        for opnd, ty in enumerate(self.opnd_tys[insn_idx]):
            yield self.get_var(ty, f'|insn_{insn_idx}_opnd_{opnd}_{instance}|')

    def var_outs_val(self, instance):
        for opnd in self.var_insn_opnds_val(self.out_insn, instance):
            yield opnd

    def var_insn_res(self, insn_idx, instance):
        ty = self.ops[insn_idx - self.n_inputs].out_type \
             if insn_idx >= self.n_inputs else self.func.in_types[insn_idx]
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

    def add_program_constraints(self, res):
        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for i in self.iter_all():
            for v in self.var_insn_opnds(i):
                res.append(ULT(v, self.var_insn_pos(i)))

        # All instruction positions must be distinct.
        all_pos = [ self.var_insn_pos(i) for i in self.iter_all() ]
        res.append(Distinct(all_pos))
        for p in all_pos:
            res.append(ULT(p, self.length))
        for p in range(self.n_inputs):
            res.append(self.var_insn_pos(p) == p)
        res.append(self.var_insn_pos(self.out_insn) == self.length - 1)

        # Add a constraint for the maximum amount of constants if specified.
        # The output instruction is exempt because we need to be able
        # to synthesize constant outputs correctly.
        max_const_ran = range(self.n_inputs, self.length - 1)
        if not self.func.max_const is None and len(max_const_ran) > 0:
            res.append(AtMost(*[ v for insn in max_const_ran \
                        for v in self.var_insn_opnds_is_const(insn)], self.func.max_const))

        # limit the possible set of constants if desired
        if self.func.const_map:
            const_map = self.func.const_map
            ty_const_map = defaultdict(list)
            const_constr_map = defaultdict(list)
            for c, n in const_map.items():
                ty_const_map[c.sort()].append((c, n))
            for insn in range(self.n_inputs, self.length):
                for _, c, cv in self.iter_opnd_info_struct(insn):
                    for v, _ in ty_const_map[c.sort()]:
                        const_constr_map[v] += [ And([c, cv == v ]) ]
            for c, constr in const_constr_map.items():
                if not (n := const_map[c]) is None:
                    res.append(AtMost(*constr, n))
        return res

    def _add_constr_conn(self, insn_idx, opnd_tys, instance, res):
        for (l, v, c, cv), ty in zip(self.iter_opnd_info(insn_idx, instance), opnd_tys):
            # if the operand is a constant, its value is the constant value
            res.append(Implies(c, v == cv))
            # else, for other each instruction preceding it ...
            for other in self.iter_no_output():
                d = self.var_insn_pos(other)
                if ty == self.res_tys[other]:
                    # if the operand type is compatible with the result type
                    # the operand is equal to the result of the instruction
                    r = self.var_insn_res(other, instance)
                    res.append(Implies(Not(c), Implies(l == d, v == r)))
                else:
                    res.append(Implies(Not(c), l != d))
        return res

    def _add_constr_instance(self, instance, res):
        # for all instructions that get an op
        for insn_idx, op in self.iter_interior():
            # add constraints to select the proper operation
            r = self.var_insn_res(insn_idx, instance)
            opnds = list(self.var_insn_opnds_val(insn_idx, instance))
            precond, phi = op.instantiate([ r ], opnds)
            res.append(precond)
            res.append(phi)
        # connect values of operands to values of corresponding results
        for insn_idx, op in self.iter_interior():
            self._add_constr_conn(insn_idx, op.in_types, instance, res)
        # add connection constraints for output instruction
        self._add_constr_conn(self.out_insn, self.func.out_types, instance, res)
        return res

    def instantiate(self, instance, args, res):
        self._add_constr_instance(instance, res)
        in_vars = [ self.var_input_res(i, instance) for i in range(self.n_inputs) ]
        for a, v in zip(args, in_vars):
            res.append(a == v)
        out_vars = [ v for v in self.var_outs_val(instance) ]
        return res, out_vars, in_vars

    def create_prg(self, model):
        def prep_opnds(insn_idx):
            for opnd, c, cv in self.iter_opnd_info_struct(insn_idx):
                if is_true(model[c]):
                    assert not model[c] is None
                    yield (True, model[cv])
                else:
                    yield (False, model[opnd].as_long())
        insns = [ None ] * len(self.ops)
        for insn_idx, _ in self.iter_interior():
            pos_var = self.var_insn_pos(insn_idx)
            pos     = model[pos_var].as_long() - self.n_inputs
            assert 0 <= pos and pos < len(self.ops)
            opnds   = [ v for v in prep_opnds(insn_idx) ]
            insns[pos] = (self.ops[insn_idx - self.n_inputs], opnds)
        outputs      = [ v for v in prep_opnds(self.out_insn) ]
        return Prg(self.func, insns, outputs)

@dataclass(frozen=True)
class BrahmaExact(util.HasDebug, solvers.HasSolver):
    """Brahma algorithm that synthesizes with exactly with the given library.
       The synthesized program might contain dead code."""

    init_samples: int = 1
    """Number of initial samples."""

    detailed_stats: bool = False
    """Collect detailed statistics."""

    def _invoke(self, problem: Problem):
        constr  = problem.constraint
        funcs   = problem.funcs
        solver  = self.solver.create(theory=problem.theory)
        synths  = { name: _Brahma(self, name, f) for name, f in funcs.items() }
        samples = constr.counterexample_eval.sample_n(self.init_samples)

        for s in synths.values():
            s.add_program_constraints(solver)

        with timer() as elapsed:
            prg, stats, _ = cegis(solver, constr, synths, self, samples)
            all_stats = { 'time': elapsed(), 'iterations': stats }
            return prg, all_stats

    def synth_prgs(self, problem: Problem):
        assert all(not cnt is None for f in problem.funcs.values() for cnt in f.ops.values()), \
            'this synthesizer does not support unbounded operator frequency'
        prg, stats = self._invoke(problem)
        return prg, stats

@dataclass(frozen=True)
class BrahmaMaxLen(BrahmaExact):
    """Brahma algorithm for unknown operator frequencies.
       You have to specify a maximum program size S and each operator
       will be present S times in the library."""

    max_len: int = 5
    """Maximum length of the program to synthesize."""

    def synth_prgs(self, problem: Problem):
        new_funcs = { n: f.copy_with_different_ops({ op: self.max_len for op in f.ops }) for n, f in problem.funcs.items() }
        new_problem = Problem(constraint=problem.constraint, funcs=new_funcs, theory=problem.theory)
        prg, stats = self._invoke(new_problem)
        return prg, stats

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

    def synth_prgs(self, problem: Problem):
        assert len(problem.funcs) == 1, 'this synthesizer only supports a single function'
        func = next(iter(problem.funcs.values()))
        all_stats = []
        min_len, max_len = self.size_range
        # put the maximum length of the program as an upper bound for
        # the operator frequency if the operator is specified unbounded
        bounded_ops = { op: (cnt if not cnt is None else max_len) \
                        for op, cnt in func.ops.items() }
        assert all(not cnt is None for cnt in bounded_ops.values())
        # get two lists/tuples with the operators and their frequency upper bound
        ops, freqs = zip(*bounded_ops.items())
        # This iterator creates all combinations of operator frequencies,
        # filters those out whose program length is not in the given range
        # and sorts them by size (sum of the individual frequencies)
        with timer() as elapsed:
            for fs in sorted(_product_sum_bounded(freqs, min_len, max_len)):
                curr_ops = { op: f for op, f in zip(ops, fs) }
                self.debug(1, 'configuration', curr_ops)
                new_funcs = { n: f.copy_with_different_ops(curr_ops) for n, f in problem.funcs.items() }
                p = Problem(constraint=problem.constraint, funcs=new_funcs, theory=problem.theory)
                prg, stats = self._invoke(p)
                all_stats += [ stats | { 'config': str(curr_ops) } ]
                if prg:
                    return prg, { 'time': elapsed(), 'stats': all_stats }
            return None, { 'time': elapsed(), 'stats': all_stats }

@dataclass(frozen=True)
class BrahmaPaper(BrahmaExact):
    """The Brahma variant discussed in the original paper.
        Only works with bit-vector libraries."""
    def synth_prgs(self, problem: Problem):
        new_funcs = {}
        for name, func in problem.funcs.items():
            if not all(is_bv_sort(i.sort()) for o in func.ops \
                    for i in o.outputs + o.inputs):
                return None, { 'time': 0 }

            w = next(iter(func.ops)).inputs[0].sort().size()
            bv = Bv(w)
            initial_ops = {
                bv.neg_, bv.not_, bv.and_, bv.or_, bv.xor_,
                bv.add_, bv.sub_, bv.shl_, bv.lshr_, bv.ashr_,
                bv.uge_, bv.ult_,
            }
            use_ops = { op: 1 for op in initial_ops }
            for o, n in func.ops.items():
                if not n is None:
                    use_ops[o] = n
            new_funcs[name] = func.copy_with_different_ops(use_ops)
            self.debug(1, f'library for {name} (#{len(use_ops)}):', use_ops)
        problem = Problem(constraint=problem.constraint, funcs=new_funcs, theory=problem.theory)
        prg, stats = self._invoke(problem)
        return prg, stats