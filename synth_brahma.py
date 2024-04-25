from functools import lru_cache
from itertools import chain, combinations_with_replacement

from z3 import *

from cegis import Spec, Func, Prg, OpFreq, no_debug, timer, cegis
from oplib import Bl
from util import bv_sort

class Brahma:
    def __init__(self, spec: Spec, ops: list[Func], \
        debug=no_debug, timeout=None, max_const=None, const_set=None, \
        output_prefix=None, theory=None, reset_solver=True):

        """Synthesize a program that computes the given functions.

        Attributes:
        spec: The specification of the program to be synthesized.
        ops: List of operations that can be used in the program.
        debug: Debug level. 0: no debug output, >0 more debug output.
        max_const: Maximum number of constants that can be used in the program.
        const_set: Restrict constants to values from this set.
        init_samples: A list of input/output samples that are used to initialize the synthesis process.
        output_prefix: If set to a string, the synthesizer dumps every SMT problem to a file with that prefix.
        theory: A theory to use for the synthesis solver (e.g. QF_FD for finite domains).
        reset_solver: Resets the solver for each counter example.
            For some theories (e.g. FD) incremental solving makes Z3 fall back
            to slower solvers. Setting reset_solver to false prevents that.
        """

        assert all(insn.ctx == spec.ctx for insn in ops)
        self.ctx       = ctx = Context()
        self.orig_spec = spec
        self.spec      = spec = spec.translate(ctx)
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
        self.d = debug
        self.n_samples = 0
        self.output_prefix = output_prefix
        self.reset_solver = reset_solver

        if theory:
            self.synth_solver = SolverFor(theory, ctx=ctx)
        else:
            self.synth_solver = Tactic('psmt', ctx=ctx).solver()
        if not timeout is None:
            self.synth_solver.set('timeout', timeout)
        self.synth = Goal(ctx=ctx) if reset_solver else self.synth_solver
        # add well-formedness, well-typedness, and optimization constraints
        self.add_constr_wfp(max_const, const_set)

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

    def add_constr_wfp(self, max_const, const_set):
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
        if const_set:
            consts = set(c.translate(self.ctx) for c in const_set)
            for insn in range(self.n_inputs, self.length):
                for _, _, cv in self.iter_opnd_info_struct(insn):
                    solver.add(Or([ cv == v for v in consts ]))

    def synth_with_new_samples(self, samples):
        ctx       = self.ctx
        spec      = self.spec
        samples   = [ [ v.translate(ctx) for v in s ] for s in samples ]

        def add_constr_conn(solver, insn_idx, opnd_tys, instance):
            for (l, v, c, cv), ty in zip(self.iter_opnd_info(insn_idx, instance), opnd_tys):
                # if the operand is a constant, its value is the constant value
                solver.add(Implies(c, v == cv))
                # else, for other each instruction preceding it ...
                for other in self.iter_no_output():
                    d = self.var_insn_pos(other)
                    if ty == self.res_tys[other]:
                        # if the operand type is compatible with the result type
                        # the operand is equal to the result of the instruction
                        r = self.var_insn_res(other, instance)
                        solver.add(Implies(Not(c), Implies(l == d, v == r)))
                    else:
                        solver.add(Implies(Not(c), l != d))

        def add_constr_instance(solver, instance):
            # for all instructions that get an op
            for insn_idx, op in self.iter_interior():
                # add constraints to select the proper operation
                res = self.var_insn_res(insn_idx, instance)
                opnds = list(self.var_insn_opnds_val(insn_idx, instance))
                precond, phi = op.instantiate([ res ], opnds)
                solver.add(precond)
                solver.add(phi)
            # connect values of operands to values of corresponding results
            for insn_idx, op in self.iter_interior():
                add_constr_conn(solver, insn_idx, op.in_types, instance)
            # add connection constraints for output instruction
            add_constr_conn(solver, self.out_insn, self.spec.out_types, instance)

        def add_constr_io_sample(solver, instance, in_vals, out_vals):
            # add input value constraints
            assert len(in_vals) == self.n_inputs
            assert len(out_vals) == self.n_outputs
            for inp, val in enumerate(in_vals):
                assert not val is None
                res = self.var_input_res(inp, instance)
                solver.add(res == val)
            for out, val in zip(self.var_outs_val(instance), out_vals):
                assert not val is None
                solver.add(out == val)

        def add_constr_io_spec(solver, instance, in_vals):
            # add input value constraints
            assert len(in_vals) == self.n_inputs
            assert all(not val is None for val in in_vals)
            for inp, val in enumerate(in_vals):
                solver.add(val == self.var_input_res(inp, instance))
            outs = [ v for v in self.var_outs_val(instance) ]
            pre, phi = spec.instantiate(outs, in_vals)
            solver.add(Implies(pre, phi))

        def create_prg(model):
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
            return Prg(self.orig_spec, insns, outputs)

        def write_smt2(*args):
            s = self.synth_solver
            if not type(s) is Solver:
                s = Solver(ctx=ctx)
                s.add(self.synth_solver)
            if self.output_prefix:
                filename = f'{self.output_prefix}_{"_".join(str(a) for a in args)}.smt2'
                with open(filename, 'w') as f:
                    print(s.to_smt2(), file=f)

        # main synthesis algorithm.
        # 1) set up counter examples
        for sample in samples:
            if self.spec.is_deterministic and self.spec.is_total:
                # if the specification is deterministic and total we can
                # just use the specification to sample output values and
                # include them in the counterexample constraints.
                out_vals = self.spec.eval(sample)
                add_constr_io_sample(self.synth, self.n_samples, sample, out_vals)
            else:
                # if the spec is not deterministic or total, we have to
                # express the output of the specification implicitly by
                # the formula of the specification.
                add_constr_io_spec(self.synth, self.n_samples, sample)
            # add a new instance of the specification for each sample
            add_constr_instance(self.synth, self.n_samples)
            self.n_samples += 1
        write_smt2('synth', self.n_samples)
        stat = {}
        if self.reset_solver:
            self.synth_solver.reset()
            self.synth_solver.add(self.synth)
        self.d(3, 'synth', self.n_samples, self.synth_solver)
        with timer() as elapsed:
            res = self.synth_solver.check()
            synth_time = elapsed()
            stat['synth_stat'] = self.synth_solver.statistics()
            self.d(6, stat['synth_stat'])
            self.d(2, f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = self.synth_solver.model()
            prg = create_prg(m)
            self.d(4, 'model: ', m)
            return prg, stat
        else:
            return None, stat

def synth_exact(spec: Spec, ops, n_samples=1, **args):
    """Synthesize a program that computes the given function.

    Note that the program will consist exactly of
    the given list of operations (ops).

    Parameters:
    spec: Specification of the program to synthesize.
    ops: List of operations that will be used in the program.
    n_samples: Number of initial I/O samples to give to the synthesizer.
    args: arguments passed to the synthesizer

    Returns:
    A tuple (prg, stats) where prg is the synthesized program (or None
    if no program has been found) and stats is a list of statistics for each
    iteration of the synthesis loop.
    """
    all_stats = []
    init_samples = spec.eval.sample_n(n_samples)
    with timer() as elapsed:
        synthesizer = Brahma(spec, ops, **args)
        prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                           debug=synthesizer.d)
        all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
    return prg, all_stats

def synth(spec: Spec, ops, size_range, n_samples=1, **args):
    d = args.get('debug', no_debug)
    unbounded_ops = [ op for op, cnt in ops.items() if cnt >= OpFreq.MAX ]
    bounded_ops = list(chain.from_iterable([ op ] * cnt for op, cnt in ops.items() if cnt < OpFreq.MAX))
    seen = set()
    all_stats = []
    if not unbounded_ops:
        return synth_exact(spec, bounded_ops, n_samples, **args)
    else:
        op_list = bounded_ops + list(o for op in unbounded_ops for o in [ op ] * len(size_range))
    for n in size_range:
        d(1, 'length', n)
        for os in combinations_with_replacement(op_list, n):
            key = tuple(sorted(os, key=lambda o: o.name))
            if key in seen:
                continue
            else:
                seen.add(key)
            config = ', '.join(str(o) for o in os)
            d(1, 'configuration', config)
            with timer() as elapsed:
                prg, stats = synth_exact(spec, os, n_samples, **args)
                all_stats += [ { 'time': elapsed(), 'config': config, 'iterations': stats } ]
            if prg:
                return prg, all_stats
    return None, all_stats

# Enable Z3 parallel mode
set_param("parallel.enable", True)
set_param("sat.random_seed", 0);
set_param("smt.random_seed", 0);
set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

def p(l, *args):
    if l <= 1:
        print(*args)

if __name__ == "__main__":
    # x, y = Bools('x y')
    # spec = Func('and', And(x, y))
    # ops  = [ Bl.nand2 ] * 2
    # synth(spec, ops, theory='QF_FD', debug=p, max_const=0)

    # w = 32
    # x, y = BitVecs('x y', w)
    # ops = [
    #     Func('sub', x - y),
    #     Func('xor', x ^ y),
    #     Func('shr', x >> y, precond=And([y >= 0, y < w]))
    # ]
    # spec = Func('spec', If(x >= 0, x, -x))
    # prg, _ = synth(spec, ops, theory='QF_FD', debug=p)

    x = Int('x')
    y = BitVec('y', 8)
    int2bv = Func('int2bv', Int2BV(x, 16))
    bv2int = Func('bv2int', BV2Int(y))
    div2   = Func('div2', x / 2)
    spec   = Func('shr2', LShR(ZeroExt(8, y), 1))
    ops    = [ int2bv, bv2int, div2 ]
    prg, _ = synth_exact(spec, ops, debug=p)
    print(prg)

    x, y, ci, s, co = Bools('x y ci s co')
    add = And([co == AtLeast(x, y, ci, 2), s == Xor(x, Xor(y, ci))])
    spec = Spec('adder', add, [s, co], [x, y, ci])
    ops  = [ Bl.and2 ] * 2 + [ Bl.xor2 ] * 2 + [ Bl.or2 ] * 1
    prg, _ = synth_exact(spec, ops, theory='QF_FD', debug=p, max_const=0)
    print(prg)
