from functools import lru_cache
from collections import defaultdict

from z3 import *

from cegis import Spec, Func, Prg, OpFreq, no_debug, timer, cegis
from util import bv_sort

class EnumBase:
    def __init__(self, items, cons):
        assert len(items) == len(cons)
        self.cons = cons
        self.item_to_cons = { i: con for i, con in zip(items, cons) }
        self.cons_to_item = { con: i for i, con in zip(items, cons) }

    def __len__(self):
        return len(self.cons)

class EnumSortEnum(EnumBase):
    def __init__(self, name, items, ctx):
        # TODO: Seems to be broken with contexts
        # self.sort, cons = EnumSort(name, [ str(i) for i in items ], ctx=ctx)
        s = Datatype(name, ctx=ctx)
        for i in items:
            s.declare(str(i))
        self.sort = s.create()
        cons = [ getattr(self.sort, str(i)) for i in items ]
        super().__init__(items, cons)

    def get_from_model_val(self, val):
        return self.cons_to_item[val]

    def add_range_constr(self, solver, var):
        pass

class BitVecEnum(EnumBase):
    def __init__(self, name, items, ctx):
        self.sort = bv_sort(len(items), ctx)
        super().__init__(items, [ i for i, _ in enumerate(items) ])

    def get_from_model_val(self, val):
        return self.cons_to_item[val.as_long()]

    def add_range_constr(self, solver, var):
        solver.add(ULT(var, len(self.item_to_cons)))

class SynthN:
    def __init__(self, spec: Spec, ops: list[Func], n_insns, \
        debug=no_debug, timeout=None, max_const=None, const_set=None, \
        output_prefix=None, theory=None, reset_solver=True, \
        opt_no_dead_code=True, opt_no_cse=True, opt_const=True, \
        opt_commutative=True, opt_insn_order=True):

        """Synthesize a program that computes the given functions.

        Attributes:
        spec: The specification of the program to be synthesized.
        ops: List of operations that can be used in the program.
        n_insn: Number of instructions in the program.
        debug: Debug level. 0: no debug output, >0 more debug output.
        max_const: Maximum number of constants that can be used in the program.
        const_set: Restrict constants to values from this set.
        init_samples: A list of input/output samples that are used to initialize the synthesis process.
        output_prefix: If set to a string, the synthesizer dumps every SMT problem to a file with that prefix.
        theory: A theory to use for the synthesis solver (e.g. QF_FD for finite domains).
        reset_solver: Resets the solver for each counter example.
            For some theories (e.g. FD) incremental solving makes Z3 fall back
            to slower solvers. Setting reset_solver to false prevents that.

        Following search space space pruning optimization flags are available:
        opt_no_dead_code: Disallow dead code.
        opt_no_cse: Disallow common subexpressions.
        opt_const: At most arity-1 operands can be constants.
        opt_commutative: Force order of operands of commutative operators.
        opt_insn_order: Order of instructions is determined by operands.

        Returns:
        A pair (prg, stats) where prg is the synthesized program (or None
        if no program has been found), stats is a list of statistics for each
        iteration of the synthesis loop.
        """
        assert all(insn.ctx == spec.ctx for insn in ops)
        self.ctx       = ctx = Context()
        self.orig_spec = spec
        self.spec      = spec = spec.translate(ctx)

        if len(ops) == 0:
            ops = { Func('dummy', Int('v') + 1): 0 }
        elif type(ops) == list or type(ops) == set:
            ops = { op: OpFreq.MAX for op in ops }

        self.orig_ops  = { op.translate(ctx): op for op in ops }
        self.op_freqs  = { op_new: ops[op_old] for op_new, op_old in self.orig_ops.items() }
        self.ops       = ops = list(self.orig_ops.keys())
        self.n_insns   = n_insns

        self.in_tys    = spec.in_types
        self.out_tys   = spec.out_types
        self.n_inputs  = len(self.in_tys)
        self.n_outputs = len(self.out_tys)
        self.out_insn  = self.n_inputs + self.n_insns
        self.length    = self.out_insn + 1
        max_arity      = max(op.arity for op in ops)
        self.arities   = [ 0 ] * self.n_inputs \
                       + [ max_arity ] * self.n_insns \
                       + [ self.n_outputs ]

        assert all(o.ctx == ctx for o in self.ops)
        assert all(op.ctx == spec.ctx for op in self.orig_ops)
        types = set(ty for op in ops for ty in op.out_types + op.in_types)

        # prepare operator enum sort
        self.op_enum = EnumSortEnum('Operators', ops, ctx)
        # create map of types to their id
        self.ty_enum = EnumSortEnum('Types', types, ctx)

        # get the sorts for the variables used in synthesis
        self.ty_sort = self.ty_enum.sort
        self.op_sort = self.op_enum.sort
        self.ln_sort = bv_sort(self.length - 1, ctx)
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
        self.add_constr_ty()
        self.add_constr_opt(opt_no_dead_code, opt_no_cse, opt_const, \
                            opt_commutative, opt_insn_order)
        self.d(1, 'size', self.n_insns)

    def sample_n(self, n):
        return self.spec.eval.sample_n(n)

    @lru_cache
    def get_var(self, ty, name, instance=None):
        name = f'|{name}_{instance}|' if not instance is None else f'|{name}|'
        assert ty.ctx == self.ctx
        return Const(name, ty)

    def var_insn_op(self, insn):
        return self.get_var(self.op_sort, f'insn_{insn}_op')

    def var_insn_opnds_is_const(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.get_var(self.bl_sort, f'insn_{insn}_opnd_{opnd}_is_const')

    def var_insn_op_opnds_const_val(self, insn, opnd_tys):
        for opnd, ty in enumerate(opnd_tys):
            yield self.get_var(ty, f'insn_{insn}_opnd_{opnd}_{ty}_const_val')

    def var_insn_opnds(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.get_var(self.ln_sort, f'insn_{insn}_opnd_{opnd}')

    def var_insn_opnds_val(self, insn, tys, instance):
        for opnd, ty in enumerate(tys):
            yield self.get_var(ty, f'insn_{insn}_opnd_{opnd}_{ty}', instance)

    def var_outs_val(self, instance):
        for opnd in self.var_insn_opnds_val(self.out_insn, self.out_tys, instance):
            yield opnd

    def var_insn_opnds_type(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.get_var(self.ty_sort, f'insn_{insn}_opnd_type_{opnd}')

    def var_insn_res(self, insn, ty, instance):
        return self.get_var(ty, f'insn_{insn}_res_{ty}', instance)

    def var_insn_res_type(self, insn):
        return self.get_var(self.ty_sort, f'insn_{insn}_res_type')

    def var_input_res(self, insn, instance):
        return self.var_insn_res(insn, self.in_tys[insn], instance)

    def is_op_insn(self, insn):
        return insn >= self.n_inputs and insn < self.length - 1

    def iter_opnd_info(self, insn, tys, instance):
        return zip(tys, \
                self.var_insn_opnds(insn), \
                self.var_insn_opnds_val(insn, tys, instance), \
                self.var_insn_opnds_is_const(insn), \
                self.var_insn_op_opnds_const_val(insn, tys))

    def iter_opnd_info_struct(self, insn, tys):
        return zip(tys, \
                self.var_insn_opnds(insn), \
                self.var_insn_opnds_is_const(insn), \
                self.var_insn_op_opnds_const_val(insn, tys))

    def add_constr_wfp(self, max_const, const_set):
        solver = self.synth

        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for insn in range(self.length):
            for v in self.var_insn_opnds(insn):
                solver.add(ULT(v, insn))

        for op, op_cons in self.op_enum.item_to_cons.items():
            if (f := self.op_freqs[op]) < OpFreq.MAX:
                a = [ self.var_insn_op(insn) == op_cons \
                      for insn in range(self.n_inputs, self.length - 1) ]
                if a:
                    solver.add(AtMost(*a, f))

        # pin operands of an instruction that are not used (because of arity)
        # to the last input of that instruction
        for insn in range(self.n_inputs, self.length - 1):
            self.op_enum.add_range_constr(solver, self.var_insn_op(insn))
            opnds = list(self.var_insn_opnds(insn))
            for op, op_id in self.op_enum.item_to_cons.items():
                unused = opnds[op.arity:]
                for opnd in unused:
                    solver.add(Implies(self.var_insn_op(insn) == op_id, \
                                       opnd == opnds[op.arity - 1]))

        # Add a constraint for the maximum amount of constants if specified.
        # The output instruction is exempt because we need to be able
        # to synthesize constant outputs correctly.
        max_const_ran = range(self.n_inputs, self.length)
        # max_const_ran = range(self.n_inputs, self.length - 1)
        if not max_const is None and len(max_const_ran) > 0:
            solver.add(AtMost(*[ v for insn in max_const_ran \
                        for v in self.var_insn_opnds_is_const(insn)], max_const))

        # limit the possible set of constants if desired
        if const_set:
            const_map = defaultdict(list)
            for c in const_set:
                c = c.translate(self.ctx)
                const_map[c.sort()].append(c)
            for insn in range(self.n_inputs, self.length):
                for op, op_id in self.op_enum.item_to_cons.items():
                    for ty, _, _, cv in self.iter_opnd_info_struct(insn, op.in_types):
                        solver.add(Or([ cv == v for v in const_map[ty] ]))

    def add_constr_ty(self):
        if len(self.ty_enum) <= 1:
            # we don't need constraints if there is only one type
            return

        solver = self.synth
        # for all instructions that get an op
        # add constraints that set the type of an instruction's operand
        # and the result type of an instruction
        types = self.ty_enum.item_to_cons
        for insn in range(self.n_inputs, self.length - 1):
            for op, op_id in self.op_enum.item_to_cons.items():
                # add constraints that set the result type of each instruction
                solver.add(Implies(self.var_insn_op(insn) == op_id, \
                                self.var_insn_res_type(insn) == types[op.out_type]))
                # add constraints that set the type of each operand
                for op_ty, v in zip(op.in_types, self.var_insn_opnds_type(insn)):
                    solver.add(Implies(self.var_insn_op(insn) == op_id, \
                                        v == types[op_ty]))

        # define types of inputs
        for inp, ty in enumerate(self.in_tys):
            solver.add(self.var_insn_res_type(inp) == types[ty])

        # define types of outputs
        for v, ty in zip(self.var_insn_opnds_type(self.out_insn), self.out_tys):
            solver.add(v == types[ty])

        # constrain types of outputs
        for insn in range(self.n_inputs, self.length):
            for other in range(0, insn):
                for opnd, c, ty in zip(self.var_insn_opnds(insn), \
                                       self.var_insn_opnds_is_const(insn), \
                                       self.var_insn_opnds_type(insn)):
                    solver.add(Implies(Not(c), Implies(opnd == other, \
                                    ty == self.var_insn_res_type(other))))
            self.ty_enum.add_range_constr(solver, self.var_insn_res_type(insn))

    def add_constr_opt(self, opt_no_dead_code, opt_no_cse, \
                       opt_const, opt_commutative, opt_insn_order):
        solver = self.synth

        def opnd_set(insn):
            ext = self.length - self.ln_sort.size()
            assert ext >= 0
            res = BitVecVal(0, self.length, ctx=self.ctx)
            one = BitVecVal(1, self.length, ctx=self.ctx)
            for opnd in self.var_insn_opnds(insn):
                res |= one << ZeroExt(ext, opnd)
            return res

        if opt_insn_order:
            for insn in range(self.n_inputs, self.out_insn - 1):
                solver.add(ULE(opnd_set(insn), opnd_set(insn + 1)))

        for insn in range(self.n_inputs, self.out_insn):
            op_var = self.var_insn_op(insn)
            for op, op_id in self.op_enum.item_to_cons.items():
                # if operator is commutative, force the operands to be in ascending order
                if opt_commutative and op.is_commutative:
                    opnds = list(self.var_insn_opnds(insn))
                    c = [ ULE(l, u) for l, u in zip(opnds[:op.arity - 1], opnds[1:]) ]
                    solver.add(Implies(op_var == op_id, And(c, self.ctx)))

                if opt_const:
                    vars = [ v for v in self.var_insn_opnds_is_const(insn) ][:op.arity]
                    assert len(vars) > 0
                    if op.arity == 2 and op.is_commutative:
                        # Binary commutative operators have at most one constant operand
                        # Hence, we pin the first operand to me non-constant
                        solver.add(Implies(op_var == op_id, vars[0] == False))
                    else:
                        # Otherwise, we require that at least one operand is non-constant
                        solver.add(Implies(op_var == op_id, Not(And(vars))))

            # Computations must not be replicated: If an operation appears again
            # in the program, at least one of the operands must be different from
            # a previous occurrence of the same operation.
            if opt_no_cse:
                for other in range(self.n_inputs, insn):
                    un_eq = [ p != q for p, q in zip(self.var_insn_opnds(insn), self.var_insn_opnds(other)) ]
                    assert len(un_eq) > 0
                    solver.add(Implies(op_var == self.var_insn_op(other), Or(un_eq)))

        # no dead code: each produced value is used
        if opt_no_dead_code:
            for prod in range(self.n_inputs, self.length):
                opnds = [ And([ prod == v, Not(c) ]) \
                          for cons in range(prod + 1, self.length) \
                          for c, v in zip(self.var_insn_opnds_is_const(cons), self.var_insn_opnds(cons)) ]
                if len(opnds) > 0:
                    solver.add(Or(opnds))

    def add_constr_conn(self, insn, tys, instance):
        for ty, l, v, c, cv in self.iter_opnd_info(insn, tys, instance):
            # if the operand is a constant, its value is the constant value
            self.synth.add(Implies(c, v == cv))
            # else, for other each instruction preceding it ...
            for other in range(insn):
                r = self.var_insn_res(other, ty, instance)
                # ... the operand is equal to the result of the instruction
                self.synth.add(Implies(Not(c), Implies(l == other, v == r)))

    def add_constr_instance(self, instance):
        # for all instructions that get an op
        for insn in range(self.n_inputs, self.length - 1):
            # add constraints to select the proper operation
            op_var = self.var_insn_op(insn)
            for op, op_id in self.op_enum.item_to_cons.items():
                res = self.var_insn_res(insn, op.out_type, instance)
                opnds = list(self.var_insn_opnds_val(insn, op.in_types, instance))
                precond, phi = op.instantiate([ res ], opnds)
                self.synth.add(Implies(op_var == op_id, And([ precond, phi ])))
            # connect values of operands to values of corresponding results
            for op in self.ops:
                self.add_constr_conn(insn, op.in_types, instance)
        # add connection constraints for output instruction
        self.add_constr_conn(self.out_insn, self.out_tys, instance)

    def add_constr_io_sample(self, instance, in_vals, out_vals):
        # add input value constraints
        assert len(in_vals) == self.n_inputs and len(out_vals) == self.n_outputs
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
        precond, phi = self.spec.instantiate(outs, in_vals)
        self.synth.add(Implies(precond, phi))

    def create_prg(self, model):
        def prep_opnds(insn, tys):
            for _, opnd, c, cv in self.iter_opnd_info_struct(insn, tys):
                if is_true(model[c]):
                    assert not model[cv] is None
                    yield (True, model[cv].translate(self.orig_spec.ctx))
                else:
                    assert not model[opnd] is None, str(opnd) + str(model)
                    yield (False, model[opnd].as_long())
        insns = []
        for insn in range(self.n_inputs, self.length - 1):
            val    = model.evaluate(self.var_insn_op(insn), model_completion=True)
            op     = self.op_enum.get_from_model_val(val)
            opnds  = [ v for v in prep_opnds(insn, op.in_types) ]
            insns += [ (self.orig_ops[op], opnds) ]
        outputs      = [ v for v in prep_opnds(self.out_insn, self.out_tys) ]
        return Prg(self.orig_spec, insns, outputs)

    def synth_with_new_samples(self, samples):
        ctx       = self.ctx
        samples   = [ [ v.translate(ctx) for v in s ] for s in samples ]

        def write_smt2(*args):
            s = self.synth
            if not type(s) is Solver:
                s = Solver(ctx=ctx)
                s.add(self.synth)
            if self.output_prefix:
                filename = f'{self.output_prefix}_{"_".join(str(a) for a in args)}.smt2'
                with open(filename, 'w') as f:
                    print(s.to_smt2(), file=f)

        # main synthesis algorithm.
        # 1) set up counter examples
        for sample in samples:
            # add a new instance of the specification for each sample
            self.add_constr_instance(self.n_samples)
            if self.spec.is_deterministic and self.spec.is_total:
                # if the specification is deterministic and total we can
                # just use the specification to sample output values and
                # include them in the counterexample constraints.
                out_vals = self.spec.eval(sample)
                self.add_constr_io_sample(self.n_samples, sample, out_vals)
            else:
                # if the spec is not deterministic or total, we have to
                # express the output of the specification implicitly by
                # the formula of the specification.
                self.add_constr_io_spec(self.n_samples, sample)
            self.n_samples += 1
        write_smt2('synth', self.n_insns, self.n_samples)
        stat = {}
        if self.reset_solver:
            self.synth_solver.reset()
            self.synth_solver.add(self.synth)
        self.d(3, 'synth', self.n_samples, self.synth_solver)
        with timer() as elapsed:
            res = self.synth_solver.check()
            synth_time = elapsed()
            stat['synth_stat'] = self.synth_solver.statistics()
            self.d(5, stat['synth_stat'])
            self.d(2, f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = self.synth_solver.model()
            prg = self.create_prg(m)
            self.d(4, 'model: ', m)
            return prg, stat
        else:
            return None, stat

def synth(spec: Spec, ops, iter_range, n_samples=1, **args):
    """Synthesize a program that computes the given function.

    Attributes:
    spec: Specification of the function to be synthesized.
    ops: Collection (set/list) of operations that can be used in the program.
    iter_range: Range of program lengths that are tried.
    n_samples: Number of initial I/O samples to give to the synthesizer.
    args: arguments passed to the synthesizer

    Returns:
    A tuple (prg, stats) where prg is the synthesized program (or None
    if no program has been found) and stats is a list of statistics for each
    iteration of the synthesis loop.
    """

    all_stats = []
    init_samples = spec.eval.sample_n(n_samples)
    for n_insns in iter_range:
        with timer() as elapsed:
            synthesizer = SynthN(spec, ops, n_insns, **args)
            prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                               debug=synthesizer.d)
            all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
            if not prg is None:
                return prg, all_stats
    return None, all_stats