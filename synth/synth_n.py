from functools import lru_cache
from collections import defaultdict
from dataclasses import dataclass
from typing import Tuple

from z3 import *

from synth.cegis import cegis
from synth.spec import Func, Prg, Task
from synth.optimizers import HasOptimizer
from synth.downscaling import transform_task_to_bitwidth
from synth import solvers, util

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
        self.sort = util.bv_sort(len(items), ctx)
        super().__init__(items, [ i for i, _ in enumerate(items) ])

    def get_from_model_val(self, val):
        return self.cons_to_item[val.as_long()]

    def add_range_constr(self, solver, var):
        solver.add(ULT(var, len(self.item_to_cons)))

class CegisBaseSynth:
    def synth_with_new_samples(self, samples):
        ctx       = self.ctx
        samples   = [ [ v.translate(ctx) for v in s ] for s in samples ]

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
        if self.options.dump_constr:
            # write synthesis constraint into a text file
            s = Solver(ctx=ctx)
            s.add(self.synth)
            with open(f'{self.spec.name}_{self.n_insns}_{self.n_samples}.smt2', 'wt') as f:
                print(s.to_smt2(), file=f)
        stat = {}
        self.d(3, 'synth', self.n_samples, self.synth)
        synth_time, model = self.solve(self.synth)
        self.d(2, f'synth time: {synth_time / 1e9:.3f}')
        stat['synth_time'] = synth_time
        if model:
            # if sat, we found location variables
            prg = self.create_prg(model)
            self.d(4, 'model: ', model)
            return prg, stat
        else:
            return None, stat

class _Ctx(CegisBaseSynth):
    def __init__(self, options, task: Task, n_insns: int):
        """Synthesize a program that computes the given functions.

        Attributes:
        options: Options to the synthesis.
        task: The synthesis task.
        n_insn: Number of instructions in the program.
        """
        self.task      = task
        assert all(insn.ctx == task.spec.ctx for insn in task.ops)
        self.options   = options
        self.ctx       = ctx = Context()
        self.orig_spec = task.spec
        self.spec      = spec = task.spec.translate(ctx)

        if len(task.ops) == 0:
            ops = { Func('dummy', Int('v') + 1): 0 }
        elif type(task.ops) == list or type(task.ops) == set:
            ops = { op: None for op in ops }
        else:
            ops = task.ops

        self.orig_ops  = { op.translate(ctx): op for op in ops }
        self.op_freqs  = { op_new: ops[op_old] for op_new, op_old in self.orig_ops.items() }
        self.ops       = ops = list(self.orig_ops.keys())
        self.n_insns   = n_insns

        self.in_tys    = spec.in_types
        self.out_tys   = spec.out_types
        self.n_inputs  = len(self.in_tys)
        self.n_outputs = len(self.out_tys)
        self.out_insn  = self.n_inputs + self.n_insns # index of the out instruction
        self.length    = self.out_insn + 1
        self.max_arity = max(op.arity for op in ops)
        self.arities   = [ 0 ] * self.n_inputs \
                       + [ self.max_arity ] * self.n_insns \
                       + [ self.n_outputs ]

        assert all(o.ctx == ctx for o in self.ops)
        assert all(op.ctx == spec.ctx for op in self.orig_ops)
        self.types = set(ty for op in ops for ty in op.out_types + op.in_types)

        if options.bitvec_enum:
            # prepare operator enum sort
            self.op_enum = BitVecEnum('Operators', ops, ctx)
            # create map of types to their id
            self.ty_enum = BitVecEnum('Types', self.types, ctx)
        else:
            # prepare operator enum sort
            self.op_enum = EnumSortEnum('Operators', ops, ctx)
            # create map of types to their id
            self.ty_enum = EnumSortEnum('Types', self.types, ctx)

        # get the sorts for the variables used in synthesis
        self.ty_sort = self.ty_enum.sort
        self.op_sort = self.op_enum.sort
        self.ln_sort = util.bv_sort(self.length - 1, ctx)
        self.bl_sort = BoolSort(ctx=ctx)

        # set options
        self.d = options.debug
        self.n_samples = 0
        self.solve = lambda goal: options.solver.solve(goal, theory=task.theory)
        self.synth = Goal(ctx=ctx)

        # add well-formedness, well-typedness, and optimization constraints
        self.add_constr_wfp()
        self.add_constr_ty()
        self.add_constr_opt()
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

    def add_constr_insn_count(self):
        # constrain the number of usages of an operator if specified
        for op, op_cons in self.op_enum.item_to_cons.items():
            if not (f := self.op_freqs[op]) is None:
                a = [ self.var_insn_op(insn) == op_cons \
                    for insn in range(self.n_inputs, self.length - 1) ]
                if a:
                    self.synth.add(AtMost(*a, f))
                    if self.options.exact:
                        self.synth.add(AtLeast(*a, f))

    def add_constr_const_count(self):
        const_map = self.task.const_map
        max_const = self.task.max_const
        solver    = self.synth

        # If supplied with an empty set of constants, we don't allow any constants
        if not const_map is None and len(const_map) == 0:
            max_const = 0

        # Add a constraint for the maximum amount of constants if specified.
        ran = range(self.n_inputs, self.length)
        if not max_const is None and len(ran) > 0:
            solver.add(AtMost(*[ v for insn in ran \
                       for v in self.var_insn_opnds_is_const(insn)], max_const))

        # limit the possible set of constants if desired
        if const_map:
            const_map_t = { c.translate(self.ctx): n for c, n in const_map.items() }
            ty_const_map = defaultdict(list)
            const_constr_map = defaultdict(list)
            for c, n in const_map_t.items():
                ty_const_map[c.sort()].append((c, n))
            for insn in range(self.n_inputs, self.length):
                for ty in self.types:
                    for _, _, c, cv in self.iter_opnd_info_struct(insn, [ ty ] * self.max_arity):
                        eqs = []
                        for v, _ in ty_const_map[ty]:
                            eqs += [ cv == v ]
                            const_constr_map[v] += [ And([c, cv == v ]) ]
                        solver.add(Implies(c, Or(eqs)))
            for c, constr in const_constr_map.items():
                if not (n := const_map_t[c]) is None:
                    solver.add(AtMost(*constr, n))
                    if self.options.exact:
                        solver.add(AtLeast(*constr, n))

    def add_constr_wfp(self):
        solver = self.synth

        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for insn in range(self.length):
            for v in self.var_insn_opnds(insn):
                solver.add(ULT(v, insn))

        # Add bounds for the operand ids
        for insn in range(self.n_inputs, self.length - 1):
            self.op_enum.add_range_constr(solver, self.var_insn_op(insn))

        # Add constraints on the instruction counts
        self.add_constr_insn_count()

        # Add constraints on constant usage
        self.add_constr_const_count()

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
                    solver.add(Implies(self.var_insn_op(insn) == op_id, v == types[op_ty]))

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

    def add_constr_opt(self):
        solver = self.synth

        def opnd_set(insn):
            ext = self.length - self.ln_sort.size()
            assert ext >= 0
            res = BitVecVal(0, self.length, ctx=self.ctx)
            one = BitVecVal(1, self.length, ctx=self.ctx)
            for opnd in self.var_insn_opnds(insn):
                res |= one << ZeroExt(ext, opnd)
            return res

        if self.options.opt_insn_order:
            for insn in range(self.n_inputs, self.out_insn - 1):
                solver.add(ULE(opnd_set(insn), opnd_set(insn + 1)))

        for insn in range(self.n_inputs, self.out_insn):
            op_var = self.var_insn_op(insn)
            for op, op_id in self.op_enum.item_to_cons.items():
                # if operator is commutative, force the operands to be in ascending order
                if self.options.opt_commutative and op.is_commutative:
                    opnds = list(self.var_insn_opnds(insn))
                    c = [ ULE(l, u) for l, u in zip(opnds[:op.arity - 1], opnds[1:]) ]
                    solver.add(Implies(op_var == op_id, And(c, self.ctx)))

                if self.options.opt_const:
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
            if self.options.opt_cse:
                for other in range(self.n_inputs, insn):
                    un_eq = [ p != q for p, q in zip(self.var_insn_opnds(insn), \
                                                     self.var_insn_opnds(other)) ]
                    assert len(un_eq) > 0
                    solver.add(Implies(op_var == self.var_insn_op(other), Or(un_eq)))

        # no dead code: each produced value is used
        if self.options.opt_no_dead_code:
            for prod in range(self.n_inputs, self.length):
                opnds = [ And([ prod == v, Not(c) ]) \
                        for cons in range(prod + 1, self.length) \
                        for c, v in zip(self.var_insn_opnds_is_const(cons), \
                                        self.var_insn_opnds(cons)) ]
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
            for ty in self.types:
                self.add_constr_conn(insn, [ ty ] * self.max_arity, instance)
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
        s = self.orig_spec
        def prep_opnds(insn, tys):
            for _, opnd, c, cv in self.iter_opnd_info_struct(insn, tys):
                if is_true(model[c]):
                    assert not model[cv] is None
                    yield (True, model[cv].translate(s.ctx))
                else:
                    assert not model[opnd] is None, str(opnd) + str(model)
                    yield (False, model[opnd].as_long())
        insns = []
        for insn in range(self.n_inputs, self.length - 1):
            val    = model.evaluate(self.var_insn_op(insn), model_completion=True)
            op     = self.op_enum.get_from_model_val(val)
            opnds  = [ v for v in prep_opnds(insn, op.in_types) ]
            insns += [ (self.orig_ops[op], opnds) ]
        outputs = [ v for v in prep_opnds(self.out_insn, self.out_tys) ]
        return Prg(s.ctx, insns, outputs, s.outputs, s.inputs)

@dataclass(frozen=True)
class _Base(util.HasDebug, solvers.HasSolver):
    opt_no_dead_code: bool = True
    """Disallow dead code."""

    opt_cse: bool = True
    """Disallow common subexpressions."""

    opt_const: bool = True
    """At most arity-1 operands can be constants."""

    opt_commutative: bool = True
    """Force order of operands of commutative operators."""

    opt_insn_order: bool = True
    """Order of instructions is determined by operands."""

    bitvec_enum: bool = True
    """Use bitvector encoding of enum types."""

    dump_constr: bool = False
    """Dump the synthesis constraints to a file."""

    exact: bool = False
    """Each operator appears exactly as often as indicated (overrides size_range)."""

    size_range: Tuple[int, int] = (0, 10)
    """Range of program sizes to try."""

    def synth(self, task: Task):
        self.debug(2, task)
        if self.exact:
            assert all(not v is None for v in task.ops.values())
            l = h = sum(f for f in task.ops.values())
        else:
            l, h = self.size_range
        all_stats = []
        init_samples = self.get_init_samples(task.spec)
        for n_insns in range(l, h + 1):
            with util.timer() as elapsed:
                prg, stats = self.invoke_synth(task, n_insns, init_samples)
                all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
                if not prg is None:
                    return prg, all_stats
        return None, all_stats


@dataclass(frozen=True)
class LenCegis(_Base):
    """Cegis synthesizer that finds the shortest program."""
    init_samples: int = 1

    def get_init_samples(self, spec):
        return spec.eval.sample_n(self.init_samples)

    def invoke_synth(self, task: Task, n_insns: int, init_samples):
        s = _Ctx(self, task, n_insns)
        return cegis(task.spec, s, init_samples=init_samples, debug=self.debug)

class _FA(_Ctx):
    def __init__(self, *argp, **argk):
        self.exist_vars = set()
        super().__init__(*argp, **argk)

    @lru_cache
    def get_var(self, ty, name, instance=None):
        res = super().get_var(ty, name, instance)
        if not instance is None:
            self.exist_vars.add(res)
        return res

    def do_synth(self):
        ins  = [ self.var_input_res(i, 'fa') for i in range(self.n_inputs) ]
        self.exist_vars.difference_update(ins)
        self.add_constr_instance('fa')
        self.add_constr_io_spec('fa', ins)
        s = Solver(ctx=self.ctx)
        s.add(ForAll(ins, Exists(list(self.exist_vars), And([a for a in self.synth]))))

        if self.options.dump_constr:
            filename = f'{self.spec.name}_synth.smt2'
            with open(filename, 'w') as f:
                print(s.to_smt2(), file=f)

        stat = {}
        self.d(3, 'synth', s)
        with util.timer() as elapsed:
            res = s.check()
            synth_time = elapsed()
            stat['synth_stat'] = s.statistics()
            self.d(5, stat['synth_stat'])
            self.d(2, f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = s.model()
            prg = self.create_prg(m)
            self.d(4, 'model: ', m)
            return prg, stat
        else:
            return None, stat

@dataclass(frozen=True)
class LenFA(_Base):
    """Synthesizer that uses a forall constraint and finds the shortest program."""
    def get_init_samples(self, spec):
        return None

    def invoke_synth(self, task: Task, n_insns: int, init_samples):
        return _FA(self, task, n_insns).do_synth()

@dataclass(frozen=True)
class _OptZ3Solver:
    parallel: bool = False
    """Enable Z3 parallel mode."""

    verbose: int = 0
    """Set Z3 verbosity level."""

    def __post_init__(self):
        if self.parallel:
            set_option("parallel.enable", True);
        if self.verbose > 0:
            set_option("verbose", self.verbose);
            set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

    def solve(self, goal, theory):
        with util.timer() as elapsed:
            res = goal.check()
            time = elapsed()
        return time, goal.model() if res == sat else None

class _OptCegis(_Ctx):
    def __init__(self, options, task: Task, n_insns: int):

        # if required add an additional identify operator to the operators
        id_operator = Func('id', task.spec.outputs[0])
        if options.insert_identity_operator:
            task.ops[id_operator] = None


        super().__init__(options, task, n_insns)

        # find the transformed id operator
        if options.insert_identity_operator:
            # let it be accessible by optimizations
            self.id = next(transformed for (transformed, op) in self.orig_ops.items() if op == id_operator)

            # add the constraints on the id operator
            self.add_constr_id_wfp()

        # if required set the goal to be Optimizer
        if options.use_z3_opt:
            # self.synth is a goal at this point -> overwrite it to be the Optimize class
            goal = self.synth
            self.synth = Optimize(ctx=self.ctx)
            self.synth.add(goal)

            solver = _OptZ3Solver(parallel=options.solver.parallel, verbose=options.solver.verbose)

            # overwrite the solve function to only call for the model
            self.solve = lambda goal: solver.solve(goal, None)

    def add_constr_id_wfp(self):
        solver = self.synth

        # id is only used for the output as a last instruction
        # iterate over all instructions used in output
        for insn in range(self.n_inputs, self.out_insn):
            # get operator of instruction
            op_var = self.var_insn_op(insn)
            # get the id operator
            id_id = self.op_enum.item_to_cons[self.id]
            # every following instruction is id
            cons = [ self.var_insn_op(f_insn) == id_id for f_insn in range(insn + 1, self.out_insn)]
            # if the operator is id, every following insn operator is also id (if there is at least one following insn)
            solver.add(Implies(op_var == id_id, And(cons, self.ctx)))

        # only first id may receive a constant as an operand
        # iterate over all instructions used in output
        for insn in range(self.n_inputs, self.out_insn):
            # get operator of instruction
            op_var = self.var_insn_op(insn)
            # get the id operator
            id_id = self.op_enum.item_to_cons[self.id]
            # if operator is id AND  >=one of the operands is a constant
            cond = And(op_var == id_id, Or([var == True for var in self.var_insn_opnds_is_const(insn)]))
            # then every previous instruction may not be id
            cons = [ self.var_insn_op(f_insn) != id_id for f_insn in range(self.n_inputs, insn)]
            solver.add(Implies(cond, And(cons, self.ctx)))

@dataclass(frozen=True)
class OptCegis(LenCegis, HasOptimizer):
    """Cegis synthesizer that finds the program optimal for a provided metric"""

    use_z3_opt: bool = True
    """Use the Z3 Optimize API to minimize the cost function."""

    insert_identity_operator: bool = True

    def invoke_synth(self, task: Task, n_insns: int, init_samples):
        s = _OptCegis(self, task, n_insns)
        self.optimizer.add_constraint(s)
        return cegis(task.spec, s, init_samples=init_samples, debug=self.debug)


class _ConstantSolver:
    """Interface for constant solvers"""

    def __init__(self, options, task: Task, base_program: Prg):
        self.ctx            = ctx = Context()
        self.solver         = lambda goal: options.solver.solve(goal, theory=None)
        self.synth          = Goal(ctx=ctx)
        self.prg            = base_program
        self.const_map      = {}
        self.task           = task
        self.sample_counter = 0
        self.spec           = task.spec.translate(ctx)

    # weird hack to get type translated to the correct context, as Sort.translate always throws an error
    def get_type(self, ty):
        return Const(f'type_{ty}', ty).translate(self.ctx).sort()

    def get_const_var(self, ty, insn, opnd):
        return Const(f'insn_{insn}_opnd_{opnd}_{ty}_const_val', self.get_type(ty))

    def const_to_var(self, insn, n_opnd, ty, _):
        if insn in self.const_map:
            val = self.const_map[insn]
            if n_opnd in val:
                return val[n_opnd]

            # create new const for the operand
            var = self.get_const_var(ty, insn, n_opnd)
            val[n_opnd] = var
            return var
        else:
            # create new const for the instruction
            var = self.get_const_var(ty, insn, n_opnd)
            self.const_map[insn] = { n_opnd: var }
            return var

    def create_in_out_vars(self, n_sample):
        # create in variables
        in_vars = [ Const(f'in_{i}_{n_sample}', ty)
                    for i, ty in enumerate(self.spec.in_types) ]
        # create out variables
        out_vars = [ Const(f'out_{i}_{n_sample}', ty)
                    for i, ty in enumerate(self.spec.out_types) ]
        return in_vars, out_vars

    def create_prg(self, model):
        insns = [
            (op,
             [
                 (is_const,
                  model[self.const_map[insn][n_opnd]].translate(self.task.spec.ctx) if is_const else value
                  ) for (n_opnd, (is_const, value)) in enumerate(args) ]
            ) for (insn, (op, args)) in enumerate(self.prg.insns) ]

        outputs = [ (is_const,
                     model[self.const_map[len(self.prg.insns)][n_out]].translate(self.task.spec.ctx) if is_const else value
                    ) for (n_out, (is_const, value)) in enumerate(self.prg.outputs)]

        return Prg(self.task.spec.ctx, insns, outputs, self.task.spec.outputs, self.task.spec.inputs)


class _CegisConstantSolver(_ConstantSolver):
    """Synthesizer that implements CEGIS solver interface to find the constants in the program."""

    def synth_with_new_samples(self, samples):
        # TODO: support for constant set restrictions
        ctx = self.ctx
        prg = self.prg
        assert prg is not None

        samples = [ [ v.translate(ctx) for v in s ] for s in samples ]

        for sample in samples:
            # use the Prg::eval_clauses_external to create the constraints

            # create variables
            in_vars, out_vars = self.create_in_out_vars(self.sample_counter)
            # add io constraints
            if self.task.spec.is_deterministic and self.task.spec.is_total:
                out_vals = self.spec.eval(sample)
                # set out variables
                self.synth.add([ v == val for v, val in zip(out_vars, out_vals) ])
                # set in variables
                self.synth.add([ v == val for v, val in zip(in_vars, sample) ])
            else:
                # set in vals
                self.synth.add([ v == val for v, val in zip(in_vars, sample) ])
                # set outs based on the spec
                outs = [ v for v in out_vars ]
                precond, phi = self.spec.instantiate(outs, sample)
                self.synth.add(Implies(precond, phi))
            # add program constraints
            for constraint in prg.eval_clauses_external(in_vars, out_vars, const_to_var=self.const_to_var, ctx=ctx, intermediate_vars=[]):
                self.synth.add(constraint)
            self.sample_counter += 1

        stat = {}
        synth_time, model = self.solver(self.synth)
        # self.d(2, f'synth time: {synth_time / 1e9:.3f}')
        stat['synth_time'] = synth_time
        if model:
            # if sat, we found location variables
            prg = self.create_prg(model)
            # self.d(4, 'model: ', model)
            return prg, stat
        else:
            return None, stat


class _FAConstantSolver(_ConstantSolver):
    def do_synth(self):
        constraints = []

        in_vars, out_vars = self.create_in_out_vars(0)
        precond, phi = self.spec.instantiate(out_vars, in_vars)
        constraints.append(Implies(precond, phi))

        intermediate_vars = list(out_vars)

        # add program constraints
        for constraint in self.prg.eval_clauses_external(in_vars, out_vars,
                const_to_var=self.const_to_var, ctx=self.ctx, intermediate_vars=intermediate_vars):
            constraints.append(constraint)

        if len(intermediate_vars) > 0:
            self.synth.add(ForAll(in_vars, Exists(list(intermediate_vars), And(constraints))))
        else:
            self.synth.add(ForAll(in_vars, And(constraints)))

        stat = {}
        synth_time, model = self.solver(self.synth)
        # self.d(2, f'synth time: {synth_time / 1e9:.3f}')
        stat['synth_time'] = synth_time
        if model:
            # if sat, we found location variables
            prg = self.create_prg(model)
            # self.d(4, 'model: ', model)
            return prg, stat
        else:
            return None, stat


@dataclass(frozen=True)
class DownscaleSynth(LenCegis):
    """Synthesizer that first solve the task on a smaller bitwidth, then scales it up."""

    target_bitwidth: str = "4"
    """Comma separated list of target bitwidths (integer) to scale down to."""

    constant_finder_use_cegis: bool = False
    """Whether to use CEGIS to find the constants in the upscaling process."""

    keep_const_map: bool = False
    """Whether to keep the constant map for the downscaling process."""

    def synth(self, task: Task):
        combined_stats = []

        init_samples = self.get_init_samples(task.spec)

        # try to downscale
        for target_bitwidth in self.target_bitwidth.split(","):
            target_bw = int(target_bitwidth)
            # scale down the task
            try:
                scaled_task = transform_task_to_bitwidth(task, target_bw, self.keep_const_map)
            except Exception as e:
                self.debug(1, f"Failed to scale down the task to bitwidth {target_bw}: {e}")
                continue

            # run the synthesis on the scaled task
            prg, stats = super().synth(scaled_task.transformed_task)
            combined_stats += stats
            if prg is None:
                self.debug(2, f"Failed to synthesize a program for bitwidth {target_bw}")
                continue

            # scale up
            # revert to original operators
            prg = scaled_task.prg_with_original_operators(prg)
            with util.timer() as elapsed:
                self.debug(1, f"Proposed program for bitwidth {target_bw}:\n{prg}")

                if (self.constant_finder_use_cegis):
                    # find the constants using CEGIS
                    solver = _CegisConstantSolver(self, task, prg)
                    prg, stats = cegis(task.spec, solver, init_samples=init_samples, debug=self.debug)
                else:
                    # find the constants using FA
                    solver = _FAConstantSolver(self, task, prg)
                    prg, stats = solver.do_synth()
                    stats = [ stats ]

                combined_stats += [ { 'time': elapsed(), 'iterations': stats } ]

            if prg is not None:
                return prg, combined_stats

        # Fallback to normal synthesis if normal synthesis fails
        self.debug(1, f"Fallback to normal synthesis")
        prg, stats = super().synth(task)
        combined_stats.extend(stats)
        return prg, combined_stats
