from functools import lru_cache
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Tuple

from z3 import *

from synth.cegis import CegisBaseSynth
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

class BitVecEnum(EnumBase):
    def __init__(self, name, items):
        self.sort = util.bv_sort(len(items))
        super().__init__(items, [ i for i, _ in enumerate(items) ])

    def get_from_model_val(self, val):
        return self.cons_to_item[val.as_long()]

    def get_from_op(self, op):
        return self.item_to_cons[op]

    def add_range_constr(self, solver, var):
        solver.add(ULT(var, len(self.item_to_cons)))

class AllPrgSynth:
    def synth_all_prgs(self):
        while True:
            prg, stats = self.synth_prg()
            yield prg, stats
            if prg is None:
                return
            else:
                self.exclude_program(prg)

class _LenConstraints:
    def __init__(self, options, task: Task, n_insns: int):
        """Synthesize a program that computes the given functions.

        Attributes:
        options: Options to the synthesis.
        task: The synthesis task.
        n_insn: Number of instructions in the program.
        """
        self.task      = task
        self.options   = options
        self.orig_spec = task.spec
        self.spec      = spec = task.spec
        self.n_insns   = n_insns

        if len(task.ops) == 0:
            ops = { Func('dummy', Int('v') + 1): 0 }
        elif type(task.ops) == list or type(task.ops) == set:
            ops = { op: None for op in task.ops }
        else:
            ops = dict(task.ops)

        self.ops       = ops
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

        self.types = set(ty for op in ops for ty in op.out_types + op.in_types)

        # prepare operator enum sort
        self.op_enum = BitVecEnum('Operators', ops)
        # create map of types to their id
        self.ty_enum = BitVecEnum('Types', self.types)

        # get the sorts for the variables used in synthesis
        self.ty_sort = self.ty_enum.sort
        self.op_sort = self.op_enum.sort
        self.ln_sort = util.bv_sort(self.length - 1)
        self.bl_sort = BoolSort()

        # set options
        self.d = options.debug
        self.n_samples = 0
        self.synth = options.solver.create(theory=task.theory)

        # add well-formedness, well-typedness, and optimization constraints
        self.add_constr_wfp()
        self.add_constr_ty()
        self.add_constr_opt()
        self.d(1, 'size', self.n_insns)

    @lru_cache
    def get_var(self, ty, name, instance=None):
        name = f'|{name}_{instance}|' if not instance is None else f'|{name}|'
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

    def var_not_all_eq(self, insn, ty, instance):
        return self.get_var(BoolSort(), f'not_all_eq_{insn}_{ty}', instance)

    def var_not_eq_pair(self, i1, i2, ty, instance):
        return self.get_var(BoolSort(), f'not_eq_pair_{i1}_{i2}_{ty}', instance)

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
            if not (f := self.ops[op]) is None:
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
            ty_const_map = defaultdict(list)
            const_constr_map = defaultdict(list)
            for c, n in const_map.items():
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
                if not (n := const_map[c]) is None:
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
        # Add a constraint that pins potentially unused operands to the last
        # one. This is important because otherwise the no_dead_code constraints
        # will not work.
        for insn in range(self.n_inputs, self.length - 1):
            for op, op_id in self.op_enum.item_to_cons.items():
                if op.arity < self.max_arity:
                    opnds = list(self.var_insn_opnds(insn))
                    self.synth.add(Implies(self.var_insn_op(insn) == op_id, \
                        And([ opnds[op.arity - 1] == x for x in opnds[op.arity:] ])))
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
            sz  = self.length + (self.op_sort.size() if self.options.opt_insn_order_op else 0)
            ext = sz - self.ln_sort.size()
            assert ext >= 0
            res = BitVecVal(0, sz)
            one = BitVecVal(1, sz)
            for opnd in self.var_insn_opnds(insn):
                res |= one << ZeroExt(ext, opnd)
            if self.options.opt_insn_order_op:
                res = (res << BitVecVal(self.op_sort.size(), sz)) \
                    | ZeroExt(sz - self.op_sort.size(), self.var_insn_op(insn))
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
                    solver.add(Implies(op_var == op_id, And(c)))

                if self.options.opt_const:
                    vars = [ v for v in self.var_insn_opnds_is_const(insn) ][:op.arity]
                    assert len(vars) > 0
                    if op.arity == 2 and op.is_commutative:
                        # Binary commutative operators have at most one constant operand
                        # Hence, we pin the first operand to me non-constant
                        not_const = vars[0]
                    else:
                        # Otherwise, we require that at least one operand is non-constant
                        not_const = And(vars)
                    solver.add(Implies(op_var == op_id, Not(not_const)))

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
            for prod in range(self.n_inputs, self.out_insn):
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

    def add_constr_opt_instance(self, instance):
        for insn in range(self.n_inputs, self.length - 1):
            # add constraints to select the proper operation
            for op in self.op_enum.item_to_cons:
                res = self.var_insn_res(insn, op.out_type, instance)

                # forbid constant expressions that are not constant
                if self.options.no_const_expr:
                    v = self.var_not_all_eq(insn, op.out_type, instance)
                    if instance >= 1:
                        prev_res = self.var_insn_res(insn, op.out_type, instance - 1)
                        if instance > 1:
                            prev = self.var_not_all_eq(insn, op.out_type, instance - 1)
                        else:
                            prev = BoolVal(False)
                        self.synth.add(v == Or([ prev, res != prev_res ]))

                # forbid semantic equivalence of instructions
                if self.options.no_semantic_eq:
                    for other in range(0, insn):
                        for other_op in self.op_enum.item_to_cons:
                            if other_op.out_type != op.out_type:
                                continue
                            other_res = self.var_insn_res(other, op.out_type, instance)
                            v = self.var_not_eq_pair(insn, other, op.out_type, instance)
                            if instance > 0:
                                prev = self.var_not_eq_pair(insn, other, op.out_type, instance - 1)
                                self.synth.add(v == Or([prev, res != other_res]))
                            else:
                                self.synth.add(v == (res != other_res))

    def add_cross_instance_constr(self, last_instance):
        if self.options.no_const_expr and last_instance > 0:
            for insn in range(self.n_inputs, self.length - 1):
                for op in self.op_enum.item_to_cons:
                    self.synth.add(self.var_not_all_eq(insn, op.out_type, last_instance))

        if self.options.no_semantic_eq:
            for insn in range(self.n_inputs, self.length - 1):
                for op in self.op_enum.item_to_cons:
                    for other in range(0, insn):
                        for other_op in self.op_enum.item_to_cons:
                            if other_op.out_type != op.out_type:
                                continue
                            self.synth.add(self.var_not_eq_pair(insn, other, op.out_type, last_instance))

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
        self.synth.add(And([ precond, phi ]))

    def create_prg(self, model):
        s = self.orig_spec
        def prep_opnds(insn, tys):
            for _, opnd, c, cv in self.iter_opnd_info_struct(insn, tys):
                if is_true(model[c]):
                    assert not model[cv] is None
                    yield (True, model[cv])
                else:
                    assert not model[opnd] is None, str(opnd) + str(model)
                    yield (False, model[opnd].as_long())
        insns = []
        for insn in range(self.n_inputs, self.length - 1):
            val    = model.evaluate(self.var_insn_op(insn), model_completion=True)
            op     = self.op_enum.get_from_model_val(val)
            opnds  = [ v for v in prep_opnds(insn, op.in_types) ]
            insns += [ (op, opnds) ]
        outputs      = [ v for v in prep_opnds(self.out_insn, self.out_tys) ]
        s = self.orig_spec
        return Prg(insns, outputs, s.outputs, s.inputs)

    def prg_constraints(self, prg):
        """Yields constraints that represent a given program."""
        for i, (op, params) in enumerate(prg.insns):
            insn_nr = self.n_inputs + i
            val = self.op_enum.get_from_op(op)
            yield self.var_insn_op(insn_nr) == val
            tys  = op.in_types
            for (is_const, p), v_is_const, v_opnd, v_const_val \
                in zip(params,
                       self.var_insn_opnds_is_const(insn_nr),
                       self.var_insn_opnds(insn_nr),
                       self.var_insn_op_opnds_const_val(insn_nr, tys)):
                yield v_is_const == is_const
                if is_const:
                    yield v_const_val == p
                else:
                    yield v_opnd == p

    def exclude_program(self, prg):
        self.synth.add(Not(And([ p for p in self.prg_constraints(prg) ])))

@dataclass(frozen=True)
class _LenBase(util.HasDebug, solvers.HasSolver):
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

    opt_insn_order_op: bool = True
    """Include the operator into the instruction order optimization."""

    bitvec_enum: bool = True
    """Use bitvector encoding of enum types."""

    dump_constr: bool = False
    """Dump the synthesis constraints to a file."""

    dump_model: bool = False
    """Dump the model to a file."""

    exact: bool = False
    """Each operator appears exactly as often as indicated (overrides size_range)."""

    size_range: Tuple[int, int] = (0, 10)
    """Range of program sizes to try."""

    def synth_all(self, task: Task):
        self.debug(2, task)
        if self.exact:
            assert all(not v is None for v in task.ops.values())
            l = h = sum(f for f in task.ops.values())
        else:
            l, h = self.size_range
        for n_insns in range(l, h + 1):
            synth = self.create_synth(task, n_insns)
            for prg, stats in synth.synth_all_prgs():
                yield prg, stats

    def synth(self, task: Task):
        time = 0
        all_stats = []
        for prg, stats in self.synth_all(task):
            time += stats['time']
            all_stats += [ stats ]
            if not prg is None:
                return prg, { 'time': time, 'stats': all_stats }

class _LenCegis(_LenConstraints, CegisBaseSynth, AllPrgSynth):
    def __init__(self, options, task: Task, n_insns: int):
        CegisBaseSynth.__init__(self, task.spec, options.debug)
        _LenConstraints.__init__(self, options, task, n_insns)

        # add initial samples
        # for the no_const_expr option, we need at least two samples
        n_init_samples = max(2 if options.no_const_expr else 1, options.init_samples)
        for s in task.spec.eval.sample_n(n_init_samples):
            self._add_sample(s)

@dataclass(frozen=True)
class LenCegis(_LenBase):
    """Cegis synthesizer that finds the shortest program."""

    no_const_expr: bool = False
    """Prevent non-constant constant expressions (e.g. x - x)."""

    no_semantic_eq: bool = False
    """Forbid placing two semantically equivalent instructions in the program (e.g. x << 1 and x + x)."""

    init_samples: int = 1
    """Number of initial samples to use for the synthesis."""

    def create_synth(self, task: Task, n_insns: int):
        return _LenCegis(self, task, n_insns)

class _FA(_LenConstraints, AllPrgSynth):
    def __init__(self, options, task: Task, n_insns: int):
        self.exist_vars = set()
        _LenConstraints.__init__(self, options, task, n_insns)

    @lru_cache
    def get_var(self, ty, name, instance=None):
        res = super().get_var(ty, name, instance)
        if not instance is None:
            self.exist_vars.add(res)
        return res

    def synth_prg(self):
        ins  = [ self.var_input_res(i, 'fa') for i in range(self.n_inputs) ]
        self.exist_vars.difference_update(ins)
        self.add_constr_instance('fa')
        self.add_constr_io_spec('fa', ins)
        s = Solver()
        s.add(ForAll(ins, Exists(list(self.exist_vars), And([a for a in self.synth.assertions()]))))

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
            stat['time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = s.model()
            prg = self.create_prg(m)
            self.d(4, 'model: ', m)
            return prg, stat
        else:
            return None, stat

@dataclass(frozen=True)
class LenFA(_LenBase):
    """Synthesizer that uses a forall constraint and finds the shortest program."""

    def create_synth(self, task: Task, n_insns: int):
        return _FA(self, task, n_insns)

class _OptCegis(_LenCegis, AllPrgSynth):
    def __init__(self, options, task: Task, n_insns: int):
        # if required add an additional identify operator to the operators
        self.id = Func('id', task.spec.outputs[0])
        task.ops[self.id] = None

        super().__init__(options, task, n_insns)

        # add the constraints on the id operator
        self.add_constr_id_wfp()

        options.optimizer.add_constraint(self)

    def add_constr_id_wfp(self):
        solver = self.synth
        id_id = self.op_enum.item_to_cons[self.id]

        # id is only used for the output as a last instruction
        # iterate over all instructions used in output
        for insn in range(self.n_inputs, self.out_insn):
            # get operator of instruction
            op_var = self.var_insn_op(insn)
            # every following instruction is id
            cons = [ self.var_insn_op(f_insn) == id_id for f_insn in range(insn + 1, self.out_insn)]
            # if the operator is id, every following insn operator is also id (if there is at least one following insn)
            solver.add(Implies(op_var == id_id, And(cons)))

        # id operators can only use the result of the previous instruction as a result
        for insn in range(self.n_inputs, self.out_insn):
            opnds = list(self.var_insn_opnds(insn))
            solver.add(Implies(self.var_insn_op(insn) == id_id, opnds[0] == insn - 1))

        # only first id may receive a constant as an operand
        # iterate over all instructions used in output
        for insn in range(self.n_inputs, self.out_insn):
            # get operator of instruction
            op_var = self.var_insn_op(insn)
            # if operator is id AND  >=one of the operands is a constant
            cond = And(op_var == id_id, Or([var == True for var in self.var_insn_opnds_is_const(insn)]))
            # then every previous instruction may not be id
            cons = [ self.var_insn_op(f_insn) != id_id for f_insn in range(self.n_inputs, insn)]
            solver.add(Implies(cond, And(cons)))

@dataclass(frozen=True)
class OptCegis(LenCegis, HasOptimizer):
    """Cegis synthesizer that finds the program optimal for a provided metric"""

    solver: solvers._OPT_SOLVERS = solvers.InternalZ3Opt()
    """Use the Z3 Optimize API to minimize the cost function."""

    def synth(self, task: Task):
        with util.timer() as elapsed:
            prg, stats = _OptCegis(self, task, self.size_range[1]).synth_prg()
            return prg, { 'time': elapsed(), 'stats': stats }

class _ConstantSolver:
    """Interface for constant solvers"""

    def __init__(self, options, task: Task, base_program: Prg):
        self.options        = options
        self.synth          = options.solver.create(theory=task.theory)
        self.prg            = base_program
        self.const_map      = {}
        self.task           = task
        self.sample_counter = 0
        self.spec           = task.spec

    def get_const_var(self, ty, insn, opnd):
        return Const(f'|insn_{insn}_opnd_{opnd}_{ty}_const_val|', ty)

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
                  model.evaluate(self.const_map[insn][n_opnd], model_completion=True) if is_const else value
                  ) for (n_opnd, (is_const, value)) in enumerate(args) ]
            ) for (insn, (op, args)) in enumerate(self.prg.insns) ]

        outputs = [ (is_const,
                     model[self.const_map[len(self.prg.insns)][n_out]] if is_const else value
                    ) for (n_out, (is_const, value)) in enumerate(self.prg.outputs)]

        return Prg(insns, outputs, self.task.spec.outputs, self.task.spec.inputs)


class _CegisConstantSolver(_ConstantSolver, CegisBaseSynth):
    """Synthesizer that implements CEGIS solver interface to find the constants in the program."""

    def __init__(self, options, task: Task, base_program: Prg):
        CegisBaseSynth.__init__(self, task.spec, options.debug)
        _ConstantSolver.__init__(self, options, task, base_program)

        # add initial samples
        for s in task.spec.eval.sample_n(1):
            self._add_sample(s)

    def add_cross_instance_constr(self, instance):
        pass

    def _add_sample(self, sample):
        # TODO: support for constant set restrictions
        prg = self.prg
        assert prg is not None

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
            self.synth.add(And([ precond, phi ]))
        # add program constraints
        for constraint in prg.eval_clauses_external(in_vars, out_vars, const_to_var=self.const_to_var, intermediate_vars=[]):
            self.synth.add(constraint)
        self.sample_counter += 1


class _FAConstantSolver(_ConstantSolver):
    def do_synth(self):
        constraints = []

        in_vars, out_vars = self.create_in_out_vars(0)
        precond, phi = self.spec.instantiate(out_vars, in_vars)
        constraints.append(Implies(precond, phi))

        intermediate_vars = list(out_vars)

        # add program constraints
        for constraint in self.prg.eval_clauses_external(in_vars, out_vars,
                const_to_var=self.const_to_var, intermediate_vars=intermediate_vars):
            constraints.append(constraint)

        if len(intermediate_vars) > 0:
            self.synth.add(ForAll(in_vars, Exists(list(intermediate_vars), And(constraints))))
        else:
            self.synth.add(ForAll(in_vars, And(constraints)))

        stat = {}
        synth_time, model = self.synth.solve()
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
class Downscale(LenCegis):
    """Synthesizer that first solve the task on a smaller bitwidth, then scales it up."""

    target_bitwidth: list[int] = field(default_factory=lambda: [4, 8])
    """Comma separated list of target bitwidths (integer) to scale down to."""

    constant_finder_use_cegis: bool = True
    """Whether to use CEGIS to find the constants in the upscaling process."""

    keep_const_map: bool = False
    """Whether to keep the constant map for the downscaling process."""

    def synth(self, task: Task):
        combined_stats = []

        with util.timer() as overall:
            # try to downscale
            for target_bw in self.target_bitwidth:
                # scale down the task
                try:
                    scaled_task = transform_task_to_bitwidth(task, target_bw, self.keep_const_map)
                except Exception as e:
                    self.debug(1, f"Failed to scale down the task to bitwidth {target_bw}: {e}")
                    continue

                # run the synthesis on the scaled task
                prg, stats = super().synth(scaled_task.transformed_task)
                combined_stats += { 'bw': target_bw, 'stats': stats }
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
                        prg, stats = _CegisConstantSolver(self, task, prg).synth_prg()
                    else:
                        # find the constants using FA
                        solver = _FAConstantSolver(self, task, prg)
                        prg, stats = solver.do_synth()
                        stats = [ stats ]

                    combined_stats += [ { 'const_bw': target_bw, 'time': elapsed(), 'iterations': stats } ]

                if prg is not None:
                    return prg, { 'time': overall(), 'stats': combined_stats }

            # Fallback to normal synthesis if normal synthesis fails
            self.debug(1, f"Fallback to normal synthesis")
            prg, stats = super().synth(task)
            return prg, stats | { 'stats': combined_stats }
