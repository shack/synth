from functools import lru_cache
from collections import defaultdict
from dataclasses import dataclass, field

from z3 import *

from synth.cegis import cegis
from synth.spec import Func, Prg, Problem, SynthFunc
from synth.objective import HasObjective, Length
from synth.downscaling import transform_problem_to_bitwidth
from synth import solvers, util

import enum

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

    def add_range_constr(self, var, res):
        res.append(ULT(var, len(self.item_to_cons)))
        return res

class AllPrgSynth:
    def synth_all_prgs(self):
        while True:
            prg, stats = self.synth_prg()
            if prg is None:
                return
            else:
                yield prg, stats
                self.exclude_program(prg)

class _LenConstraints:
    def __init__(self, options, name: str, func: SynthFunc, n_insns: int, use_nop: bool = False):
        """Synthesize a program that computes the given functions.

        Attributes:
        options: Options to the synthesis.
        task: The synthesis task.
        n_insn: Number of instructions in the program.
        """
        self.name    = name
        self.func    = func
        self.options = options
        self.n_insns = n_insns

        if type(func.ops) == list or type(func.ops) == set:
            ops = { op: None for op in func.ops }
        else:
            ops = dict(func.ops)

        if use_nop or len(ops) == 0:
            # if we want to use a nop instruction or if there's an empty set of operators ...
            self.nop = Func('$nop', Const('$nop_y', self.func.out_types[0]), inputs=())
            ops[self.nop] = None
        else:
            self.nop = None

        assert len(ops) > 0, 'no operators to synthesize with'

        self.ops       = ops
        self.in_tys    = self.func.in_types
        self.out_tys   = self.func.out_types
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
        self.ln_sort = util.bv_sort(self.length)
        self.bl_sort = BoolSort()

        self.n_insn_var = self.get_var(self.ln_sort, 'n_insns')
        self.length_var = self.get_var(self.ln_sort, 'length_var')

        # set options
        self.d = options.debug

    def _get_id_insn(self):
        return self.nop

    @lru_cache
    def get_var(self, ty, name, instance=None):
        prefix = f'{self.name}_{name}'
        name = f'|{prefix}_{instance}|' if not instance is None else f'|{prefix}|'
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

    def vars_out_in(self, instance):
        return [ v for v in self.var_outs_val(instance) ], [ self.var_input_res(i, instance) for i in range(self.n_inputs) ]

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

    def _add_constr_insn_count(self, res):
        # constrain the number of usages of an operator if specified
        for op, op_cons in self.op_enum.item_to_cons.items():
            if not (f := self.ops[op]) is None:
                a = [ self.var_insn_op(insn) == op_cons \
                    for insn in range(self.n_inputs, self.length - 1) ]
                if a:
                    res.append(AtMost(*a, f))
                    if self.options.exact:
                        res.append(AtLeast(*a, f))
        return res

    def _add_constr_const_count(self, res):
        const_map = self.func.const_map
        max_const = self.func.max_const

        # If supplied with an empty set of constants, we don't allow any constants
        if not const_map is None and len(const_map) == 0:
            max_const = 0

        # Add a constraint for the maximum amount of constants if specified.
        ran = range(self.n_inputs, self.length)
        if not max_const is None and len(ran) > 0:
            res.append(AtMost(*[ v for insn in ran \
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
                        res.append(Implies(c, Or(eqs)))
            for c, constr in const_constr_map.items():
                if not (n := const_map[c]) is None:
                    res.append(AtMost(*constr, n))
                    if self.options.exact:
                        res.append(AtLeast(*constr, n))
        return res

    def _add_nop_length_constr(self, res):
        if self.nop:
            # make sure that nop instructions are at the end of the program
            op_id_nop = self.op_enum.get_from_op(self._get_id_insn())
            res.append(ULE(self.n_inputs, self.n_insn_var))
            res.append(ULE(self.n_insn_var, self.out_insn))
            for insn in range(self.n_inputs, self.out_insn):
                res.append(If(self.var_insn_op(insn) == op_id_nop,
                           ULE(self.n_insn_var, insn),
                           ULT(insn, self.n_insn_var)))
            # and that the output instruction cannot use nop outputs
            for out in self.var_insn_opnds(self.out_insn):
                res.append(ULT(out, self.n_insn_var))
        else:
            res.append(self.n_insn_var == self.out_insn)
        res.append(self.n_insn_var - self.n_inputs == self.length_var)
        return res

    def _add_constr_wfp(self, res):
        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for insn in range(self.length):
            for v in self.var_insn_opnds(insn):
                res.append(ULT(v, insn))
        # Add bounds for the operand ids
        for insn in range(self.n_inputs, self.length - 1):
            self.op_enum.add_range_constr(self.var_insn_op(insn), res)
        # Add a constraint that pins potentially unused operands to the last
        # one. This is important because otherwise the no_dead_code constraints
        # will not work.
        for insn in range(self.n_inputs, self.length - 1):
            for op, op_id in self.op_enum.item_to_cons.items():
                if op.arity < self.max_arity:
                    opnds = list(self.var_insn_opnds(insn))
                    res.append(Implies(self.var_insn_op(insn) == op_id, \
                               And([ opnds[op.arity - 1] == x for x in opnds[op.arity:] ])))
        # Add constraints on the instruction counts
        self._add_constr_insn_count(res)
        # Add constraints on constant usage
        self._add_constr_const_count(res)
        # Add constraints for nop instructions
        self._add_nop_length_constr(res)
        return res

    def _add_constr_ty(self, res):
        if len(self.ty_enum) <= 1:
            # we don't need constraints if there is only one type
            return res

        # for all instructions that get an op
        # add constraints that set the type of an instruction's operand
        # and the result type of an instruction
        types = self.ty_enum.item_to_cons
        for insn in range(self.n_inputs, self.length - 1):
            for op, op_id in self.op_enum.item_to_cons.items():
                # add constraints that set the result type of each instruction
                res.append(Implies(self.var_insn_op(insn) == op_id, \
                           self.var_insn_res_type(insn) == types[op.out_type]))
                # add constraints that set the type of each operand
                for op_ty, v in zip(op.in_types, self.var_insn_opnds_type(insn)):
                    res.append(Implies(self.var_insn_op(insn) == op_id, v == types[op_ty]))

        # define types of inputs
        for inp, ty in enumerate(self.in_tys):
            res.append(self.var_insn_res_type(inp) == types[ty])

        # define types of outputs
        for v, ty in zip(self.var_insn_opnds_type(self.out_insn), self.out_tys):
            res.append(v == types[ty])

        # constrain types of outputs
        for insn in range(self.n_inputs, self.length):
            for other in range(0, insn):
                for opnd, c, ty in zip(self.var_insn_opnds(insn), \
                                    self.var_insn_opnds_is_const(insn), \
                                    self.var_insn_opnds_type(insn)):
                    res.append(Implies(Not(c), Implies(opnd == other, \
                               ty == self.var_insn_res_type(other))))
            self.ty_enum.add_range_constr(self.var_insn_res_type(insn), res)
        return res

    def _add_constr_opt(self, res):
        def opnd_set(insn):
            sz  = self.length + self.op_sort.size()
            ext = sz - self.ln_sort.size()
            assert ext >= 0
            r = BitVecVal(0, sz)
            o = BitVecVal(1, sz)
            for opnd in self.var_insn_opnds(insn):
                r |= o << ZeroExt(ext, opnd)
            r = (r << BitVecVal(self.op_sort.size(), sz)) \
                | ZeroExt(sz - self.op_sort.size(), self.var_insn_op(insn))
            return r

        if self.options.opt_insn_order:
            for insn in range(self.n_inputs, self.out_insn - 1):
                res.append(ULE(opnd_set(insn), opnd_set(insn + 1)))

        for insn in range(self.n_inputs, self.out_insn):
            op_var = self.var_insn_op(insn)
            opnds = list(self.var_insn_opnds(insn))

            for op, op_id in self.op_enum.item_to_cons.items():
                is_cnst = list(v for v in self.var_insn_opnds_is_const(insn))[:op.arity]
                # if operator is commutative, force the operands to be in ascending order
                if self.options.opt_commutative and op.is_commutative:
                    c = [ ULE(l, u) for l, u in zip(opnds[:op.arity - 1], opnds[1:]) ]
                    res.append(Implies(op_var == op_id, And(c)))

                if self.options.opt_const and len(is_cnst) > 0:
                    if op.arity == 2 and op.is_commutative:
                        # Binary commutative operators have at most one constant operand
                        # Hence, we pin the first operand to me non-constant
                        not_const = is_cnst[0]
                    else:
                        # Otherwise, we require that at least one operand is non-constant
                        not_const = And(is_cnst)
                    res.append(Implies(op_var == op_id, Not(not_const)))

            # Computations must not be replicated: If an operation appears again
            # in the program, at least one of the operands must be different from
            # a previous occurrence of the same operation.
            if self.options.opt_cse:
                for other in range(self.n_inputs, insn):
                    un_eq = [ p != q for p, q in zip(self.var_insn_opnds(insn), \
                                                     self.var_insn_opnds(other)) ]
                    if len(un_eq) > 0:
                        res.append(Implies(op_var == self.var_insn_op(other), Or(un_eq)))

        # no dead code: each produced value is used
        if self.options.opt_no_dead_code:
            for prod in range(self.n_inputs, self.out_insn):
                opnds = [ Implies(ULT(prod, self.n_insn_var), And([ prod == v, Not(c) ])) \
                            for cons in range(prod + 1, self.length) \
                            for c, v in zip(self.var_insn_opnds_is_const(cons), \
                                            self.var_insn_opnds(cons)) ]
                if len(opnds) > 0:
                    res.append(Or(opnds))

        return res

    def _add_constr_conn(self, insn, tys, instance, res):
        for ty, l, v, c, cv in self.iter_opnd_info(insn, tys, instance):
            # if the operand is a constant, its value is the constant value
            res.append(Implies(c, v == cv))
            # else, for other each instruction preceding it ...
            for other in range(insn):
                r = self.var_insn_res(other, ty, instance)
                # ... the operand is equal to the result of the instruction
                res.append(Implies(Not(c), Implies(l == other, v == r)))
        return res

    def _add_constr_instance(self, instance, res):
        # for all instructions that get an op
        for insn in range(self.n_inputs, self.length - 1):
            # add constraints to select the proper operation
            op_var = self.var_insn_op(insn)
            for op, op_id in self.op_enum.item_to_cons.items():
                res_var = self.var_insn_res(insn, op.out_type, instance)
                opnds = list(self.var_insn_opnds_val(insn, op.in_types, instance))
                precond, phi = op.instantiate([ res_var ], opnds)
                res.append(Implies(op_var == op_id, And([ precond, phi ])))
            # connect values of operands to values of corresponding results
            for ty in self.types:
                self._add_constr_conn(insn, [ ty ] * self.max_arity, instance, res)
        # add connection constraints for output instruction
        self._add_constr_conn(self.out_insn, self.out_tys, instance, res)
        return res

    def add_program_constraints(self, res):
        self._add_constr_wfp(res)
        self._add_constr_ty(res)
        self._add_constr_opt(res)
        return res

    def instantiate(self, instance, args, res):
        self._add_constr_instance(instance, res)
        inst_outs, inst_ins = self.vars_out_in(instance)
        for var, val in zip(inst_ins, args):
            res.append(var == val)
        return res, inst_outs

    def create_prg(self, model):
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
        outputs = [ v for v in prep_opnds(self.out_insn, self.out_tys) ]
        return Prg(self.func, insns, outputs)

    def prg_constraints(self, prg):
        """Yields constraints that represent a given program."""
        for i, (op, params) in enumerate(prg.insns):
            insn_nr = self.n_inputs + i
            val = self.op_enum.get_from_op(op)
            yield self.var_insn_op(insn_nr) == val
            tys  = op.sig.in_types
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

    def exclude_program_constr(self, prg, res):
        res.append(Not(And([ p for p in self.prg_constraints(prg) ])))
        return res

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

    nops: bool = False
    """Allow use of nop instructions."""

    exact: bool = False
    """Each operator appears exactly as often as indicated (overrides size_range)."""

    size_range: tuple[int, int] = (0, 10)
    """Range of program sizes to try."""

    detailed_stats: bool = False
    """Record detailed statistics during synthesis."""

    def get_range(self, problem: Problem):
        if self.exact:
            assert len(problem.funcs) == 1, 'exact size only supported for single function synthesis'
            fun = next(iter(problem.funcs))
            assert all(not v is None for v in fun.ops.values())
            n = sum(f for f in fun.ops.values())
            return n, n
        else:
            return self.size_range

    def synth_all(self, func: SynthFunc):
        raise NotImplementedError()

    def _iter_len_synths(self, problem: Problem):
        raise NotImplementedError()

    def _create_nop_synth(self, name: str, f: SynthFunc, max_len: int):
        raise NotImplementedError()

    def synth_prgs_nops(self, problem: Problem, add_constraints=None):
        lo, hi = self.get_range(problem)
        solver = self.solver.create(theory=problem.theory)
        synths = { name: self._create_nop_synth(name, f, hi) for name, f in problem.funcs.items() }

        for s in synths.values():
            s.add_program_constraints(solver)

        samples = problem.constraint.counterexample_eval.sample_n(self.init_samples)
        prgs = None
        iterations = []
        with util.timer() as elapsed:
            for n_insns in range(lo, hi + 1):
                self.debug('len', f'size {n_insns}')
                solver.push()
                for s in synths.values():
                    solver.add(s.length_var == n_insns)
                prgs, stats, res_samples = cegis(solver, problem.constraint, synths, samples,
                                                 self.debug, self.detailed_stats)
                if self.keep_samples:
                    samples = res_samples
                solver.pop()
                iterations += [ stats ]
                if not prgs is None:
                    break
        return prgs, { 'time': elapsed(), 'iterations': iterations }

    def synth_prgs_len_iter(self, problem: Problem, add_constraints=None):
        prgs = None
        iterations = []
        with util.timer() as elapsed:
            for synth in self._iter_len_synths(problem):
                if add_constraints:
                    add_constraints(synth)
                prgs, stats = synth.synth_prgs()
                iterations += [ stats ]
                if not prgs is None:
                    break
        return prgs, { 'time': elapsed(), 'iterations': iterations }

    def synth_prgs(self, problem: Problem, add_constraints=None):
        if self.nops or len(problem.funcs) > 1:
            # if we want to use nops or if we are synthesizing multiple functions
            return self.synth_prgs_nops(problem, add_constraints)
        else:
            # else, we use the standard length iteration
            return self.synth_prgs_len_iter(problem, add_constraints)

@dataclass
class _LenCegisImpl:
    options: _LenBase
    problem: Problem
    n_insns: int
    samples: list = field(default_factory=list)

    def synth_prgs(self):
        solver = self.options.solver.create(theory=self.problem.theory)
        synths = { name: _LenConstraints(self.options, name, f, self.n_insns) for name, f in self.problem.funcs.items() }

        for s in synths.values():
            s.add_program_constraints(solver)

        prg, stats, self.samples = cegis(solver, self.problem.constraint, synths, self.samples,
                                         d=self.options.debug, detailed_stats=self.options.detailed_stats)
        return prg, stats

@dataclass(frozen=True)
class LenCegis(_LenBase):
    """Cegis synthesizer that finds the shortest program."""

    init_samples: int = 1
    """Number of initial samples to use for the synthesis."""

    keep_samples: bool = True
    """Keep samples across different program lengths."""

    def _create_nop_synth(self, name: str, f: SynthFunc, max_len: int):
        return _LenConstraints(self, name, f, max_len, use_nop=True)

    def _iter_len_synths(self, problem: Problem):
        l, h = self.get_range(problem)
        samples = problem.constraint.counterexample_eval.sample_n(self.init_samples)
        for n_insns in range(l, h + 1):
            self.debug('len', f'size {n_insns}')
            # TODO: synthesizing multiple functions with different lengths does not work yet
            synth = _LenCegisImpl(self, problem, n_insns, samples)
            yield synth
            samples = synth.samples

class _FAConstraints(_LenConstraints, AllPrgSynth):
    def __init__(self, options, name, func: SynthFunc, n_insns: int, use_nop: bool):
        self.exist_vars = set()
        _LenConstraints.__init__(self, options, name, func, n_insns, use_nop)

    @lru_cache
    def get_var(self, ty, name, instance=None):
        res = super().get_var(ty, name, instance)
        if not instance is None:
            self.exist_vars.add(res)
        return res

@dataclass
class _FAImpl:
    options: _LenBase
    problem: Problem
    n_insns: int

    def synth_prgs(self):
        d           = self.options.debug
        constr      = self.problem.constraint
        funcs       = self.problem.funcs
        exist_vars  = set()
        constraints = []

        use_nops = self.options.nops or len(funcs) > 1
        synths = { name: _FAConstraints(self.options, name, f, self.n_insns, use_nops) for name, f in funcs.items() }
        constr.add_instance_constraints('fa', synths, constr.params, constraints)
        for name, applications in constr.function_applications.items():
            s = synths[name]
            s.add_program_constraints(constraints)
            exist_vars.update(s.exist_vars)
            for _, args in applications:
                exist_vars.difference_update(args)

        s = self.options.solver.create(theory=self.problem.theory)
        s.add(ForAll(constr.params, Exists(list(exist_vars), And(constraints))))

        stat = {}
        if self.options.detailed_stats:
            stat['synth_constraint'] = str(s)
        with util.timer() as elapsed:
            res = s.check()
            synth_time = elapsed()
            d('time', f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = s.model()
            prgs = { name: c.create_prg(m) for name, c in synths.items() }
            stat['success'] = True
            if self.options.detailed_stats:
                stat['synth_model'] = str(m)
                stat['prgs'] = str(prgs)
            return prgs, stat
        else:
            return None, stat | { 'success': False }

@dataclass(frozen=True)
class LenFA(_LenBase):
    """Synthesizer that uses a forall constraint and finds the shortest program."""

    def _create_nop_synth(self, name: str, f: SynthFunc, max_len: int):
        return _FAConstraints(self, name, f, max_len, use_nop=True)

    def _iter_len_synths(self, problem):
        l, h = self.get_range(problem)
        for n_insns in range(l, h + 1):
            self.debug('len', f'size {n_insns}')
            yield _FAImpl(self, problem, n_insns)

'''
class _OptCegisImpl(_LenCegisImpl, AllPrgSynth):
    def __init__(self, options, task: Task, n_insns: int):
        # if required add an additional identify operator to the operators
        self.id = Func('id', task.spec.outputs[0])
        task.ops[self.id] = None

        super().__init__(options, task, n_insns)

        # add the constraints on the id operator
        self.add_constr_id_wfp()
        self.goal = options.objective.add_constraint(self)

    def _get_id_insn(self):
        return self.id

    def add_constr_id_wfp(self):
        solver = self.solver
        id_id = self.op_enum.item_to_cons[self.id]

        # id is only used for the output as a last instruction
        # iterate over all instructions used in output
        for insn in range(self.n_inputs, self.out_insn - 1):
            # get operator of instruction
            op_var = self.var_insn_op(insn)
            # every following instruction is id
            # solver.add(Implies(op_var == id_id, And(cons)))
            solver.add(Implies(op_var == id_id, self.var_insn_op(insn + 1) == id_id))

        # id operators can only use the result of the previous instruction as a result
        for insn in range(self.n_inputs, self.out_insn):
            opnds = list(self.var_insn_opnds(insn))
            solver.add(Implies(self.var_insn_op(insn) == id_id, opnds[0] == insn - 1))

        # only first id may receive a constant as an operand
        # iterate over all instructions used in output
        for insn in range(self.n_inputs + 1, self.out_insn):
            # get operator of instruction
            pr_var = self.var_insn_op(insn - 1)
            solver.add(Implies(pr_var == id_id, And([ Not(c) for c in self.var_insn_opnds_is_const(insn) ])))

class MultiObjectivePriority(enum.Enum):
    LEX = enum.auto()
    PARETO = enum.auto()

class MultiObjective(enum.Enum):
    OBJ_ONLY = enum.auto()
    LEN_FST = enum.auto()
    LEN_SND = enum.auto()

@dataclass(frozen=True)
class OptCegis(LenCegis, HasObjective, solvers.HasSolver):
    """Cegis synthesizer that finds the optimal program for a given metric."""

    multi_obj: MultiObjective = MultiObjective.OBJ_ONLY
    """Multi-Optimization objective."""

@dataclass(frozen=True)
class OptSolver(OptCegis):
    priority: MultiObjectivePriority = MultiObjectivePriority.LEX
    """Priority for multi-objective optimization."""

    def synth(self, task: Task):
        synth = _OptCegisImpl(self, task, self.size_range[1])
        assert self.solver.has_minimize(), f"Solver {self.solver} does not support optimization"
        match self.multi_obj:
            case MultiObjective.LEN_FST:
                synth.solver.minimize(Length().add_constraint(synth))
                synth.solver.minimize(synth.goal)
                synth.solver.set(priority=self.priority.name.lower())
            case MultiObjective.LEN_SND:
                synth.solver.minimize(synth.goal)
                synth.solver.minimize(Length().add_constraint(synth))
                synth.solver.set(priority=self.priority.name.lower())
            case MultiObjective.OBJ_ONLY:
                synth.solver.minimize(synth.goal)
        with util.timer() as elapsed:
            prg, stats = synth.synth_prg()
        return prg, stats | { 'time': elapsed(), 'stats': stats }

@dataclass(frozen=True)
class OptSearch(OptCegis):
    start_search: Optional[int] = 10
    """Starting point for binary search."""

    def _search_obj(self, task: Task, length: int):
        def eval(m):
            synth.solver.push()
            synth.solver.add(synth.goal < m)
            prg, stats = synth.synth_prg()
            synth.solver.pop()
            return None if prg is None else str(prg), stats
        def is_lt(res):
            return res[0] is not None

        synth = _OptCegisImpl(self, task, length)
        with util.timer() as elapsed:
            lower, upper = util.find_start_interval(eval, is_lt, start=self.start_search, debug=self.debug)
            val, results = util.binary_search(eval, is_lt, lower, upper, debug=self.debug)
            synth.solver.push()
            synth.solver.add(synth.goal == val)
            prg, stats = synth.synth_prg()
            synth.solver.pop()
            assert prg is not None
            time = elapsed()
        return val, prg, {
            'time': time,
            'iterations': results,
            'final': stats
        }

    def synth(self, task: Task):
        match self.multi_obj:
            case MultiObjective.LEN_FST:
                # Find the shortest program first
                synth = LenCegis(self, size_range=self.size_range)
                with util.timer() as elapsed:
                    prg, initial_stats = synth.synth(task)
                    start_time = elapsed()
                # if there is none, exit
                if prg is None:
                    return None, {
                        'time': start_time,
                        'success': False,
                        'iterations': [],
                        'init_stats': initial_stats,
                    }
                else:
                    # now, find the best program according to the other objective
                    val, prg, stats = self._search_obj(task, len(prg))
                    return prg, {
                        'minimum_length': len(prg),
                        'objective_value': val,
                        'success': True,
                        'time': stats['time'],
                        'init_stats': initial_stats,
                        'obj_stats': stats,
                    }

            case MultiObjective.LEN_SND | MultiObjective.OBJ_ONLY:
                def add_constraints(synth):
                    goal = self.objective.add_constraint(synth)
                    synth.solver.add(goal == val)
                with util.timer() as elapsed:
                    val, prg, obj_stats = self._search_obj(task, self.size_range[1])
                    self.debug('opt', f'found program with optimal objective {val}: {prg}')
                    if prg is None:
                        return None, {
                            'time': elapsed(),
                            'success': False,
                            'obj_stats': obj_stats,
                        }
                    else:
                        prg, stats = super(LenCegis, self).synth(task, add_constraints=add_constraints)
                        return prg, {
                            'time': elapsed(),
                            'success': not prg is None,
                            'objective_value': val,
                            'obj_stats': obj_stats,
                            'len_stats': stats,
                        }
'''

class _ConstantSynth:
    """Interface for constant solvers"""

    def __init__(self, func: SynthFunc, base_program: Prg):
        self.prg            = base_program
        self.const_map      = {}
        self.func           = func

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

    def instantiate(self, instance_id, args, res):
        out_vars = [ Const(f'out_{i}_{instance_id}', ty)
                     for i, ty in enumerate(self.func.out_types) ]
        for c in self.prg.eval_clauses(args, out_vars, instance_id=instance_id,
                                       const_translate=self.const_to_var):
            res.append(c)
        return res, out_vars

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

        return Prg(self.func, insns, outputs)

class CegisConstantSolver:
    def __call__(self, solver: Solver, problem: Problem, base_prgs: dict[str, Prg],
                 d: util.Debug = util.no_debug, detailed_stats: bool = False):
        synths = { name: _ConstantSynth(func, base_prgs[name]) for name, func in problem.funcs.items() }
        prgs, stats, _ = cegis(solver, problem.constraint, synths, initial_samples=[],
                               d=d, detailed_stats=detailed_stats)
        return prgs, stats

class FAConstantSolver:
    def __call__(self, solver: Solver, problem: Problem, base_prgs: dict[str, Prg],
                 d: util.Debug = util.no_debug, detailed_stats: bool = False):
        constr = problem.constraint
        synths = { name: _ConstantSynth(func, base_prgs[name]) for name, func in problem.funcs.items() }
        constraints = []
        constr.add_instance_constraints('fa', synths, constr.params, constraints)
        solver.add(ForAll(constr.params, And(constraints)))
        stat = {}
        if self.options.detailed_stats:
            stat['synth_constraint'] = str(s)
        with util.timer() as elapsed:
            res = solver.check()
            synth_time = elapsed()
            d('time', f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = solver.model()
            prgs = { name: c.create_prg(m) for name, c in synths.items() }
            stat['success'] = True
            if self.options.detailed_stats:
                stat['synth_model'] = str(m)
                stat['prgs'] = str(prgs)
            return prgs, stat
        else:
            return None, stat | { 'success': False }

@dataclass(frozen=True)
class Downscale(util.HasDebug):
    """Synthesizer that first solve the task on a smaller bitwidth, then scales it up."""

    target_bitwidth: list[int] = field(default_factory=lambda: [8])
    """Comma separated list of target bit widths (integer) to scale down to."""

    keep_const_map: bool = False
    """Whether to keep the constant map for the downscaling process."""

    constant_synth: CegisConstantSolver | FAConstantSolver = field(default_factory=lambda: CegisConstantSolver())
    """The constant synthesizer to use."""

    synth: LenCegis = LenCegis()
    """The base synthesiser to use for synthesis on the downscaled task."""

    def synth_prgs(self, problem: Problem):
        res_stats = {}

        with util.timer() as overall:
            # try to downscale
            for target_bw in self.target_bitwidth:
                # scale down the problem
                curr_stats = {}
                res_stats[target_bw] = curr_stats

                try:
                    scaled_problem = transform_problem_to_bitwidth(problem, target_bw, self.keep_const_map)
                    curr_stats['transform'] = True
                except Exception as e:
                    self.debug('downscale', f"Failed to scale down the problem to bitwidth {target_bw}: {e}")
                    curr_stats['transform'] = False
                    curr_stats['error'] = str(e)
                    continue

                # run the synthesis on the scaled problem
                prgs, stats = self.synth.synth_prgs(scaled_problem.transformed_problem)
                curr_stats |= { 'synth_success': not prgs is None, 'stats': stats }
                if prgs is None:
                    self.debug('downscale', f"Failed to synthesize program(s) for bitwidth {target_bw}")
                    continue

                # scale up
                # revert to original operators
                prgs = scaled_problem.prgs_with_original_operators(prgs)
                with util.timer() as elapsed:
                    self.debug('downscale', f"Proposed program(s) for bitwidth {target_bw}:\n{str(prgs)}")

                    solver = self.synth.solver.create(theory=problem.theory)
                    prgs, stats = self.constant_synth(solver, problem, prgs, d=self.synth.debug, detailed_stats=self.synth.detailed_stats)

                    curr_stats['const_finder'] = {
                        'time': elapsed(),
                        'stats': stats,
                        'success': not prgs is None
                    }
                if prgs is not None:
                    return prgs, { 'time': overall(), 'stats': res_stats, 'prg': str(prgs), 'fallback': False }

            # Fallback to normal synthesis if normal synthesis fails
            self.debug('downscale', f"Fallback to normal synthesis")
            prg, stats = self.synth.synth_prgs(problem)
            return prg, { 'time': overall(), 'stats': res_stats, 'prg': str(prg), 'fallback': True }