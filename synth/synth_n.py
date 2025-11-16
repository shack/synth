from functools import lru_cache
from collections import defaultdict
from dataclasses import dataclass, field

from z3 import *

from synth.cegis import cegis
from synth.spec import Func, Prg, Problem, SynthFunc
from synth.downscaling import transform_problem_to_bitwidth
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

class LenConstraints:
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

        self.ops        = ops
        self.in_tys     = self.func.in_types
        self.out_tys    = self.func.out_types
        self.n_inputs   = len(self.in_tys)
        self.n_outputs  = len(self.out_tys)
        self.out_insn   = self.n_inputs + self.n_insns # index of the out instruction
        self.length     = self.out_insn + 1
        self.max_arity  = max(op.arity for op in ops)
        self.arities    = [ 0 ] * self.n_inputs \
                        + [ self.max_arity ] * self.n_insns \
                        + [ self.n_outputs ]
        self.arity_bits = util.bv_width(self.max_arity)

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

    def constr_is_nop(self, insn):
        return self.var_insn_op(insn) == self.op_enum.item_to_cons[self.nop] \
            if self.nop else BoolVal(False)

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

    def var_tree_use(self, insn):
        n_bits = self.arity_bits + self.ln_sort.size()
        return self.get_var(BitVecSort(n_bits), f'insn_{insn}_user')

    def var_arity(self, insn):
        return self.get_var(util.bv_sort(self.max_arity), f'insn_{insn}_arity')

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
                    for opnd_ty, (_, _, c, cv) in zip(self.var_insn_opnds_type(insn),
                                                      self.iter_opnd_info_struct(insn, [ ty ] * self.max_arity)):
                        eqs = []
                        for v, _ in ty_const_map[ty]:
                            eqs += [ cv == v ]
                            const_constr_map[v] += [ And([c, cv == v ]) ]
                        if len(self.types) > 1:
                            res.append(Implies(opnd_ty == self.ty_enum.item_to_cons[ty], Or(eqs)))
                        else:
                            res.append(Or(eqs))
            for c, constr in const_constr_map.items():
                if not (n := const_map[c]) is None:
                    res.append(AtMost(*constr, n))
                    if self.options.exact:
                        res.append(AtLeast(*constr, n))
        return res

    def _add_nop_length_constr(self, res):
        if self.nop:
            # make sure that nop instructions are at the end of the program
            res.append(ULE(self.n_inputs, self.n_insn_var))
            res.append(ULE(self.n_insn_var, self.out_insn))
            for insn in range(self.n_inputs, self.out_insn):
                res.append(If(self.constr_is_nop(insn),
                           ULE(self.n_insn_var, insn),
                           ULT(insn, self.n_insn_var)))
            # and that the output instruction cannot use nop outputs
            for out in self.var_insn_opnds(self.out_insn):
                res.append(ULT(out, self.n_insn_var))
        else:
            res.append(self.n_insn_var == self.out_insn)
        res.append(self.n_insn_var - self.n_inputs == self.length_var)
        return res

    def _add_tree_constr(self, res):
        if self.options.tree:
            for insn in range(self.n_inputs, self.length - 1):
                for op, op_id in self.op_enum.item_to_cons.items():
                    res.append(Implies(self.var_insn_op(insn) == op_id,
                                       self.var_arity(insn) == op.arity))
                for i, opnd in enumerate(self.var_insn_opnds(insn)):
                    user = (insn << self.arity_bits) | i
                    for prod in range(self.n_inputs, insn):
                        res.append(Implies(ULT(i, self.var_arity(insn)),
                                           Implies(opnd == prod,
                                                   self.var_tree_use(prod) == user)))
        return res

    def _add_constr_params(self, res):
        input_names = map(lambda x: x[0], self.func.inputs)
        for insn in range(self.n_inputs, self.length - 1):
            for op, op_id in self.op_enum.item_to_cons.items():
                if op.param_constr:
                    for p, v, c in zip(op.param_constr, self.var_insn_opnds(insn), self.var_insn_opnds_is_const(insn)):
                        match p:
                            case '#':
                                res.append(Implies(self.var_insn_op(insn) == op_id, c == True))
                            case str() as s:
                                try:
                                    idx = input_names.index(s)
                                    res.append(Implies(self.var_insn_op(insn) == op_id, v == idx))
                                except:
                                    pass

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
        # Add tree constraints
        self._add_tree_constr(res)
        # Add parameter constraints
        self._add_constr_params(res)
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
            if self.options.opt_cse and not self.options.tree:
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

def _get_length_constr(constr, n_insns):
    len_width = next(iter(constr.values())).length_var.sort().size()
    w = len(constr) * len_width
    return sum(ZeroExt(w - len_width, s.length_var) for s in constr.values()) == BitVecVal(n_insns, w)

@dataclass
class _Session:
    options: Any
    problem: Problem
    solver: Solver
    max_len: int

    def create_constr(self, name: str, f: SynthFunc, n_insns: int):
        use_nop = len(self.problem.funcs) > 1
        return LenConstraints(self.options, name, f, n_insns, use_nop=use_nop)

    def create_all_constr(self, n_insns):
        return { name: self.create_constr(name, f, n_insns) \
                 for name, f in self.problem.funcs.items() }


    def synth_prgs(self, n_insns: int, add_constraints):
        solver = self.solver.create(self.problem.theory)
        constr = self.create_all_constr(n_insns)
        for c in constr.values():
            c.add_program_constraints(solver)
        for c in add_constraints(constr, n_insns):
            solver.add(c)
        # in principle, here should be a constraint that limits the
        # sum of all lengths to n_insns in case we synthesize multiple
        # functions. However, that is slow so we might synthesize
        # non-length-optimal programs first and we could optimize
        # them individually later.
        return self.synth(solver, constr)

@dataclass
class _NopSession(_Session):
    def __post_init__(self):
        self.solver = self.solver.create(self.problem.theory)
        self.constr = self.create_all_constr(self.max_len)
        for c in self.constr.values():
            c.add_program_constraints(self.solver)

    def create_constr(self, name: str, f: SynthFunc, n_insns: int):
        return LenConstraints(self, name, f, n_insns, use_nop=True)

    def synth_prgs(self, n_insns: int, add_constraints=[]):
        self.solver.push()
        self.solver.add(_get_length_constr(self.constr, n_insns))
        for c in add_constraints(self.constr, n_insns):
            self.solver.add(c)
        prgs, stats = self.synth(self.solver, self.constr)
        self.solver.pop()
        return prgs, stats

@dataclass
class _LenCegisSession(_Session):
    def __post_init__(self):
        self.samples = self.problem.constraint.counterexample_eval.sample_n(self.options.init_samples)

    def synth(self, solver, constr):
        prgs, stats, new_samples = cegis(solver, self.problem.constraint,
                                         constr, self.samples,
                                         self.options.debug, self.options.verbose)
        if self.options.keep_samples:
            self.samples = new_samples
        return prgs, stats

@dataclass
class _LenCegisNopSession(_LenCegisSession, _NopSession):
    def __post_init__(self):
        _LenCegisSession.__post_init__(self)
        _NopSession.__post_init__(self)

    def create_constr(self, name: str, f: SynthFunc, n_insns: int):
        return LenConstraints(self.options, name, f, n_insns, use_nop=True)

def _no_add_constraints(constr, n_insns):
    return
    yield

@dataclass(frozen=True, kw_only=True)
class _LenBase(util.HasDebug):
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

    exact: bool = False
    """Each operator appears exactly as often as indicated (overrides size_range)."""

    tree: bool = False
    """Force synthesized programs to be a tree."""

    size_range: tuple[int, int] = (0, 10)
    """Range of program sizes to try."""

    verbose: bool = False
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

    def synth_prgs(self, problem: Problem, add_constraints=_no_add_constraints):
        lo, hi = self.get_range(problem)
        session = self.create_session(problem, hi)
        iterations = []
        with util.timer() as elapsed:
            for n_insns in range(lo, hi + 1):
                self.debug('len', f'size {n_insns}')
                prgs, stats = session.synth_prgs(n_insns, add_constraints)
                iterations += [ stats ]
                if not prgs is None:
                    break
        return prgs, { 'time': elapsed(), 'iterations': iterations }


@dataclass(frozen=True, kw_only=True)
class _LenCegisBase(_LenBase):
    """Cegis synthesizer that finds the shortest program."""

    init_samples: int = 1
    """Number of initial samples to use for the synthesis."""

    keep_samples: bool = False
    """Keep samples across different program lengths."""

    def create_session(self, problem: Problem, max_len: int):
        return _LenCegisSession(options=self,
                                problem=problem,
                                solver=self.solver,
                                max_len=max_len)

@dataclass(frozen=True, kw_only=True)
class LenCegis(_LenCegisBase, solvers.HasSolver):
    pass

class _FAConstraints(LenConstraints, AllPrgSynth):
    def __init__(self, options, name, func: SynthFunc, n_insns: int, use_nop: bool):
        self.exist_vars = set()
        LenConstraints.__init__(self, options, name, func, n_insns, use_nop)

    @lru_cache
    def get_var(self, ty, name, instance=None):
        res = super().get_var(ty, name, instance)
        if not instance is None:
            self.exist_vars.add(res)
        return res

@dataclass
class _FASession(_Session):
    def create_constr(self, name, f, n_insns):
        return _FAConstraints(self.options, name, f, n_insns, use_nop=False)

    def synth(self, solver, constr):
        exist_vars = set()
        constraints = []
        synth_constr = self.problem.constraint
        synth_constr.add_instance_constraints('fa', constr, synth_constr.params,
                                              constraints)
        for name, applications in synth_constr.function_applications.items():
            s = constr[name]
            exist_vars.update(s.exist_vars)
            for _, args in applications:
                exist_vars.difference_update(args)
        solver.add(ForAll(synth_constr.params, Exists(list(exist_vars), And(constraints))))

        d = self.options.debug
        stat = {}
        if self.options.verbose:
            stat['synth_constraint'] = str(s)
        with util.timer() as elapsed:
            res = solver.check()
            synth_time = elapsed()
            d('time', f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = solver.model()
            prgs = { name: c.create_prg(m) for name, c in constr.items() }
            stat['success'] = True
            if self.options.verbose:
                stat['synth_model'] = str(m)
                stat['prgs'] = str(prgs)
            return prgs, stat
        else:
            return None, stat | { 'success': False }

@dataclass
class _FANopSession(_FASession, _NopSession):
    def __post_init__(self):
        return _NopSession.__post_init__(self)

    def create_constr(self, name: str, f: SynthFunc, n_insns: int):
        return _FAConstraints(self.options, name, f, n_insns, use_nop=True)

@dataclass(frozen=True)
class LenFA(_LenBase, solvers.HasSolver):
    """Synthesizer that uses a forall constraint and finds the shortest program."""

    def create_session(self, problem: Problem, max_len: int):
        cls = _FANopSession if len(problem.funcs) > 1 else _FASession
        return cls(options=self,
                   solver=self.solver,
                   problem=problem,
                   max_len=max_len)

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
                 d: util.Debug = util.no_debug, verbose: bool = False):
        synths = { name: _ConstantSynth(func, base_prgs[name]) for name, func in problem.funcs.items() }
        prgs, stats, _ = cegis(solver, problem.constraint, synths, initial_samples=[],
                               d=d, verbose=verbose)
        return prgs, stats

class FAConstantSolver:
    def __call__(self, solver: Solver, problem: Problem, base_prgs: dict[str, Prg],
                 d: util.Debug = util.no_debug, verbose: bool = False):
        constr = problem.constraint
        synths = { name: _ConstantSynth(func, base_prgs[name]) for name, func in problem.funcs.items() }
        constraints = []
        constr.add_instance_constraints('fa', synths, constr.params, constraints)
        solver.add(ForAll(constr.params, And(constraints)))
        stat = {}
        if self.options.verbose:
            stat['synth_constraint'] = str(solver)
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
            if self.options.verbose:
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
                    prgs, stats = self.constant_synth(solver, problem, prgs, d=self.synth.debug, verbose=self.synth.verbose)

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