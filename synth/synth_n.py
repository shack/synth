from functools import cache
from collections import defaultdict
from dataclasses import dataclass, field

from z3 import *

from synth.cegis import cegis
from synth.spec import Func, Prg, Problem, SynthFunc, Production
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

        self.non_terms = self.func.nonterminals
        self.prods     = { p: nt for nt in self.non_terms.values() for p in nt.productions }
        self.types     = set(nt.sort for nt in self.non_terms.values())

        if use_nop or not self.prods:
            # if we want to use a nop instruction or if there's an empty set of operators ...
            assert func.result_nonterminals, 'function must have at least one output non-terminal'
            fst_result_name = func.result_nonterminals[0]
            fst_result_nt   = self.non_terms[fst_result_name]
            func     = Func('$nop', Const('$nop_y', fst_result_nt.sort), inputs=())
            self.nop = Production(
                op=func,
                operands=(),
                operand_is_nt=(),
                sexpr=(),
                attributes={})
            self.prods[self.nop] = fst_result_nt
        else:
            self.nop = None

        assert len(self.prods) > 0, 'no operators to synthesize with'

        self.in_tys     = self.func.in_types
        self.out_nts    = self.func.result_nonterminals
        self.out_tys    = [ self.non_terms[nt].sort for nt in self.out_nts ]
        self.inputs     = [ name for name, _ in self.func.inputs ]
        self.n_inputs   = len(self.in_tys)
        self.n_outputs  = len(self.out_nts)
        self.out_insn   = self.n_inputs + self.n_insns # index of the out instruction
        self.length     = self.out_insn + 1
        self.max_arity  = max(prod.op.arity for prod in self.prods)
        self.arities    = [ 0 ] * self.n_inputs \
                        + [ self.max_arity ] * self.n_insns \
                        + [ self.n_outputs ]
        self.arity_bits = util.bv_width(self.max_arity)

        # prepare operator enum sort
        self.pr_enum = BitVecEnum('Productions', self.prods)
        # create map of types to their id
        self.nt_enum = BitVecEnum('Nonterminals', self.non_terms.keys())

        # get the sorts for the variables used in synthesis
        self.nt_sort = self.nt_enum.sort
        self.pr_sort = self.pr_enum.sort
        self.ln_sort = util.bv_sort(self.length)
        self.bl_sort = BoolSort()

        self.n_insn_var = self.get_var(self.ln_sort, 'n_insns')
        self.length_var = self.get_var(self.ln_sort, 'length_var')

        # set options
        self.d = options.debug

    def constr_is_nop(self, insn):
        return self.var_insn_prod(insn) == self.pr_enum.item_to_cons[self.nop] \
            if self.nop else BoolVal(False)

    @cache
    def get_var(self, ty, name, instance=None):
        name = f'|{self.name}_{name}' + (f'_{instance}|' if instance is not None else '|')
        # name = f'|{prefix}_{instance}|' if not instance is None else f'|{prefix}|'
        return Const(name, ty)

    def var_insn_prod(self, insn):
        return self.get_var(self.pr_sort, f'insn_{insn}_prod')

    def var_insn_arity(self, insn):
        return self.get_var(util.bv_sort(self.max_arity), f'insn_{insn}_arity')

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

    def var_insn_opnds_nt(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.get_var(self.nt_sort, f'insn_{insn}_opnd_nt_{opnd}')

    def var_insn_res_nt(self, insn):
        return self.get_var(self.nt_sort, f'insn_{insn}_res_nt')

    def var_insn_res(self, insn, ty, instance):
        return self.get_var(ty, f'insn_{insn}_res_{ty}', instance)

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

    # def _add_constr_insn_count(self, res):
    #     # constrain the number of usages of an operator if specified
    #     for op, op_cons in self.op_enum.item_to_cons.items():
    #         if not (f := self.ops[op]) is None:
    #             a = [ self.var_insn_op(insn) == op_cons \
    #                 for insn in range(self.n_inputs, self.length - 1) ]
    #             if a:
    #                 res.append(AtMost(*a, f))
    #                 if self.options.exact:
    #                     res.append(AtLeast(*a, f))
    #     return res

    def _add_constr_const_count(self, res):
        for insn in range(self.n_inputs, self.length):
            for nt, nt_id in self.nt_enum.item_to_cons.items():
                nt = self.non_terms[nt]
                cvs = list(self.var_insn_op_opnds_const_val(insn, [nt.sort] * self.max_arity))
                for i, (opnd_nt, ic) in enumerate(zip(self.var_insn_opnds_nt(insn),
                                                      self.var_insn_opnds_is_const(insn))):
                    if nt.constants is None:
                        # if constants are unbounded, no constraint
                        pass
                    elif len(nt.constants) == 0:
                        # if there are no constants, set the const variable to false
                        res.append(Implies(opnd_nt == nt_id, Not(ic)))
                    else:
                        # otherwise, restrict the constant value to the allowed set
                        assert len(nt.constants) > 0
                        res.append(Implies(opnd_nt == nt_id, Implies(ic, nt.const_val_constraint(cvs[i]))))
        return res

    # def _add_constr_const_count(self, res):
    #     const_map = self.func.const_map
    #     max_const = self.func.max_const

    #     # If supplied with an empty set of constants, we don't allow any constants
    #     if not const_map is None and len(const_map) == 0:
    #         max_const = 0

    #     # Add a constraint for the maximum amount of constants if specified.
    #     ran = range(self.n_inputs, self.length)
    #     if not max_const is None and len(ran) > 0:
    #         res.append(AtMost(*[ v for insn in ran \
    #                    for v in self.var_insn_opnds_is_const(insn)], max_const))

    #     # limit the possible set of constants if desired
    #     if const_map:
    #         ty_const_map = defaultdict(list)
    #         const_constr_map = defaultdict(list)
    #         # create a map from types to constants of that type
    #         # each pair in the list is the constant value and its allowed count (or None)
    #         for c, n in const_map.items():
    #             ty_const_map[c.sort()].append((c, n))

    #         # create a map from types to functions that create constraints that
    #         # ensure that a value of that type is one of the allowed constants
    #         ty_const_constr = {}
    #         for ty, consts in ty_const_map.items():
    #             if not consts:
    #                 f = lambda _: BoolVal(True)
    #             else:
    #                 all_unbounded = all(n is None for _, n in consts)
    #                 f = None
    #                 if ty == IntSort() and all_unbounded:
    #                     # for integer constants, we can create range constraints
    #                     # if all constants are unbounded and form a contiguous range
    #                     vals = set(v.as_long() for v, _ in consts)
    #                     l, u = min(vals), max(vals)
    #                     if all(i in vals for i in range(l, u + 1)):
    #                         f = lambda cv: And(IntVal(l) <= cv, cv <= IntVal(u))
    #                 if not f:
    #                     f = lambda cv: Or([ cv == v for v, _ in consts ])
    #             ty_const_constr[ty] = f

    #         for insn in range(self.n_inputs, self.length):
    #             for ty in ty_const_constr:
    #                 for _, _, c, cv in self.iter_opnd_info_struct(insn, [ ty ] * self.max_arity):
    #                     for v, _ in ty_const_map[ty]:
    #                         const_constr_map[v] += [ And([c, cv == v ]) ]
    #                     res.append(Implies(c, ty_const_constr[ty](cv)))
    #         for c, constr in const_constr_map.items():
    #             if (n := const_map[c]) is not None:
    #                 res.append(AtMost(*constr, n))
    #                 if self.options.exact:
    #                     res.append(AtLeast(*constr, n))
    #     return res

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
            if self.out_insn > 0:
                for out in self.var_insn_opnds(self.out_insn):
                    res.append(ULT(out, self.n_insn_var))
        else:
            res.append(self.n_insn_var == self.out_insn)
        res.append(self.n_insn_var - self.n_inputs == self.length_var)
        return res

    def _add_tree_constr(self, res):
        if self.options.tree:
            for insn in range(self.n_inputs, self.length - 1):
                for prod, prod_id in self.pr_enum.item_to_cons.items():
                    res.append(Implies(self.var_insn_prod(insn) == prod_id,
                                       self.var_arity(insn) == prod.op.arity))
                for i, opnd in enumerate(self.var_insn_opnds(insn)):
                    user = (insn << self.arity_bits) | i
                    for prod in range(self.n_inputs, insn):
                        res.append(Implies(ULT(i, self.var_arity(insn)),
                                           Implies(opnd == prod,
                                                   self.var_tree_use(prod) == user)))
        return res

    def _add_constr_wfp(self, res):
        if self.n_inputs == 0:
            # if there are no inputs
            # all operands of the first instruction must be constant
            # and the operand indexes cannot be constrained because there
            # is no proper operand except a constant.
            first_real_insn = 1
            for ic in self.var_insn_opnds_is_const(0):
                res.append(ic)
        else:
            first_real_insn = self.n_inputs
        # acyclic: line numbers of uses are lower than line number of definition
        # i.e.: we can only use results of preceding instructions
        for insn in range(first_real_insn, self.length):
            for v in self.var_insn_opnds(insn):
                res.append(ULT(v, insn))
        # Add bounds for the operand ids
        for insn in range(first_real_insn, self.length - 1):
            self.pr_enum.add_range_constr(self.var_insn_prod(insn), res)
        # Add a constraint that pins potentially unused operands to the last
        # one. This is important because otherwise the no_dead_code constraints
        # will not work.
        for insn in range(first_real_insn, self.length - 1):
            for prod, prod_id in self.pr_enum.item_to_cons.items():
                res.append(Implies(self.var_insn_prod(insn) == prod_id, self.var_insn_arity(insn) == prod.op.arity))
                if prod.op.arity < self.max_arity:
                    opnds = list(self.var_insn_opnds(insn))
                    res.append(Implies(self.var_insn_prod(insn) == prod_id, \
                               And([ opnds[prod.op.arity - 1] == x for x in opnds[prod.op.arity:] ])))
        # Add constraints on the instruction counts
        # self._add_constr_insn_count(res)
        # Add constraints on constant usage
        self._add_constr_const_count(res)
        # Add constraints for nop instructions
        self._add_nop_length_constr(res)
        # Add tree constraints
        self._add_tree_constr(res)
        return res

    def _add_constr_ty(self, res):
        # for all instructions that get an op
        # add constraints that set the type of an instruction's operand
        # and the result type of an instruction
        non_term_vars = self.nt_enum.item_to_cons
        for insn in range(self.n_inputs, self.length - 1):
            for prod, prod_id in self.pr_enum.item_to_cons.items():
                # add constraints that set the result type of each instruction
                res_nt = self.prods[prod]
                res.append(Implies(self.var_insn_prod(insn) == prod_id, \
                           self.var_insn_res_nt(insn) == non_term_vars[res_nt.name]))
                # add constraints that set the type of each operand
                for op_nt, v, o, ic in zip(prod.operands,
                                           self.var_insn_opnds_nt(insn),
                                           self.var_insn_opnds(insn),
                                           self.var_insn_opnds_is_const(insn)):
                    if op_nt in non_term_vars:
                        # if the operand of the production is a non-terminal, set its type
                        res.append(Implies(self.var_insn_prod(insn) == prod_id,
                                           v == non_term_vars[op_nt]))
                    else:
                        # else the operand refers to a specific parameter of the function
                        # then, we pin the operand of the instruction to that parameter
                        assert op_nt in self.inputs, f'unknown operand {op_nt}'
                        idx = self.inputs.index(op_nt)
                        assert 0 <= idx < self.n_inputs, f'operand {op_nt} index out of range'
                        res.append(Implies(self.var_insn_prod(insn) == prod_id,
                                           And(o == idx, ic == False)))

        # constrain sorts of inputs
        # note that a parameter (input) can appear in multiple non-terminals
        # so we need to create a disjunction of possible non-terminals.
        # first create a map from inputs to non-terminals in which they are used
        input_nt_map = defaultdict(list)
        for nt in self.non_terms.values():
            for p in nt.parameters:
                input_nt_map[p].append(nt)

        for insn, name in enumerate(self.inputs):
            # it could be that the input does not appear in any non-terminal
            # therefore, we always allow the input to have the type of a
            # dummy, non-existent non-terminal
            v = self.var_insn_res_nt(insn)
            if (nts := input_nt_map[name]):
                res.append(Or([v == non_term_vars[nt.name] for nt in nts]))
            else:
                res.append(v == len(non_term_vars))

        # define types of outputs
        for v, nt in zip(self.var_insn_opnds_nt(self.out_insn), self.out_nts):
            res.append(v == non_term_vars[nt])

        # constrain types of outputs
        for insn in range(self.n_inputs, self.length):
            for other in range(0, insn):
                for opnd, c, nt in zip(self.var_insn_opnds(insn), \
                                       self.var_insn_opnds_is_const(insn), \
                                       self.var_insn_opnds_nt(insn)):
                    res.append(Implies(Not(c), Implies(opnd == other, \
                               nt == self.var_insn_res_nt(other))))
            self.nt_enum.add_range_constr(self.var_insn_res_nt(insn), res)
        return res

    def _add_constr_opt(self, res):

        if self.options.opt_insn_order:
            opnd_set = {}
            n_pr = self.pr_sort.size()
            sz   = self.length + n_pr
            ext  = sz - self.ln_sort.size()
            assert ext >= 0
            r = BitVecVal(0, sz)
            o = BitVecVal(1, sz)
            for insn in range(self.n_inputs, self.out_insn):
                for opnd, ic in zip(self.var_insn_opnds(insn),
                                    self.var_insn_opnds_is_const(insn)):
                    r |= If(ic, 0, (o << ZeroExt(ext, opnd)))
                r = (r << BitVecVal(n_pr, sz)) \
                    | ZeroExt(sz - n_pr, self.var_insn_prod(insn))
                v = BitVec(f'opnd_set_{insn}', r.sort().size())
                opnd_set[insn] = v
                res.append(v == r)
            for insn in range(self.n_inputs, self.out_insn - 2):
                res.append(ULE(opnd_set[insn], opnd_set[insn + 1]))

        for insn in range(self.n_inputs, self.out_insn):
            prod_var = self.var_insn_prod(insn)
            opnds = list(self.var_insn_opnds(insn))

            for prod, prod_id in self.pr_enum.item_to_cons.items():
                op = prod.op
                is_cnst = list(v for v in self.var_insn_opnds_is_const(insn))[:op.arity]
                # if operator is commutative, force the operands to be in ascending order
                if self.options.opt_commutative and op.is_commutative:
                    c = [ ULE(l, u) for l, u in zip(opnds[:op.arity - 1], opnds[1:]) ]
                    res.append(Implies(prod_var == prod_id, And(c)))

                if len(set(prod.operands)) == 1 \
                    and prod.operands[0] not in self.inputs \
                    and (self.non_terms[prod.operands[0]].constants is None or self.options.opt_const_relaxed) \
                    and self.options.opt_const \
                    and len(is_cnst) > 0:
                    # this optimisation only works if all operands have the same type
                    # and the set of allowed constants of the non-terminal is unbounded
                    if op.arity == 2 and op.is_commutative:
                        # Binary commutative operators have at most one constant operand
                        # Hence, we pin the first operand to me non-constant
                        not_const = is_cnst[0]
                    else:
                        # Otherwise, we require that at least one operand is non-constant
                        not_const = And(is_cnst)
                    res.append(Implies(prod_var == prod_id, Not(not_const)))

            # Computations must not be replicated: If an operation appears again
            # in the program, at least one of the operands must be different from
            # a previous occurrence of the same operation.
            if self.options.opt_cse and not self.options.tree:
                for other in range(self.n_inputs, insn):
                    un_eq = [ p != q for p, q in zip(self.var_insn_opnds(insn), \
                                                     self.var_insn_opnds(other)) ]
                    if len(un_eq) > 0:
                        res.append(Implies(prod_var == self.var_insn_prod(other), Or(un_eq)))

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
            prod_var = self.var_insn_prod(insn)
            for prod, prod_id in self.pr_enum.item_to_cons.items():
                res_var = self.var_insn_res(insn, prod.op.out_type, instance)
                opnds = list(self.var_insn_opnds_val(insn, prod.op.in_types, instance))
                precond, phi = prod.op.instantiate([ res_var ], opnds)
                res.append(Implies(prod_var == prod_id, And([ precond, phi ])))
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
                    res = model.evaluate(cv, model_completion=True)
                    assert res is not None
                    yield (True, res)
                else:
                    assert model[opnd] is not None, str(opnd) + str(model)
                    yield (False, model[opnd].as_long())
        insns = []
        for insn in range(self.n_inputs, self.length - 1):
            val    = model.evaluate(self.var_insn_prod(insn), model_completion=True)
            prod   = self.pr_enum.get_from_model_val(val)
            opnds  = [ v for v in prep_opnds(insn, prod.op.in_types) ]
            insns += [ (prod.op, opnds) ]
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
        self.samples = self.problem.constraints[0].counterexample_eval.sample_n(self.options.init_samples)

    def synth(self, solver, constr):
        prgs, stats, new_samples = cegis(solver, self.problem.constraints, constr,
                                         self.samples,
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
    """Prevent all-const instructions (only has an effect if constants are unrestricted)."""

    opt_const_relaxed: bool = False
    """Prevent all-const instructions even for restricted constants (requires opt_const set to True)."""

    opt_commutative: bool = True
    """Force order of operands of commutative operators."""

    opt_insn_order: bool = True
    """Order of instructions is determined by operands."""

    exact: bool = False
    """Each operator appears exactly as often as indicated (overrides size_range)."""

    tree: bool = False
    """Force synthesized programs to be a tree."""

    size_range: tuple[int, int] = (0, 20)
    """Range of program sizes to try."""

    verbose: bool = False
    """Record detailed statistics during synthesis."""

    def get_range(self, problem: Problem):
        if self.exact:
            assert len(problem.funcs) == 1, 'exact size only supported for single function synthesis'
            fun = next(iter(problem.funcs.values()))
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
                self.debug('len', f'(size {n_insns})')
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

    @cache
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
        synth_constr = And(self.problem.constraints)
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
