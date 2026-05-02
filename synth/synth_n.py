from enum import Enum, auto
from functools import cache, reduce
from collections import defaultdict
from dataclasses import dataclass, field

import itertools

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

    def __iter__(self):
        return iter(self.item_to_cons.keys())

    def add_cases(self, res, var, f, *args):
        for item, val in self.item_to_cons.items():
            for c in f(item, *args):
                res.append(Implies(var == val, c))
        return res

    def add_cases_dict(self, res, var, d):
        assert all(k in self.item_to_cons for k in d)
        return self.add_cases(res, var, lambda item: d[item])

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
    def __init__(self, options: '_LenBase', name: str, func: SynthFunc, n_insns: int, use_nop: bool = False):
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

        # import pprint
        # pprint.pprint(func)

        self.non_terms    = self.func.nonterminals
        self.non_term_idx = { nt_name: i for i, nt_name in enumerate(self.non_terms) }
        self.types        = set(nt.sort for nt in self.non_terms.values())
        self.param_idx    = { name: i for i, (name, _) in enumerate(self.func.inputs) }

        self.prods = defaultdict(list)
        for nt_name, nt in self.non_terms.items():
            for p in nt.productions:
                self.prods[p].append(nt_name)

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
                sexpr='',
                attributes={})
            self.prods[self.nop] = [ fst_result_nt ]
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
        self.max_arity  = max(prod.nonterminal_arity() for prod in self.prods)
        self.arities    = [ 0 ] * self.n_inputs \
                        + [ self.max_arity ] * self.n_insns \
                        + [ self.n_outputs ]
        self.arity_bits = util.bv_width(self.max_arity)

        # prepare operator enum sort
        self.pr_enum = BitVecEnum('Productions', self.prods)

        # get the sorts for the variables used in synthesis
        self.nt_sort = BitVecSort(len(self.non_terms))
        self.pr_sort = self.pr_enum.sort
        self.ln_sort = util.bv_sort(self.length)
        self.bl_sort = BoolSort()

        self.n_insn_var = self.get_var(self.ln_sort, 'n_insns')
        self.length_var = self.get_var(self.ln_sort, 'length_var')

        # set options
        self.d = options.debug

    def nt_mask(self, *nt_names):
        val = reduce(lambda a, x: a | (1 << self.non_term_idx[x]), nt_names, 0)
        return BitVecVal(val, self.nt_sort.size())

    def nt_mask_for_prod(self, prod):
        return self.nt_mask(*self.prods[prod])

    def constr_is_nop(self, insn):
        return self.var_insn_prod(insn) == self.pr_enum.item_to_cons[self.nop] \
            if self.nop else BoolVal(False)

    @cache
    def get_var(self, ty, name, instance=None):
        name = f'|{self.name}_{name}' + (f'_{instance}|' if instance is not None else '|')
        return Const(name, ty)

    def var_insn_prod(self, insn):
        return self.get_var(self.pr_sort, f'insn_{insn}_prod')

    def var_insn_arity(self, insn):
        return self.get_var(util.bv_sort(self.max_arity), f'insn_{insn}_arity')

    def var_insn_opnd_is_const(self, insn, idx):
        return self.get_var(self.bl_sort, f'insn_{insn}_opnd_{idx}_is_const')

    def var_insn_opnds_is_const(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.var_insn_opnd_is_const(insn, opnd)

    def var_insn_opnd_const_val(self, insn, idx, ty):
        return self.get_var(ty, f'insn_{insn}_opnd_{idx}_{ty}_const_val')

    def var_insn_opnds_const_val(self, insn, opnd_tys):
        for opnd, ty in enumerate(opnd_tys):
            yield self.var_insn_opnd_const_val(insn, opnd, ty)

    def var_insn_opnds_const_val_prod(self, insn, prod: Production):
        for opnd, (idx, nt) in enumerate(prod.nonterminal_operands()):
            yield (idx, self.get_var(nt.sort, f'insn_{insn}_opnd_{opnd}_{nt.sort}_const_val'))

    def var_insn_opnd(self, insn, idx):
        return self.get_var(self.ln_sort, f'insn_{insn}_opnd_{idx}')

    def var_insn_opnds(self, insn):
        for opnd in range(self.arities[insn]):
            yield self.var_insn_opnd(insn, opnd)

    def var_insn_opnd_val(self, insn, idx, ty, instance):
        return self.get_var(ty, f'insn_{insn}_opnd_{idx}_{ty}', instance)

    def var_insn_opnds_val(self, insn, tys: Sequence[SortRef], instance):
        for opnd, ty in enumerate(tys):
            yield self.var_insn_opnd_val(insn, opnd, ty, instance)

    def var_insn_opnds_val_prod(self, insn, prod: Production, instance):
        tys = [ self.non_terms[nt].sort for (_, nt) in prod.nonterminal_operands() ]
        return self.var_insn_opnds_val(insn, tys, instance)

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

    def var_insn_weights(self, insn):
        for name, (default, _) in self.func.weights.items():
            yield (name, default, self.get_var(IntSort(), f'weights_{name}_{insn}'))

    def is_op_insn(self, insn):
        return insn >= self.n_inputs and insn < self.length - 1

    def iter_insns_in_out(self):
        return range(0, self.length)

    def iter_insns_in(self):
        return range(0, self.out_insn)

    def iter_insns_out(self):
        return range(self.n_inputs, self.length)

    def iter_insns(self):
        return range(self.n_inputs, self.out_insn)

    def _add_constr_insn_count(self, res):
        # constrain the number of usages of a production if specified
        for prod, prod_cons in self.pr_enum.item_to_cons.items():
            if (f := prod.attributes.get('max')) is not None:
                a = [ self.var_insn_prod(insn) == prod_cons \
                      for insn in self.iter_insns() ]
                if a:
                    res.append(AtMost(*a, int(f)))
                    if self.options.exact:
                        res.append(AtLeast(*a, int(f)))
        return res

    def _add_constr_const_count(self, res):
        max_const = self.func.max_const
        ran = range(self.n_inputs, self.length)
        if not max_const is None and len(ran) > 0:
            res.append(AtMost(*[ v for insn in ran \
                       for i, v in enumerate(self.var_insn_opnds_is_const(insn))], max_const))

        for insn in range(self.n_inputs, self.length):
            for nt in self.non_terms.values():
                for i, (opnd_nt, ic) in enumerate(zip(self.var_insn_opnds_nt(insn),
                                                      self.var_insn_opnds_is_const(insn))):
                    premise = opnd_nt == self.nt_mask(nt.name) if len(self.non_terms) > 1 else BoolVal(True)
                    if nt.constants is None:
                        # if constants are unbounded, no constraint
                        pass
                    elif len(nt.constants) == 0:
                        # if there are no constants, set the const variable to false
                        res.append(Implies(premise, Not(ic)))
                    else:
                        # otherwise, restrict the constant value to the allowed set
                        assert len(nt.constants) > 0
                        cv = self.var_insn_opnd_const_val(insn, i, nt.sort)
                        res.append(Implies(premise, nt.const_val_constraint(cv)))
        return res

    def _add_nop_length_constr(self, res):
        if self.nop:
            # make sure that nop instructions are at the end of the program
            res.append(ULE(self.n_inputs, self.n_insn_var))
            res.append(ULE(self.n_insn_var, self.out_insn))
            for insn in range(self.n_inputs, self.out_insn):
                # set the n_insn_var variable to the end of the program
                res.append(If(self.constr_is_nop(insn),
                           ULE(self.n_insn_var, insn),
                           ULT(insn, self.n_insn_var)))
            # and that the output instruction cannot use nop outputs
            if self.out_insn > 0:
                for out, ic in zip(self.var_insn_opnds(self.out_insn),
                                   self.var_insn_opnds_is_const(self.out_insn)):
                    res.append(If(self.n_insn_var == 0, ic, ULT(out, self.n_insn_var)))
        else:
            res.append(self.n_insn_var == self.out_insn)
        res.append(simplify(self.n_insn_var - self.n_inputs) == self.length_var)
        return res

    def _add_tree_constr(self, res):
        if self.options.tree:
            for insn in self.iter_insns():
                for i, opnd in enumerate(self.var_insn_opnds(insn)):
                    user = (insn << self.arity_bits) | i
                    for prod in range(self.n_inputs, insn):
                        res.append(Implies(ULT(i, self.var_insn_arity(insn)),
                                           Implies(opnd == prod,
                                                   self.var_tree_use(prod) == user)))
        return res

    def _add_constr_weights(self, res):
        total = { name: IntVal(0) for name, _ in self.func.weights.items() }
        for insn in self.iter_insns():
            for name, default, var in self.var_insn_weights(insn):
                curr = IntVal(int(default))
                for prod, prod_id in self.pr_enum.item_to_cons.items():
                    if (val := prod.attributes.get(name, default)) != default:
                        curr = If(self.var_insn_prod(insn) == prod_id, val, curr)
                total[name] += curr
        for name, (_, var) in self.func.weights.items():
            res.append(var == total[name])

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
        # Add bounds for the production ids
        for insn in self.iter_insns():
            self.pr_enum.add_range_constr(self.var_insn_prod(insn), res)

        self._add_constr_insn_count(res)
        # Add constraints on constant usage
        self._add_constr_const_count(res)
        # Add constraints for nop instructions
        self._add_nop_length_constr(res)
        # Add tree constraints
        self._add_tree_constr(res)
        self._add_constr_weights(res)
        return res

    def _add_constr_wfp_per_insn_prod(self, res, insn, prod: Production):
        arity = prod.nonterminal_arity()
        if self.options.tree:
            # For tree synthesis we need the arity variables being set
            res.append(self.var_insn_arity(insn) == arity)
        if arity < self.max_arity:
            # if the operator's arity is smaller than the maximum arity
            # there are some operands that don't play a role for that operator.
            # We force these operands to the first parameter.
            # Note that if there are no parameters that is still ok:
            # see the beginning of _add_constr_wfp()
            opnds = list(self.var_insn_opnds(insn))
            res.append(And(opnd == 0 for opnd in itertools.islice(opnds, arity, None)))
            pass

    def _add_constr_ty_per_insn_prod(self, res, insn: int, prod: Production):
        if prod is not self.nop and len(self.non_terms) > 1:
            # add constraints that set the result type of each instruction
            res.append(self.var_insn_res_nt(insn) == self.nt_mask_for_prod(prod))
            # add constraints that set the type of each operand
            for (_, name), ic, v in zip(prod.nonterminal_operands(),
                                        self.var_insn_opnds_is_const(insn),
                                        self.var_insn_opnds_nt(insn)):
                res.append(v == self.nt_mask(name))
        return res

    def _add_constr_ty(self, res):
        if len(self.non_terms) <= 1:
            return res
        # set nt masks of parameters
        non_terms_per_param = defaultdict(list)
        for nt_name, nt in self.non_terms.items():
            for param in nt.parameters:
                non_terms_per_param[param].append(nt_name)
        for insn, param in enumerate(self.inputs):
            res.add(self.var_insn_res_nt(insn) == self.nt_mask(*non_terms_per_param[param]))

        # define types of outputs
        for v, nt_name in zip(self.var_insn_opnds_nt(self.out_insn), self.out_nts):
            res.append(v == self.nt_mask(nt_name))

        # constrain non-terminals of operands and results
        for insn in self.iter_insns_out():
            # make sure that the result non-terminal variables are in a given range
            for i, (opnd, c, opnd_nt) in enumerate(zip(self.var_insn_opnds(insn),
                                                       self.var_insn_opnds_is_const(insn),
                                                       self.var_insn_opnds_nt(insn))):
                # make sure that the non-terminals of the results of instructions
                # referenced by operands match the required operand non-terminal.
                # note that input instructions do not have result non-terminals
                # because they can appear in the context of more than one non-terminal.
                # for other in range(self.n_inputs, insn):
                for other in range(insn):
                    res.append(Implies(Not(c),
                               Implies(opnd == other,
                                       (opnd_nt & self.var_insn_res_nt(other)) == opnd_nt)))

        return res

    def _add_constr_opt(self, res):
        pr_bits = self.pr_sort.size()
        opt = self.options.opt

        if (Opt.ORD in opt or Opt.DCE in opt) and self.n_insns > 0:
            # compute fingerprints for order and dead_code constraints
            assert self.length >= self.ln_sort.size()
            fingerprints = []
            z = BitVecVal(0, self.length)
            o = BitVecVal(1, z.sort().size())
            n = BitVecVal(1 << (z.sort().size() - 1), z.sort().size())
            srt = BitVecSort(z.sort().size() + pr_bits)
            for insn in range(self.n_inputs, self.length):
                var = self.get_var(srt, f'fingerprint_{insn}')
                opnd_bv = z
                for c, v in zip(self.var_insn_opnds_is_const(insn),
                                self.var_insn_opnds(insn)):
                    opnd_bv |= If(c, z, o) << ZeroExt(o.sort().size() - v.sort().size(), v)
                # if this is an instruction beyond "the end" (either a nop or the out insn)
                # we make its fingerprint compliant by setting the MSB
                if self.nop:
                    opnd_bv |= If(ULE(self.n_insn_var, insn), n, z)
                res.append(var == Concat(opnd_bv, self.var_insn_prod(insn)))
                fingerprints.append(var)

            if Opt.ORD in opt:
                for a, b in itertools.pairwise(fingerprints):
                    res.append(ULE(a, b))

            # no dead code: each produced value is used
            if Opt.DCE in opt and self.n_insns > 0:
                l = pr_bits + self.n_inputs
                h = l + self.n_insns - 1
                z = BitVecVal(0, self.n_insns)
                curr = reduce(lambda a, x: a | Extract(h, l, x), fingerprints, z)
                if self.nop:
                    # when we have nops, we need to compute a bit mask of
                    # all ones based on the current length of the program.
                    # this bit mask has ones for all variables that are
                    # defined and therefore need to be used
                    ls = self.length_var.sort().size()
                    if self.n_insns < ls:
                        l = Extract(self.n_insns - 1, 0, self.length_var)
                    elif self.n_insns > ls:
                        l = ZeroExt(self.n_insns - ls, self.length_var)
                    else:
                        l = self.length_var
                    m = (BitVecVal(1, self.n_insns) << l) - 1
                    res.append((curr & m) == m)
                else:
                    # if don't have nops, this bit mask is just all ones.
                    res.append(curr == BitVecVal(-1, curr.sort().size()))

        # Prevent common subexpressions.
        # Computations must not be replicated: If an operation appears again
        # in the program, at least one of the operands must be different from
        # a previous occurrence of the same operation.
        if Opt.CSE in opt and not self.options.tree and self.n_insns > 1:
            # compute instruction operand vectors
            for insn in self.iter_insns():
                for other in range(insn + 1, self.out_insn):
                    impl = And(self.var_insn_prod(insn) == self.var_insn_prod(other), Not(self.constr_is_nop(other)))
                    rest = Or(v != w for v, w in zip(self.var_insn_opnds(insn), self.var_insn_opnds(other)))
                    res.append(Implies(impl, rest))
        return res

    def _add_constr_opt_per_insn_prod(self, res, insn, prod: Production):
        arity = prod.nonterminal_arity()
        # commutative constraints
        op = prod.op
        is_cnst = list(v for v in self.var_insn_opnds_is_const(insn))[:arity]
        opnds = list(self.var_insn_opnds(insn))
        # if operator is commutative, force the operands to be in ascending order
        if Opt.COM in self.options.opt and op.is_commutative:
            c = [ ULE(l, u) for l, u in itertools.pairwise(opnds[:arity]) ]
            res.append(And(c))

        # constant operands pruning
        if len(set(prod.operands)) == 1 \
            and prod.operands[0] not in self.inputs \
            and arity > 0:
            # we made sure that there is only one non-terminal as operand

            nt = self.non_terms[prod.operands[0]]
            allows_constants = nt.constants is None or len(nt.constants) > 0
            if Opt.CON in self.options.opt and allows_constants:
                # this optimisation only works if all operands have the same type
                # and the set of allowed constants of the non-terminal is unbounded
                if arity == 2 and op.is_commutative:
                    # Binary commutative operators have at most one constant operand
                    # Hence, we pin the first operand to me non-constant
                    res.append(Not(is_cnst[0]))
                else:
                    # Otherwise, we require that at least one operand is non-constant
                    res.append(Not(And(is_cnst)))
        return res

    def _add_constr_conn(self, insn, tys, instance, res):
        for ty, l, v, c, cv in zip(tys,
                self.var_insn_opnds(insn),
                self.var_insn_opnds_val(insn, tys, instance),
                self.var_insn_opnds_is_const(insn),
                self.var_insn_opnds_const_val(insn, tys)):
            # if the operand is a constant, its value is the constant value
            res.append(Implies(c, v == cv))
            # else, for other each instruction preceding it ...
            for other in range(insn):
                r = self.var_insn_res(other, ty, instance)
                # ... the operand is equal to the result of the instruction
                res.append(Implies(Not(c), Implies(l == other, v == r)))
        return res

    def _add_constr_instance_per_insn(self, prod: Production, insn: int, instance):
        opnds = [ None ] * prod.op.arity
        for (i, _), val in zip(prod.nonterminal_operands(),
                               self.var_insn_opnds_val_prod(insn, prod, instance)):
            opnds[i] = val

        for i, param in prod.parameter_operands():
            idx = self.param_idx[param]
            ty = self.func.in_types[idx]
            opnds[i] = self.var_insn_res(idx, ty, instance)

        res_var = self.var_insn_res(insn, prod.op.out_type, instance)
        yield And(*prod.op.instantiate([ res_var ], opnds))

    def _add_constr_instance(self, instance, res):
        # for all instructions that get an op
        for insn in range(self.n_inputs, self.length - 1):
            # add constraints to select the proper operation
            self.pr_enum.add_cases(res, self.var_insn_prod(insn), self._add_constr_instance_per_insn, insn, instance)
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
        for insn in self.iter_insns():
            constr = defaultdict(list)
            for prod in self.pr_enum:
                c = constr[prod]
                self._add_constr_wfp_per_insn_prod(c, insn, prod)
                self._add_constr_ty_per_insn_prod(c, insn, prod)
                self._add_constr_opt_per_insn_prod(c, insn, prod)
            self.pr_enum.add_cases_dict(res, self.var_insn_prod(insn), constr)
        return res

    def instantiate(self, instance, args, res):
        self._add_constr_instance(instance, res)
        inst_outs, inst_ins = self.vars_out_in(instance)
        for var, val in zip(inst_ins, args):
            res.append(var == val)
        return res, inst_outs

    def create_prg(self, model):
        def get_opnd(insn, i, ty):
            opnd = self.var_insn_opnd(insn, i)
            c    = self.var_insn_opnd_is_const(insn, i)
            cv   = self.var_insn_opnd_const_val(insn, i, ty)
            if model[c] is None or is_true(model[c]):
                # if the operand const-ness is not in the model, it is
                # unconstrained and we can just assume that the operand
                # is constant. If not, we check that it is.
                res = model.evaluate(cv, model_completion=True)
                assert res is not None
                return (True, res)
            else:
                assert model[opnd] is not None, str(opnd) + str(model)
                return (False, model[opnd].as_long())

        def prep_opnds(insn, prod: Production):
            res = [ None ] * prod.op.arity
            for i, (idx, nt_name) in enumerate(prod.nonterminal_operands()):
                res[idx] = get_opnd(insn, i, self.non_terms[nt_name].sort)
            for (idx, param) in prod.parameter_operands():
                res[idx] = (False, self.param_idx[param])
            assert None not in res
            return res
        insns = []
        for insn in range(self.n_inputs, self.length - 1):
            val    = model.evaluate(self.var_insn_prod(insn), model_completion=True)
            prod   = self.pr_enum.get_from_model_val(val)
            opnds  = prep_opnds(insn, prod)
            insns += [ (prod, opnds) ]
        outputs = [ get_opnd(self.out_insn, i, ty) for i, ty in enumerate(self.out_tys) ]
        weights = { var: model.evaluate(var) for _, (_, var) in self.func.weights.items() }
        return Prg(self.func, insns, outputs, weights=weights)

    def prg_constraints(self, prg):
        """Yields constraints that represent a given program."""
        for i, (prod, params) in enumerate(prg.insns):
            insn_nr = self.n_inputs + i
            val = self.pr_enum.get_from_op(prod)
            yield self.var_insn_prod(insn_nr) == val
            tys  = prod.op.in_types
            for (is_const, p), v_is_const, v_opnd, v_const_val \
                in zip(params,
                       self.var_insn_opnds_is_const(insn_nr),
                       self.var_insn_opnds(insn_nr),
                       self.var_insn_opnds_const_val(insn_nr, tys)):
                yield v_is_const == is_const
                if is_const:
                    yield v_const_val == p
                else:
                    yield v_opnd == p

    def exclude_program_constr(self, prg, res):
        res.append(Not(And([ p for p in self.prg_constraints(prg) ])))
        return res

def _get_length_constr(constr, n_insns):
    w = sum(s.length_var.sort().size() for s in constr.values())
    return sum(ZeroExt(w - s.length_var.sort().size(), s.length_var) for s in constr.values()) == BitVecVal(n_insns, w)

@dataclass
class _Session:
    options: Any
    problem: Problem
    solver: Solver
    max_len: int

    def create_constr(self, name: str, f: SynthFunc, n_insns: int) -> LenConstraints:
        use_nop = len(self.problem.funcs) > 1
        return LenConstraints(self.options, name, f, n_insns, use_nop=use_nop)

    def create_all_constr(self, n_insns: int) -> dict[str, LenConstraints]:
        return { name: self.create_constr(name, f, n_insns) \
                 for name, f in self.problem.funcs.items() }

    def synth_all_prgs(self, n_insns: int):
        solver = self.solver.create(self.problem.theory)
        constr = self.create_all_constr(n_insns)
        for c in constr.values():
            c.add_program_constraints(solver)
        if len(self.problem.funcs) > 1:
            solver.add(_get_length_constr(constr, n_insns))
        while True:
            prgs, stats = self.synth(solver, constr)
            if prgs is not None:
                yield prgs, stats
                for s, p in zip(constr.values(), prgs.values()):
                   s.exclude_program_constr(p, solver)
            else:
                break

    def synth_prgs(self, n_insns: int, add_constraints):
        solver = self.solver.create(self.problem.theory)
        constr = self.create_all_constr(n_insns)
        for c in constr.values():
            c.add_program_constraints(solver)
        if len(self.problem.funcs) > 1:
            solver.add(_get_length_constr(constr, n_insns))
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

class Opt(Enum):
    DCE = auto()
    """Disallow dead code."""

    CSE = auto()
    """Disallow common subexpressions."""

    CON = auto()
    """Prevent all-const instructions even for restricted constants (requires opt_const set to True)."""

    COM = auto()
    """Force order of operands of commutative operators."""

    ORD = auto()
    """Order of instructions is determined by operands."""

@dataclass(frozen=True, kw_only=True)
class _LenBase(util.HasDebug):
    opt: set[Opt] = field(default_factory=lambda: set(Opt))
    """Pruning constraints to add."""

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

    def synth_all_prgs(self, problem):
        lo, hi = self.get_range(problem)
        session = self.create_session(problem, hi)
        for n_insns in range(lo, hi + 1):
            self.debug('len', f'(size {n_insns})')
            produced_programs = False
            for prgs, stats in session.synth_all_prgs(n_insns):
                yield prgs, stats
                produced_programs = True
            if produced_programs:
                return

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
