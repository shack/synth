from functools import lru_cache
from collections import defaultdict

from z3 import *

from cegis import Spec, Func, Prg, OpFreq, no_debug, timer, cegis
from synth_n import EnumSortEnum, SynthN
from util import bv_sort


use_cegis = True

def toSMT2Benchmark(f, status="unknown", name="benchmark", logic=""):
  v = (Ast * 0)()
  return Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast())

def transform_constant_to_bitwidth(constant, target_bitwidth):
    # print("Sort is BV", constant.sort(), is_bv_sort(constant.sort()))

    if not is_bv_sort(constant.sort()):
        return constant

    # create new BV constant with target bitwidth
    return BitVec(f"{constant}_transformed", target_bitwidth, constant.ctx)

def transform_to_bitwidth_expr_ref(expr: ExprRef, decl_map, target_bitwidth):
    if len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED:
        # check if it already transformed
        if expr.decl() in decl_map:
            return decl_map[expr.decl()]
        decl_map[expr.decl()] = transform_constant_to_bitwidth(expr, target_bitwidth)
        return decl_map[expr.decl()]

    

    # print("is bv expression", is_bv(expr))

    if expr.decl().arity() == 0:
        if expr.decl().kind() == Z3_OP_BNUM:
            return BitVecVal(expr.as_long(), target_bitwidth)

    # transform operator
    if expr.decl().arity() > 0:
        # transform children 
        children = [ transform_to_bitwidth_expr_ref(c, decl_map, target_bitwidth) for c in expr.children() ]
        # create new operator
        
        
        # recreate operator on different bit width
        # check decl type
        
        if expr.decl().kind() == Z3_OP_BIT1:
            return BitVecVal(1, target_bitwidth)
        elif expr.decl().kind() == Z3_OP_BIT0:
            return BitVecVal(0, target_bitwidth)
        elif expr.decl().kind() == Z3_OP_BNEG:
            return BitVecRef(Z3_mk_bvneg(expr.decl().ctx_ref(), children[0].as_ast()))
        elif expr.decl().kind() == Z3_OP_BADD:
            return BitVecRef(Z3_mk_bvadd(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast())) # children[0] + children[1]
        elif expr.decl().kind() == Z3_OP_BSUB:
            return BitVecRef(Z3_mk_bvsub(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BMUL:
            return BitVecRef(Z3_mk_bvmul(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BSDIV:
            return BitVecRef(Z3_mk_bvsdiv(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BUDIV:
            return BitVecRef(Z3_mk_bvudiv(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BSREM:
            return BitVecRef(Z3_mk_bvsrem(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BUREM:
            return BitVecRef(Z3_mk_bvurem(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BSMOD:
            return BitVecRef(Z3_mk_bvsmod(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BAND:
            return BitVecRef(Z3_mk_bvand(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BOR:
            return BitVecRef(Z3_mk_bvor(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BNOT:
            return BitVecRef(Z3_mk_bvnot(expr.decl().ctx_ref(), children[0].as_ast()))
        elif expr.decl().kind() == Z3_OP_BXOR:
            return BitVecRef(Z3_mk_bvxor(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BNAND:
            return BitVecRef(Z3_mk_bvnand(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BNOR:
            return BitVecRef(Z3_mk_bvnor(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BXNOR:
            return BitVecRef(Z3_mk_bvxnor(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BREDOR:
            return BitVecRef(Z3_mk_bvredor(expr.decl().ctx_ref(), children[0].as_ast()))
        elif expr.decl().kind() == Z3_OP_BREDAND:
            return BitVecRef(Z3_mk_bvredand(expr.decl().ctx_ref(), children[0].as_ast()))
        elif expr.decl().kind() == Z3_OP_BCOMP:
            assert False, "unimplemented"
            # return BitVecRef(Z3_mk_bvcomp(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BSHL:
            return BitVecRef(Z3_mk_bvshl(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BLSHR:
            return BitVecRef(Z3_mk_bvlshr(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_BASHR:
            return BitVecRef(Z3_mk_bvashr(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_ZERO_EXT:
            # todo: maybe incorrect implementation
            return BitVecRef(Z3_mk_zero_ext(expr.decl().ctx_ref(), target_bitwidth - children[0].sort().size(), children[0].as_ast()))
        elif expr.decl().kind() == Z3_OP_BIT2BOOL:
            return BoolRef(Z3_mk_bit2bool(expr.decl().ctx_ref(), children[0].as_ast()))
        elif expr.decl().kind() == Z3_OP_BV2INT:
            # TODO: check whether hardcoding unsigned is acceptable
            return ArithRef(Z3_mk_bv2int(expr.decl().ctx_ref(), children[0].as_ast(), 0))
        elif expr.decl().kind() == Z3_OP_INT2BV:
            return BitVecRef(Z3_mk_int2bv(expr.decl().ctx_ref(), target_bitwidth, children[0].as_ast()))
        elif expr.decl().kind() == Z3_OP_ULEQ:
            return BoolRef(Z3_mk_bvule(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_SLEQ:
            return BoolRef(Z3_mk_bvsle(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_UGEQ:
            return BoolRef(Z3_mk_bvuge(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_SGEQ:
            return BoolRef(Z3_mk_bvsge(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_ULT:
            return BoolRef(Z3_mk_bvult(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_SLT:
            return BoolRef(Z3_mk_bvslt(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_UGT:
            return BoolRef(Z3_mk_bvugt(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_SGT:
            return BoolRef(Z3_mk_bvsgt(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_ITE:
            return BitVecRef(Z3_mk_ite(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast(), children[2].as_ast()))
        elif expr.decl().kind() == Z3_OP_EQ:
            return BoolRef(Z3_mk_eq(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        elif expr.decl().kind() == Z3_OP_DISTINCT:
            def _to_ast_array(args):
                sz = len(args)
                _args = (Ast * sz)()
                for i in range(sz):
                    _args[i] = args[i].as_ast()
                return _args

            return BoolRef(Z3_mk_distinct(expr.decl().ctx_ref(), len(children), _to_ast_array(children)))
        elif expr.decl().kind() == Z3_OP_EXTRACT:
            left = expr.params()[0]
            right = expr.params()[1]

            # TODO: clamping if it is too big

            # specification probably not down scalable -> i have no idea how to extract the information from the term correctly
            # raise Exception("Extract not supported for downscaling")

            if left >= target_bitwidth:
                left = target_bitwidth
            if right >= target_bitwidth:
                right = target_bitwidth

            return BitVecRef(Z3_mk_extract(expr.decl().ctx_ref(), left, right, children[0].as_ast()))

        
        # only checker operations, hopefully not needed...
        # elif expr.decl().kind() == Z3_OP_BSMUL_NO_OVFL:
        #     return BitVecRef(Z3_mk_bvmul_no_overflow(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast(), True))
        # elif expr.decl().kind() == Z3_OP_BUMUL_NO_OVFL:
        #     return BitVecRef(Z3_mk_bvmul_no_overflow(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast(), False))
        # elif expr.decl().kind() == Z3_OP_BSMUL_NO_UDFL:
        #     return BitVecRef(Z3_mk_bvmul_no_underflow(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast(), True))
        # elif expr.decl().kind() == Z3_OP_BSDIV_I:
        #     return BitVecRef(Z3_mk_bvsdiv_no_overflow(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        # elif expr.decl().kind() == Z3_OP_BUDIV_I:
        #     return BitVecRef(Z3_mk_bvsdiv_no_overflow(expr.decl().ctx_ref(), children[0].as_ast(), children[1].as_ast()))
        
        # print(expr.decl().kind())

        return expr.decl()(*children)

    return expr

def spec_insert_in_outs(spec: Spec, decl_map, target_bitwidth):
    # insert inputs and outputs if they are not already there
    for expr in spec.inputs + spec.outputs:
        decl_map[expr.decl()] = transform_constant_to_bitwidth(expr, target_bitwidth)

def transform_to_bitwidth(spec: Spec, decl_map, target_bitwidth):
    ins = spec.inputs
    outs = spec.outputs
    phi = spec.phi
    precond = spec.precond

    spec_insert_in_outs(spec, decl_map, target_bitwidth)

    # just for funsies: test whether outputs and inputs are always "constant" expressions
    for expr in ins + outs:
        assert len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED, "Inputs and outputs must be constants"

    ins = [ transform_to_bitwidth_expr_ref(i, decl_map, target_bitwidth) for i in ins ]
    outs = [ transform_to_bitwidth_expr_ref(o, decl_map, target_bitwidth) for o in outs ]
    # print(phi)
    phi = transform_to_bitwidth_expr_ref(phi, decl_map, target_bitwidth)
    # print(phi)
    precond = transform_to_bitwidth_expr_ref(precond, decl_map, target_bitwidth)

    return Spec(spec.name, phi,  outs, ins, precond)


def transform_to_bw_func(op: Func, decl_map, target_bitwidth):
    spec_insert_in_outs(op, decl_map, target_bitwidth)

    phi = transform_to_bitwidth_expr_ref(op.func, decl_map, target_bitwidth)
    precond = transform_to_bitwidth_expr_ref(op.precond, decl_map, target_bitwidth)
    inputs = [ transform_to_bitwidth_expr_ref(i, decl_map, target_bitwidth) for i in op.inputs ]

    # print(toSMT2Benchmark(precond))

    res_fun = Func(op.name, phi, precond, inputs)

    return res_fun



class SynthConstants:
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

        self.op_from_orig = { orig: new for new, orig in self.orig_ops.items() }

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
        self.const_set = const_set
        # self.add_constr_wfp(max_const, const_set)
        # self.add_constr_ty()
        # self.add_constr_opt(opt_no_dead_code, opt_no_cse, opt_const, \
        #                     opt_commutative, opt_insn_order)
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

        # If supplied with an empty det of constants, we don't allow any constants
        if not const_set is None and len(const_set) == 0:
            max_const = 0

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
        s = self.orig_spec
        return Prg(s.ctx, insns, outputs, s.outputs, s.inputs)


    def get_const_var(self, ty, insn, opnd, instance):
        return self.get_var(ty, f'insn_{insn}_opnd_{opnd}_{ty}_const_val', instance)
    
    def set_prg(self, prg: Prg):
        self.prg = prg

    def write_constraints(self, instance):
        prg = self.prg

        ins  = [ self.var_insn_res(i, self.in_tys[i], instance) for i in range(self.n_inputs) ]

        exists_quantified = set()

        constraints = []

        const_set = {}

        # program is already well-formed by construction -> no constraint needed
        # set result for each operator by adding constraints
        for insn in range(self.n_inputs, self.length - self.n_outputs):
            # get operator from synthesized program
            (op, args) = prg.insns[insn - self.n_inputs]

            # get the operator in the current context of the synthesizer
            translated_op = self.op_from_orig[op]


            operands = []

            # set the operands of the instruction to the operands of the synthesized program
            for (index, (is_const, value)) in enumerate(args):
                # if not const, set operand value = index of the instruction it is coming from
                if is_const:
                    const_var = self.get_const_var(translated_op.in_types[index], insn, index, 'fa')
                    operands.append(const_var)
                    const_set[(insn, index)] = const_var
                else:
                    if value < self.n_inputs:
                        out_type = self.in_tys[value]
                    else:
                        # value is index of the instruction it is coming from
                        out_type = self.op_from_orig[prg.insns[value - self.n_inputs][0]].out_type

                    operands.append(self.var_insn_res(value, out_type, instance))
            
            # set the operator of the instruction to the operator in the current context
            res = self.var_insn_res(insn, translated_op.out_type, instance)
            # quantified after instantiation
            exists_quantified.add(res)

            precond, phi = translated_op.instantiate([ res ], operands)
            constraints.append(And([ precond, phi ]))
        
        # add connection constraints for output instruction -> IO spec
        operands = []
        for (index, (is_const, value)) in enumerate(prg.outputs):
            if is_const:
                const_var = self.get_const_var(self.out_tys[index], self.out_insn, index, 'fa')
                operands.append(const_var)
                const_set[(self.out_insn, index)] = const_var
            else:
                if value < self.n_inputs:
                    out_type = self.in_tys[value]
                else:
                    out_type = self.op_from_orig[prg.insns[value - self.n_inputs][0]].out_type
                operands.append(self.var_insn_res(value, out_type, instance))
        
        for operand, val in zip(operands, self.var_outs_val(instance)):
            constraints.append(operand == val)

        # precond, phi = self.spec.instantiate(operands, ins)
        
        # constraints.append(Implies(precond, phi))

        for c in constraints:
            self.synth.add(c)
        
        return const_set

    def add_constr_io_sample_prg(self, instance, in_vals, out_vals):
        # add input value constraints
        assert len(in_vals) == self.n_inputs and len(out_vals) == self.n_outputs
        for inp, val in enumerate(in_vals):
            assert not val is None
            res = self.var_insn_res(inp, self.in_tys[inp], instance)
            self.synth.add(res == val)
        for out, val in zip(self.var_outs_val(instance), out_vals):
            assert not val is None
            self.synth.add(out == val)

    def add_constr_io_spec_prg(self, instance, in_vals):
        # add input value constraints
        assert len(in_vals) == self.n_inputs
        assert all(not val is None for val in in_vals)
        for inp, val in enumerate(in_vals):
            self.synth.add(val == self.var_insn_res(inp, self.in_tys[inp], instance))
        outs = [ v for v in self.var_outs_val(instance) ]
        precond, phi = self.spec.instantiate(outs, in_vals)
        self.synth.add(Implies(precond, phi))
    
    def prg_from_changed_model(self, m, const_set, old_prg):
        # if sat, we found location variables
            
        # prg = self.create_prg(m)

        prg_insns = []

        for (insn, prg_ins) in enumerate(old_prg.insns):
            (op, args) = prg_ins
            new_args = []
            for (index, (is_const, value)) in enumerate(args):
                if is_const:
                    new_args.append((is_const, m[const_set[(insn + self.n_inputs, index)]].translate(self.orig_spec.ctx)))
                else:
                    new_args.append((is_const, value))
            prg_insns.append((op, new_args))
        
        new_outputs = []

        for (index, (is_const, value)) in enumerate(old_prg.outputs):
            if is_const:
                new_outputs.append((is_const, m[const_set[(self.out_insn, index)]].translate(self.orig_spec.ctx)))
            else:
                new_outputs.append((is_const, value))
        
        return Prg(self.orig_spec.ctx, prg_insns, new_outputs, self.orig_spec.outputs, self.orig_spec.inputs)

    def synth_with_new_samples(self, samples):
        ctx       = self.ctx

        prg = self.prg
        assert prg is not None

        samples   = [ [ v.translate(ctx) for v in s ] for s in samples ]


        # const set
        const_set = {}

        # main synthesis algorithm.
        # 1) set up counter examples
        for sample in samples:
            # add a new instance of the specification for each sample

            # const set is always the same for all instances
            const_set = self.write_constraints(self.n_samples)
            if self.spec.is_deterministic and self.spec.is_total:
                # if the specification is deterministic and total we can
                # just use the specification to sample output values and
                # include them in the counterexample constraints.
                out_vals = self.spec.eval(sample)
                # print(sample)
                # print(out_vals)
                self.add_constr_io_sample_prg(self.n_samples, sample, out_vals)
            else:
                # if the spec is not deterministic or total, we have to
                # express the output of the specification implicitly by
                # the formula of the specification.
                self.add_constr_io_spec(self.n_samples, sample)
            self.n_samples += 1
        # write_smt2('synth', self.n_insns, self.n_samples)
        stat = {}

        

        if self.reset_solver:
            self.synth_solver.reset()
            self.synth_solver.add(self.synth)

        # print(self.synth_solver.to_smt2())
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

            prg = self.prg_from_changed_model(m, const_set, self.prg)

            # print(m, "\n")
            # print(prg, "\n")

            # prg = self.create_prg(m)
            self.d(4, 'model: ', m)
            return prg, stat
        else:
            return None, stat

    def synth_with_new_spec(self, prg: Prg):
        ctx       = self.ctx
        ins  = [ self.var_insn_res(i, self.in_tys[i], 'fa') for i in range(self.n_inputs) ]

        exists_quantified = set()

        constraints = []

        const_set = {}


        # program is already well-formed by construction -> no constraint needed
        # set result for each operator by adding constraints
        for insn in range(self.n_inputs, self.length - self.n_outputs):
            # get operator from synthesized program
            (op, args) = prg.insns[insn - self.n_inputs]

            # get the operator in the current context of the synthesizer
            translated_op = self.op_from_orig[op]


            operands = []

            # set the operands of the instruction to the operands of the synthesized program
            for (index, (is_const, value)) in enumerate(args):
                # if not const, set operand value = index of the instruction it is coming from
                if is_const:
                    const_var = self.get_const_var(translated_op.in_types[index], insn, index, 'fa')
                    operands.append(const_var)
                    const_set[(insn, index)] = const_var
                else:
                    # value is index of the instruction it is coming from
                    out_type = self.op_from_orig[prg.insns[value - self.n_inputs][0]].out_type

                    operands.append(self.var_insn_res(value, out_type, 'fa'))
            
            # set the operator of the instruction to the operator in the current context
            res = self.var_insn_res(insn, translated_op.out_type, 'fa')
            # quantified after instantiation
            exists_quantified.add(res)

            precond, phi = translated_op.instantiate([ res ], operands)
            # TODO: why and???
            constraints.append(And([ precond, phi ]))
        
        # add connection constraints for output instruction -> IO spec
        operands = []
        for (index, (is_const, value)) in enumerate(prg.outputs):
            if is_const:
                const_var = self.get_const_var(self.out_tys[index], self.out_insn, index, 'fa')
                operands.append(const_var)
                const_set[(self.out_insn, index)] = const_var
            else:
                out_type = self.op_from_orig[prg.insns[value - self.n_inputs][0]].out_type
                operands.append(self.var_insn_res(value, out_type, 'fa'))
        
        precond, phi = self.spec.instantiate(operands, ins)
        
        constraints.append(Implies(precond, phi))

        s = Solver(ctx=self.ctx)
        # Add forall
        s.add(ForAll(ins, Exists(list(exists_quantified), And(constraints))))

        if self.output_prefix:
            filename = f'{self.output_prefix}_synth.smt2'
            with open(filename, 'w') as f:
                print(s.to_smt2(), file=f)

        stat = {}
        self.d(3, 'synth', s)
        with timer() as elapsed:
            res = s.check()
            synth_time = elapsed()
            stat['synth_stat'] = s.statistics()
            self.d(5, stat['synth_stat'])
            self.d(2, f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = s.model()
            # prg = self.create_prg(m)

            prg = self.prg_from_changed_model(m, const_set, prg)


            # TODO: get out constant values
            # print(m)

            

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

    # try synthezising the program with smaller bitwidth first -> transform spec and ops to smaller bitwidth


    for target_bw in [4]:
        # maps "constant" declarations to their new counterpart
        decl_map = {}


        # constants: use "Extract" https://z3prover.github.io/api/html/namespacez3py.html#a40e9429ef16134a6d9914ecdc2182e8c -> was not necessary for some reason (conv was enough)

        try:
            new_spec = transform_to_bitwidth(spec, decl_map, target_bw)
            ops_map = { transform_to_bw_func(op, decl_map, target_bw): (op, val) for op, val in ops.items()}
            new_ops = { new_op: val for new_op, (old_op, val) in ops_map.items() }

        except Exception as e:
            print(e)
            # raise e
            continue

        # TODO: decide whether to actually transform the constants or just remove them
        # transform const set?
        
        downscaled_args = args.copy()
        if args['const_set'] is not None:
            new_const_set = { BitVecVal(expr.as_long(), target_bw) for expr in args['const_set'] }
            downscaled_args['const_set'] = new_const_set

        # print(spec.outputs[0].sort())

        # print(toSMT2Benchmark(spec.phi))
        # for op in ops:
        #     print(toSMT2Benchmark(op.phi))

        prg, stats = run_synth(new_spec, new_ops, iter_range, n_samples, **downscaled_args)

        all_stats.extend(stats)

        print(f"program for target bit width {target_bw}:", prg)


        if not prg is None:
            # try to upscale the program
            n_insns = len(prg.insns)

            original_prg_insns = [ (ops_map[op][0], args) for (op, args) in prg.insns ]
            original_prg = Prg(spec.ctx, original_prg_insns, prg.outputs, spec.outputs, spec.inputs)

            with timer() as elapsed:
                synthesizer = SynthConstants(spec, ops, n_insns, **args)
                

                if use_cegis:
                    # TODO: use counter examples from previous synthesis as well?
                    synthesizer.set_prg(original_prg)
                    init_samples = spec.eval.sample_n(n_samples)
                    prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                               debug=synthesizer.d)
                else:
                    prg, stats = synthesizer.synth_with_new_spec(original_prg)

                all_stats += [ { 'time': elapsed(), 'iterations': stats } ]

                # return prg, stats
                if prg is not None:
                   return prg, all_stats
                else:
                    print(f"not able to scale program from {target_bw}bit ")
    
    prg, stats = run_synth(spec, ops, iter_range, n_samples, **args)
    all_stats.extend(stats)
    return prg, all_stats




def run_synth(spec: Spec, ops, iter_range, n_samples=1, **args):
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