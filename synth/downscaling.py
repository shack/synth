from z3 import *
from dataclasses import dataclass, field
from synth import base_synths, util
from synth.cegis import cegis
from synth.spec import Spec, Func, Task, Prg, Constraint, SynthFunc, Problem, Nonterminal, Production
from synth.synth_n import LenCegis

"""Contains functions to downscale a given Task, Spec or Func object to a specified bitwidth

decl_map: dict[ExprRef, ExprRef] -  mapping of original expressions to transformed expressions.
                                    Useful if the same expression is used multiple times
target_bitwidth: int             -  target bitwidth to transform to
"""


def transform_constant_to_bitwidth(constant: ExprRef, target_bitwidth: int):
    if not is_bv_sort(constant.sort()):
        return constant

    # create new BV constant with target bitwidth
    # Naming of "_transformed" important for later identification in statistics collection
    return BitVec(f"{constant}_transformed", target_bitwidth, constant.ctx)

def transform_expr_ref_to_bitwidth(expr: ExprRef, decl_map: dict[ExprRef, ExprRef], target_bitwidth: int):
    if len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED:
        # check if it already transformed
        if expr.decl() in decl_map:
            return decl_map[expr.decl()]
        decl_map[expr.decl()] = transform_constant_to_bitwidth(expr, target_bitwidth)
        return decl_map[expr.decl()]

    # check if it is a constant
    if expr.decl().arity() == 0:
        if expr.decl().kind() == Z3_OP_BNUM:
            return BitVecVal(expr.as_long(), target_bitwidth)

    # transform operator
    if expr.decl().arity() > 0:
        # transform children
        children = [ transform_expr_ref_to_bitwidth(c, decl_map, target_bitwidth) for c in expr.children() ]
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
            # as per doc https://microsoft.github.io/z3guide/docs/theories/Bitvectors/#bitvectors-and-integers
            # it should be always unsigned
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

            # specification probably not down scalable -> do some arbitrary/heuristic extraction, might be totally incorrect
            if left >= target_bitwidth:
                left = target_bitwidth
            if right >= target_bitwidth:
                right = target_bitwidth

            return BitVecRef(Z3_mk_extract(expr.decl().ctx_ref(), left, right, children[0].as_ast()))

        return expr.decl()(*children)

    return expr

def spec_insert_in_outs(spec: Spec, decl_map: dict[ExprRef, ExprRef], target_bitwidth: int):
    # insert inputs and outputs if they are not already there
    for expr in spec.inputs + spec.outputs:
        decl_map[expr.decl()] = transform_constant_to_bitwidth(expr, target_bitwidth)

def transform_synth_constraint_to_bitwidth(constr: Constraint, decl_map: dict[ExprRef, ExprRef], target_bitwidth: int):
    res_vars = tuple(o for applications in constr.function_applications.values() for outs, _ in applications for o in outs)
    sorts = set(x.sort() for x in list(constr.params) + list(res_vars))
    assert len(sorts) == 1, "All constraint params and function outputs must have the same sort"
    sort = sorts.pop()
    assert is_bv_sort(sort), "Only bit vector constraints are supported"
    source_bitwidth = sort.size()
    assert source_bitwidth >= target_bitwidth, "Source bitwidth must be greater than the target bitwidth"

    precond = [ ULE(v, BitVecVal(2**target_bitwidth - 1, source_bitwidth)) for v in constr.params ]
    out_subst = {}
    new_func = {}
    for name, app in constr.function_applications.items():
        new_app = []
        for outs, ins in app:
            new_ins  = [ Extract(target_bitwidth - 1, 0, i) for i in ins ]
            new_outs = [ transform_constant_to_bitwidth(o, target_bitwidth) for o in outs ]
            new_app += [ (new_outs, new_ins) ]
            for o, n in zip(outs, new_outs):
                decl_map[o.decl()] = n
                out_subst[o] = ZeroExt(source_bitwidth - target_bitwidth, n)
        new_func[name] = new_app

    phi = substitute(constr.phi, *out_subst.items())

    return Constraint(
        phi=Implies(And(precond), phi),
        params=constr.params,
        function_applications=new_func
    )

def transform_func_to_bitwidth(op: Func, decl_map: dict[ExprRef, ExprRef], target_bitwidth: int):
    spec_insert_in_outs(op, decl_map, target_bitwidth)
    phi = transform_expr_ref_to_bitwidth(op.func, decl_map, target_bitwidth)
    precond = transform_expr_ref_to_bitwidth(op.precond, decl_map, target_bitwidth)
    inputs = tuple(transform_expr_ref_to_bitwidth(i, decl_map, target_bitwidth) for i in op.inputs)
    return Func(op.name, phi, precond, inputs)

@dataclass(frozen=True)
class TransformedProblem:
    original_problem: Problem
    transformed_problem: Problem
    operator_mapping: dict[ExprRef, ExprRef]

    def prgs_with_original_operators(self, prgs: dict[str, Prg]):
        res = {}
        for name, prg in prgs.items():
            original_prg_insn = [ (self.operator_mapping[op], args) for (op, args) in prg.insns ]
            res[name] = Prg(self.original_problem.funcs[name], original_prg_insn, prg.outputs)
        return res

def transform_problem_to_bitwidth(problem: Problem, target_bitwidth: int, keep_const_map: bool = False):
    """Try to downscale the given task to the target bitwidth. If not possible, it will throw an exception."""
    decl_map = {}

    # operator_mapping = { new_op: op for op, (new_op, _) in ops_map.items() }
    ops_map = {}
    new_funcs = {}
    tgt_sort = BitVecSort(target_bitwidth)
    for name, func in problem.funcs.items():
        new_nts = {}
        for nt_name, nt in func.nonterminals.items():
            prods = ()
            for prod in nt.productions:
                t_op = transform_func_to_bitwidth(prod.op, decl_map, target_bitwidth)
                prods += (Production(t_op, prod.operands, prod.attributes),)
                ops_map[prod.op] = t_op
            if nt.constants is not None:
                new_consts = { BitVecVal(k.as_long(), target_bitwidth): v for k,v in nt.constants.items() }
            else:
                new_consts = None
            new_nts[nt_name] = Nonterminal(
                name=nt.name,
                sort=tgt_sort,
                parameters=nt.parameters,
                productions=prods,
                constants=new_consts)

        new_funcs[name] = SynthFunc(
            outputs=[ (o[0], tgt_sort) for o in func.outputs ],
            inputs=[ (i[0], tgt_sort) for i in func.inputs ],
            nonterminals=new_nts,
            max_const=func.max_const,
            result_nonterminals=func.result_nonterminals
        )

    new_problem = Problem(
        constraints=[ transform_synth_constraint_to_bitwidth(c, decl_map, target_bitwidth) for c in problem.constraints ],
        funcs=new_funcs,
        theory='QF_BV'
    )

    inverse_ops_map = {v: k for k, v in ops_map.items()}
    return TransformedProblem(
        original_problem=problem,
        transformed_problem=new_problem,
        operator_mapping=inverse_ops_map
    )

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

@dataclass(frozen=True)
class CegisConstantSolver:
    def __call__(self, solver: Solver, problem: Problem, base_prgs: dict[str, Prg],
                 d: util.Debug = util.no_debug, verbose: bool = False):
        synths = { name: _ConstantSynth(func, base_prgs[name]) for name, func in problem.funcs.items() }
        prgs, stats, _ = cegis(solver, problem.constraint, synths, initial_samples=[],
                               d=d, verbose=verbose)
        return prgs, stats

@dataclass(frozen=True)
class FAConstantSolver:
    def __call__(self, solver: Solver, problem: Problem, base_prgs: dict[str, Prg],
                 d: util.Debug = util.no_debug, verbose: bool = False):
        synths = { name: _ConstantSynth(func, base_prgs[name]) for name, func in problem.funcs.items() }
        constraints = []
        params = problem.constraints[0].params
        for c in problem.constraints:
            c.add_instance_constraints('fa', synths, params, constraints)
        solver.add(ForAll(params, And(constraints)))
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

    target_bitwidth: list[int] = field(default_factory=lambda: [4])
    """Comma separated list of target bit widths (integer) to scale down to."""

    keep_const_map: bool = False
    """Whether to keep the constant map for the downscaling process."""

    base: base_synths.BASE_SYNTHS = field(kw_only=True, default_factory=lambda: LenCegis())
    """The base synthesiser to use for synthesis on the downscaled task."""

    constant_synth: CegisConstantSolver | FAConstantSolver = field(kw_only=True, default_factory=lambda: CegisConstantSolver())
    """The constant synthesizer to use."""

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
                prgs, stats = self.base.synth_prgs(scaled_problem.transformed_problem)
                curr_stats |= { 'synth_success': not prgs is None, 'stats': stats }
                if prgs is None:
                    self.debug('downscale', f"Failed to synthesize program(s) for bitwidth {target_bw}")
                    continue

                # scale up
                # revert to original operators
                prgs = scaled_problem.prgs_with_original_operators(prgs)
                with util.timer() as elapsed:
                    self.debug('downscale', f"Proposed program(s) for bitwidth {target_bw}:\n{str(prgs)}")

                    solver = self.base.solver.create(theory=problem.theory)
                    prgs, stats = self.constant_synth(solver, problem, prgs, d=self.base.debug, verbose=self.base.verbose)

                    curr_stats['const_finder'] = {
                        'time': elapsed(),
                        'stats': stats,
                        'success': not prgs is None
                    }
                if prgs is not None:
                    return prgs, { 'time': overall(), 'stats': res_stats, 'prg': str(prgs), 'fallback': False }

            # Fallback to normal synthesis if normal synthesis fails
            self.debug('downscale', f"Fallback to normal synthesis")
            prg, stats = self.base.synth_prgs(problem)
            return prg, { 'time': overall(), 'stats': res_stats, 'prg': str(prg), 'fallback': True }