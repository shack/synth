from z3 import *
from dataclasses import dataclass
from synth.spec import Spec, Func, Task, Prg, Constraint, SynthFunc, Problem

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

    # transform synthesis constraint
    new_constr = transform_synth_constraint_to_bitwidth(problem.constraint, decl_map, target_bitwidth)

    # operator_mapping = { new_op: op for op, (new_op, _) in ops_map.items() }
    ops_map = {}
    new_funcs = {}
    tgt_sort = BitVecSort(target_bitwidth)
    for name, func in problem.funcs.items():
        ops_map |= { op: transform_func_to_bitwidth(op, decl_map, target_bitwidth) for op in func.ops if not op in ops_map }
        new_ops = { ops_map[op]: val for op, val in func.ops.items() }

        if not func.const_map is None and keep_const_map:
            # create new constants by cutting off the bitwidth
            new_const_map = { BitVecVal(k.as_long(), target_bitwidth): v for k,v in func.const_map.items() }
        else:
            new_const_map = None

        new_funcs[name] = SynthFunc(
            outputs=[ (o[0], tgt_sort) for o in func.outputs ],
            inputs=[ (i[0], tgt_sort) for i in func.inputs ],
            ops=new_ops,
            const_map=new_const_map
        )

    new_problem = Problem(
        constraint=new_constr,
        funcs=new_funcs,
        theory='QF_BV'
    )

    inverse_ops_map = {v: k for k, v in ops_map.items()}
    return TransformedProblem(
        original_problem=problem,
        transformed_problem=new_problem,
        operator_mapping=inverse_ops_map
    )