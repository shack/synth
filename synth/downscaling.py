from z3 import *
from synth.spec import Spec, Func, Task, Prg

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

def transform_spec_to_bitwidth(spec: Spec, decl_map: dict[ExprRef, ExprRef], target_bitwidth: int):
    ins = spec.inputs
    outs = spec.outputs
    phi = spec.phi
    precond = spec.precond

    spec_insert_in_outs(spec, decl_map, target_bitwidth)

    # to ensure correctness: test whether outputs and inputs are always "constant" expressions
    for expr in ins + outs:
        assert len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED, "Inputs and outputs must be constants"

    ins = [ transform_expr_ref_to_bitwidth(i, decl_map, target_bitwidth) for i in ins ]
    outs = [ transform_expr_ref_to_bitwidth(o, decl_map, target_bitwidth) for o in outs ]
    # print(phi)
    phi = transform_expr_ref_to_bitwidth(phi, decl_map, target_bitwidth)
    # print(phi)
    precond = transform_expr_ref_to_bitwidth(precond, decl_map, target_bitwidth)

    return Spec(spec.name, phi,  outs, ins, precond)


def transform_func_to_bitwidth(op: Func, decl_map: dict[ExprRef, ExprRef], target_bitwidth: int):
    spec_insert_in_outs(op, decl_map, target_bitwidth)

    phi = transform_expr_ref_to_bitwidth(op.func, decl_map, target_bitwidth)
    precond = transform_expr_ref_to_bitwidth(op.precond, decl_map, target_bitwidth)
    inputs = [ transform_expr_ref_to_bitwidth(i, decl_map, target_bitwidth) for i in op.inputs ]

    res_fun = Func(op.name, phi, precond, inputs)

    return res_fun


class TransformedTask:
    def __init__(self, original_task: Task, transformed_task: Task, operator_mapping: dict[ExprRef, ExprRef]):
        self.original_task = original_task
        self.transformed_task = transformed_task
        # the mapping of the transformed operators to the original operators
        self.operator_mapping = operator_mapping
    
    def prg_with_original_operators(self, program: Prg): 
        original_prg_insn = [ (self.operator_mapping[op][0], args) for (op, args) in program.insns ]
        return Prg(program.ctx, original_prg_insn, program.outputs, program.out_vars, program.in_vars)
    

def transform_task_to_bitwidth(task: Task, target_bitwidth: int, keep_const_map: bool = False):
    """Try to downscale the given task to the target bitwidth. If not possible, it will throw an exception."""
    decl_map = {}

    # transform spec
    new_spec = transform_spec_to_bitwidth(task.spec, decl_map, target_bitwidth)

    # Transform operators
    ops_map = { transform_func_to_bitwidth(op, decl_map, target_bitwidth): (op, val) for op, val in task.ops.items() }
    new_ops = { new_op: val for new_op, (_, val) in ops_map.items() }

    # operator_mapping = { new_op: op for op, (new_op, _) in ops_map.items() }

    
    # apply const_map_tactic
    if task.const_map is None:
        new_const_map = None
    else:
        if keep_const_map:
            # create new constants by cutting off the bitwidth
            new_const_map = { BitVecVal(k.as_long(), target_bitwidth): v for k,v in task.const_map.items() }
        else:
            new_const_map = None

    new_task = Task(new_spec, new_ops, task.max_const, new_const_map, task.theory)

    return TransformedTask(task, new_task, ops_map)
    

