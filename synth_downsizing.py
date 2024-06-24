
from z3 import *
from cegis import *
from synth_n import SynthN
from synth_fa import SynthFA


class SynthDS(SynthFA):
    pass




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
    



def synth(spec: Spec, ops, iter_range, n_samples=1, downsize=False, **args):
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

    # try synthezising the program with smaller bitwidth first -> transform spec and ops to smaller bitwidth


    for target_bw in [4, 8]:
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

        # print(spec.outputs[0].sort())

        # print(toSMT2Benchmark(spec.phi))
        # for op in ops:
        #     print(toSMT2Benchmark(op.phi))

        prg, stats = run_synth(new_spec, new_ops, iter_range, n_samples, **args)

        all_stats.extend(stats)

        print(f"program for target bit width {target_bw}:", prg)


        if not prg is None:
            # try to upscale the program
            n_insns = len(prg.insns)

            original_prg_insns = [ (ops_map[op][0], args) for (op, args) in prg.insns ]
            original_prg = Prg(spec, original_prg_insns, prg.outputs)

            with timer() as elapsed:
                # use synth_fa for finding constants

                synthesizer = SynthDS(spec, ops, n_insns, **args)
                synthesizer.add_prg_constraints(original_prg)

                prg, stats = synthesizer.do_synth()

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
            synthesizer = SynthDS(spec, ops, n_insns, **args)
            prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                               debug=synthesizer.d)
            all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
            if not prg is None:
                return prg, all_stats
    return None, all_stats