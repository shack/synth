from functools import lru_cache
from collections import defaultdict
from math import log2

from z3 import *

from cegis import Spec, Func, Prg, no_debug, timer, cegis
from util import bv_sort

from synth_n import EnumSortEnum, SynthN, OpFreq

class SynthNOptimize(SynthN):
    def __init__(self, spec: Spec, ops: list[Func], n_insns, \
            debug=no_debug, timeout=None, max_const=None, const_set=None, \
            output_prefix=None, theory=None, reset_solver=True, \
            opt_no_dead_code=True, opt_no_cse=True, opt_const=True, \
            opt_commutative=True, opt_insn_order=True,
            use_minimizer=False, additional_id_insn=True):

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
        self.additional_id_insn = additional_id_insn
        if additional_id_insn:
            ops = list(ops) + [ Func('id', spec.outputs[0]) ]

        
        
        self.spec      = spec = spec.translate(ctx)

        if len(ops) == 0:
            ops = { Func('dummy', Int('v') + 1): 0 }
        elif type(ops) == list or type(ops) == set:
            ops = { op: OpFreq.MAX for op in ops }

        self.orig_ops  = { op.translate(ctx): op for op in ops }
        self.op_freqs  = { op_new: ops[op_old] for op_new, op_old in self.orig_ops.items() }
        self.ops       = ops = list(self.orig_ops.keys())
        self.n_insns   = n_insns

        if additional_id_insn:
            self.id        = ops[-1]

        

        self.use_minimizer = use_minimizer

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

        if use_minimizer:
            self.synth_solver = Optimize(ctx=self.ctx)
            # self.synth_solver.set(priority='pareto')
            self.synth = self.synth_solver
        else:
            if theory:
                self.synth_solver = SolverFor(theory, ctx=ctx)
            else:
                self.synth_solver = Tactic('psmt', ctx=ctx).solver()
            self.synth = Goal(ctx=ctx) if reset_solver else self.synth_solver


        if not timeout is None:
            self.synth_solver.set('timeout', timeout)
        
        # add well-formedness, well-typedness, and optimization constraints
        self.add_constr_wfp(max_const, const_set)
        self.add_constr_ty()
        self.add_constr_opt(opt_no_dead_code, opt_no_cse, opt_const, \
                            opt_commutative, opt_insn_order)
        
        # well-formedness for id operator
        if additional_id_insn:
            self.add_constr_id_wfp()

        self.d(1, 'size', self.n_insns)


    def add_constr_id_wfp(self):
        solver = self.synth

        # id is only used for the output as a last instruction
        # iterate over all instructions used in output
        for insn in range(self.n_inputs, self.out_insn):
            # get operator of instruction
            op_var = self.var_insn_op(insn)
            # get the id operator
            id_id = self.op_enum.item_to_cons[self.id]
            # every following instruction is id
            cons = [ self.var_insn_op(f_insn) == id_id for f_insn in range(insn + 1, self.out_insn)]
            # if the operator is id, every following insn operator is also id (if there is at least one following insn)
            solver.add(Implies(op_var == id_id, And(cons, self.ctx)))

        # only first id may receive a constant as an operand
        # iterate over all instructions used in output
        for insn in range(self.n_inputs, self.out_insn):
            # get operator of instruction
            op_var = self.var_insn_op(insn)
            # get the id operator
            id_id = self.op_enum.item_to_cons[self.id]
            # if operator is id AND  >=one of the operands is a constant
            cond = And(op_var == id_id, Or([var == True for var in self.var_insn_opnds_is_const(insn)]))
            # then every previous instruction may not be id
            cons = [ self.var_insn_op(f_insn) != id_id for f_insn in range(self.n_inputs, insn)]
            solver.add(Implies(cond, And(cons, self.ctx)))
    
    def synth_with_new_samples(self, samples):
        ctx       = self.ctx
        samples   = [ [ v.translate(ctx) for v in s ] for s in samples ]

        def write_smt2(*args):
            s = self.synth
            if not type(s) is Solver and not self.use_minimizer:
                s = Solver(ctx=ctx)
                s.add(self.synth)
            if self.output_prefix:
                filename = f'{self.output_prefix}_{"_".join(str(a) for a in args)}.smt2'
                with open(filename, 'w') as f:
                    print(s.to_smt2(), file=f)

        # main synthesis algorithm.
        # 1) set up counter examples
        for sample in samples:
            # add a new instance of the specification for each sample
            self.add_constr_instance(self.n_samples)
            if self.spec.is_deterministic and self.spec.is_total:
                # if the specification is deterministic and total we can
                # just use the specification to sample output values and
                # include them in the counterexample constraints.
                out_vals = self.spec.eval(sample)
                self.add_constr_io_sample(self.n_samples, sample, out_vals)
            else:
                # if the spec is not deterministic or total, we have to
                # express the output of the specification implicitly by
                # the formula of the specification.
                self.add_constr_io_spec(self.n_samples, sample)
            self.n_samples += 1
        write_smt2('synth', self.n_insns, self.n_samples)
        stat = {}
        if not self.use_minimizer:
            if self.reset_solver:
                self.synth_solver.reset()
                self.synth_solver.add(self.synth)
        self.d(3, 'synth', self.n_samples, self.synth_solver)
        with timer() as elapsed:
            res = self.synth_solver.check()
            synth_time = elapsed()
            stat['synth_stat'] = str(self.synth_solver.statistics())
            self.d(5, stat['synth_stat'])
            self.d(2, f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = self.synth_solver.model()
            prg = self.create_prg(m)
            self.d(4, 'model: ', m)
            return prg, stat
        else:
            return None, stat

class SynthOptimizer():
    def add_constraint(self, synthn: SynthN):
        pass


class DepthOptimization(SynthOptimizer):
    def __init__(self, max_depth) -> None:
        self.max_depth = max_depth

    # number of bits to represent the length
    def get_bv_ln(self, synthn: SynthN):
        x = int(log2(synthn.length)) + 1
        # print(x)
        # always unsolvable with calculated length - 8 bits should be fine for now (< 256 instructions are synthesized anyway)
        return x + 1

    # get depth cost variable for an instruction
    def get_depth_cost(self, insn,  synthn: SynthN):
        return synthn.get_var(BitVecSort(self.get_bv_ln(synthn), synthn.ctx), f'insn_{insn}_depth')
    
    def get_operand_cost(self, insn, opnd,  synthn: SynthN):
        return synthn.get_var(BitVecSort(self.get_bv_ln(synthn), synthn.ctx), f'insn_{insn}_opnd_{opnd}_cost')

    def add_constraint(self, synthn: SynthN):
        # for all instructions, restrain max value to the number of instructions -> allows QF_FD to restrict integers
        for insn in range(synthn.length):
            synthn.synth.add(And([0 <= self.get_depth_cost(insn, synthn), self.get_depth_cost(insn, synthn) < synthn.length]))

        # for input instructions, the depth cost is 0
        for insn in range(synthn.n_inputs):
            synthn.synth.add(self.get_depth_cost(insn, synthn) == 0)

        def Max(operands):
            if len(operands) == 0:
                return 0
            m = operands[0]
            for o in operands[1:]:
                m = If(o > m, o, m)
            return m
        
        # for all other instructions, the depth cost is the maximum of the
        # depth costs of the operands plus 1
        for insn in range(synthn.n_inputs, synthn.length):
            insn_depth = self.get_depth_cost(insn, synthn)

            # depth cost can only be influenced by previous instructions
            for p_insn in range(insn):
                for opndn, opnd in zip(range(synthn.arities[insn]), synthn.var_insn_opnds(insn)):
                    synthn.synth.add(Implies(opnd == p_insn, self.get_operand_cost(insn, opndn, synthn) == self.get_depth_cost(p_insn, synthn)))


            op_depths = [ If(c, 0, self.get_operand_cost(insn, opnd, synthn)) for opnd, c in zip(range(synthn.arities[insn]), synthn.var_insn_opnds_is_const(insn)) ]
            
            # id operator allows no-cost adding depth
            if synthn.additional_id_insn:
                # get operator of instruction
                op_var = synthn.var_insn_op(insn)
                # get the id operator
                id_id = synthn.op_enum.item_to_cons[synthn.id]

                # if the operator is id, The cost is the maximum, else it is the maximum of the operands + 1
                synthn.synth.add(Implies(op_var == id_id, insn_depth == Max(op_depths)))
                synthn.synth.add(Implies(op_var != id_id, insn_depth == 1 + Max(op_depths)))
            else:
                synthn.synth.add(insn_depth == 1 + Max(op_depths))
        
        # fix depth cost of output instruction
        if self.max_depth is not None:
            synthn.synth.add(self.get_depth_cost(synthn.out_insn, synthn) <= self.max_depth)
        else:
            synthn.synth.minimize(self.get_depth_cost(synthn.out_insn, synthn))
        

class OperatorUsageOptimization(SynthOptimizer):
    def __init__(self, max_op_num) -> None:
        self.max_op_num = max_op_num

    # get depth cost variable for an instruction
    def get_operator_used(self, op,  synthn: SynthN):
        return synthn.get_var(BitVecSort(8, synthn.ctx), f'op_{op}_used')
    
    def add_constraint(self, synthn: SynthN):
        for _, op_id in synthn.op_enum.item_to_cons.items():
            # whether the operator is used in any instruction
            used = Or([ op_id == synthn.var_insn_op(insn) for insn in range(synthn.n_inputs, synthn.out_insn) ], synthn.ctx)

            assert(used.ctx == synthn.ctx)

            # synthn.synth.add(And([Implies(used, self.get_operator_used(op_id, synthn) == BitVecVal(1, 8, synthn.ctx)), Implies(Not(used), self.get_operator_used(op_id, synthn) == BitVecVal(0, 8, synthn.ctx))]))
            #synthn.synth.add(And([Implies(used, self.get_operator_used(op_id, synthn) == 1), Implies(Not(used), self.get_operator_used(op_id, synthn) == 0)]))# If(used, 1, 0))
            synthn.synth.add(self.get_operator_used(op_id, synthn) == If(used, BitVecVal(1, 8, synthn.ctx), BitVecVal(0, 8, synthn.ctx), ctx=synthn.ctx))


        # calculate sum of used operators
        sum = BitVec('op_usage_sum', 8, synthn.ctx)

        def sum_bv(operands):
            if len(operands) == 0:
                return 0
            m = operands[0]
            for o in operands[1:]:
                m = m + o
            return m
        
        synthn.synth.add(sum == sum_bv([ self.get_operator_used(op_id, synthn) for _, op_id in synthn.op_enum.item_to_cons.items() ]))

        # constrain the sum of used operators
        if self.max_op_num is not None:
            synthn.synth.add(sum <= self.max_op_num)
        else:
            synthn.synth.minimize(sum)


# requires optimizer as solver
class LengthOptimizer(SynthOptimizer):
    def get_length_cost(self, insn,  synthn: SynthN):
        return synthn.get_var(BitVecSort(8, synthn.ctx), f'insn_{insn}_depth')

    def add_constraint(self, synthn: SynthN):
        # optimization makes no sense without id instruction
        # id operator allows no-cost adding depth
        if synthn.additional_id_insn:
            # for all instructions, restrain max value to the number of instructions -> allows QF_FD to restrict integers
            for insn in range(synthn.length):
                synthn.synth.add(And([0 <= self.get_length_cost(insn, synthn), self.get_length_cost(insn, synthn) < synthn.length]))

            # for input instructions, the length cost is 0
            for insn in range(synthn.n_inputs):
                synthn.synth.add(self.get_length_cost(insn, synthn) == 0)
            
            # for all other instructions, the length cost is the length of the
            # previous instruction + 1, iff the operator is not id
            for insn in range(synthn.n_inputs, synthn.length):
                insn_length = self.get_length_cost(insn, synthn)
                prev_insn = self.get_length_cost(insn - 1, synthn)
                
                # get operator of instruction
                op_var = synthn.var_insn_op(insn)
                # get the id operator
                id_id = synthn.op_enum.item_to_cons[synthn.id]

                # if the operator is id, The cost is the maximum, else it is the maximum of the operands + 1
                synthn.synth.add(Implies(op_var == id_id, insn_length == prev_insn))
                synthn.synth.add(Implies(op_var != id_id, insn_length == 1 + prev_insn))
            
            synthn.synth.minimize(self.get_length_cost(synthn.out_insn, synthn))


def run_simple_depth_optimization(spec: Spec, ops, iter_range, n_samples=1, **args):
    all_stats = []
    init_samples = spec.eval.sample_n(n_samples)
    for n_insns in iter_range:
        # iterate over depths
        # for depth in range(1, n_insns + 1):
            with timer() as elapsed:
                print(f'attempting to synthesize with {n_insns} instructions and depth')
                synthesizer = SynthNOptimize(spec, ops, n_insns, use_minimizer=True, **args)

                # LengthOptimizer().add_constraint(synthesizer)
                DepthOptimization(None).add_constraint(synthesizer)
                # DepthOptimization(2).add_constraint(synthesizer)

                prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                                debug=synthesizer.d)
                all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
                if not prg is None:
                    return prg, all_stats
    return None, all_stats

def run_iterated_depth_optimization(spec: Spec, ops, iter_range, n_samples=1, **args):
    all_stats = []
    init_samples = spec.eval.sample_n(n_samples)
    for n_insns in iter_range:
        # iterate over depths
        for depth in range(1, n_insns + 1):
            with timer() as elapsed:
                print(f'attempting to synthesize with {n_insns} instructions and depth')
                synthesizer = SynthNOptimize(spec, ops, n_insns, use_minimizer=False, **args)

                # LengthOptimizer().add_constraint(synthesizer)
                # DepthOptimization(None).add_constraint(synthesizer)
                DepthOptimization(depth).add_constraint(synthesizer)

                prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                                debug=synthesizer.d)
                all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
                if not prg is None:
                    return prg, all_stats
    return None, all_stats

def run_length_optimization(spec: Spec, ops, iter_range, n_samples=1, **args):
    all_stats = []
    init_samples = spec.eval.sample_n(n_samples)
    for n_insns in iter_range:
        # # iterate over depths
        # for depth in range(1, n_insns + 1):
            with timer() as elapsed:
                print(f'attempting to synthesize with {n_insns} instructions and depth')
                synthesizer = SynthNOptimize(spec, ops, n_insns, use_minimizer=True, **args)

                LengthOptimizer().add_constraint(synthesizer)
                # DepthOptimization(None).add_constraint(synthesizer)
                # DepthOptimization(depth).add_constraint(synthesizer)

                prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                                debug=synthesizer.d)
                all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
                if not prg is None:
                    return prg, all_stats
    return None, all_stats



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

    runs = {
        "simple_depth_optimization": run_simple_depth_optimization,
        "iterated_depth_optimization": run_iterated_depth_optimization,
        "length_optimization": run_length_optimization
    }

    run_type = "{{CAN_BE_REPLACED_BY_BENCHMARK}}"
    if run_type in runs:
        return runs[run_type](spec, ops, iter_range, n_samples, **args)

    all_stats = []
    init_samples = spec.eval.sample_n(n_samples)
    for n_insns in iter_range:
        # iterate over depths
        # for depth in range(1, n_insns + 1):
            with timer() as elapsed:
                print(f'attempting to synthesize with {n_insns} instructions and depth')
                synthesizer = SynthNOptimize(spec, ops, n_insns, use_minimizer=True, **args)

                # LengthOptimizer().add_constraint(synthesizer)
                DepthOptimization(None).add_constraint(synthesizer)
                # DepthOptimization(2).add_constraint(synthesizer)

                prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                                debug=synthesizer.d)
                all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
                if not prg is None:
                    return prg, all_stats
    return None, all_stats


    # all_stats = []
    # init_samples = spec.eval.sample_n(n_samples)
    # for depth in range(1, 10):
    #     with timer() as elapsed:
    #         # max number of instructions needed to synthesize the program
    #         n_insns = 2 ** depth


    #         print(f'attempting to synthesize with {n_insns} instructions and depth {depth}')
    #         synthesizer = SynthN(spec, ops, n_insns, depth, **args)
    #         prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
    #                         debug=synthesizer.d)
    #         all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
    #         if not prg is None:
    #             return prg, all_stats
    # return None, all_stats