from z3 import *
from dataclasses import dataclass
from typing import Dict, Optional
from math import log2

class SynthOptimizer():
    """Base class for all optimizers"""
    def add_constraint(self, opt_cegis):
        pass

@dataclass(frozen=True)
class DepthOptimization(SynthOptimizer):
    max_depth: Optional[int] = None

    # number of bits to represent the length
    def get_bv_ln(self, opt_cegis):
        x = int(log2(opt_cegis.length)) + 1
        # print(x)
        # always unsolvable with calculated length - 8 bits should be fine for now (< 256 instructions are synthesized anyway)
        return x + 1

    # get depth cost variable for an instruction
    def get_depth_cost(self, insn,  opt_cegis):
        return opt_cegis.get_var(BitVecSort(self.get_bv_ln(opt_cegis), opt_cegis.ctx), f'insn_{insn}_depth')

    def get_operand_cost(self, insn, opnd,  opt_cegis):
        return opt_cegis.get_var(BitVecSort(self.get_bv_ln(opt_cegis), opt_cegis.ctx), f'insn_{insn}_opnd_{opnd}_cost')

    def add_constraint(self, opt_cegis):
        # for all instructions, restrain max value to the number of instructions -> allows QF_FD to restrict integers
        for insn in range(opt_cegis.length):
            opt_cegis.synth.add(And([0 <= self.get_depth_cost(insn, opt_cegis), self.get_depth_cost(insn, opt_cegis) < opt_cegis.length]))

        # for input instructions, the depth cost is 0
        for insn in range(opt_cegis.n_inputs):
            opt_cegis.synth.add(self.get_depth_cost(insn, opt_cegis) == 0)

        def Max(operands):
            if len(operands) == 0:
                return 0
            m = operands[0]
            for o in operands[1:]:
                m = If(o > m, o, m)
            return m

        # for all other instructions, the depth cost is the maximum of the
        # depth costs of the operands plus 1
        for insn in range(opt_cegis.n_inputs, opt_cegis.length):
            insn_depth = self.get_depth_cost(insn, opt_cegis)

            # depth cost can only be influenced by previous instructions
            for p_insn in range(insn):
                for opndn, opnd in zip(range(opt_cegis.arities[insn]), opt_cegis.var_insn_opnds(insn)):
                    opt_cegis.synth.add(Implies(opnd == p_insn, self.get_operand_cost(insn, opndn, opt_cegis) == self.get_depth_cost(p_insn, opt_cegis)))


            op_depths = [ If(c, 0, self.get_operand_cost(insn, opnd, opt_cegis)) for opnd, c in zip(range(opt_cegis.arities[insn]), opt_cegis.var_insn_opnds_is_const(insn)) ]

            # id operator allows no-cost adding depth
            if (opt_cegis.id is not None):
                # get operator of instruction
                op_var = opt_cegis.var_insn_op(insn)
                # get the id operator
                id_id = opt_cegis.op_enum.item_to_cons[opt_cegis.id]

                # if the operator is id, The cost is the maximum, else it is the maximum of the operands + 1
                opt_cegis.synth.add(Implies(op_var == id_id, insn_depth == Max(op_depths)))
                opt_cegis.synth.add(Implies(op_var != id_id, insn_depth == 1 + Max(op_depths)))
            else:
                opt_cegis.synth.add(insn_depth == 1 + Max(op_depths))

        # fix depth cost of output instruction
        if self.max_depth is not None:
            opt_cegis.synth.add(self.get_depth_cost(opt_cegis.out_insn, opt_cegis) <= self.max_depth)
        else:
            opt_cegis.synth.minimize(self.get_depth_cost(opt_cegis.out_insn, opt_cegis))


@dataclass(frozen=True)
class OperatorUsageOptimization(SynthOptimizer):
    max_op_num: Optional[int] = None
    
    # get depth cost variable for an instruction
    def get_operator_used(self, op,  opt_cegis):
        return opt_cegis.get_var(BitVecSort(8, opt_cegis.ctx), f'op_{op}_used')

    def add_constraint(self, opt_cegis):
        for _, op_id in opt_cegis.op_enum.item_to_cons.items():
            # whether the operator is used in any instruction
            used = Or([ op_id == opt_cegis.var_insn_op(insn) for insn in range(opt_cegis.n_inputs, opt_cegis.out_insn) ], opt_cegis.ctx)

            assert(used.ctx == opt_cegis.ctx)

            # opt_cegis.synth.add(And([Implies(used, self.get_operator_used(op_id, opt_cegis) == BitVecVal(1, 8, opt_cegis.ctx)), Implies(Not(used), self.get_operator_used(op_id, opt_cegis) == BitVecVal(0, 8, opt_cegis.ctx))]))
            #opt_cegis.synth.add(And([Implies(used, self.get_operator_used(op_id, opt_cegis) == 1), Implies(Not(used), self.get_operator_used(op_id, opt_cegis) == 0)]))# If(used, 1, 0))
            opt_cegis.synth.add(self.get_operator_used(op_id, opt_cegis) == If(used, BitVecVal(1, 8, opt_cegis.ctx), BitVecVal(0, 8, opt_cegis.ctx), ctx=opt_cegis.ctx))


        # calculate sum of used operators
        sum = BitVec('op_usage_sum', 8, opt_cegis.ctx)

        def sum_bv(operands):
            if len(operands) == 0:
                return 0
            m = operands[0]
            for o in operands[1:]:
                m = m + o
            return m

        opt_cegis.synth.add(sum == sum_bv([ self.get_operator_used(op_id, opt_cegis) for _, op_id in opt_cegis.op_enum.item_to_cons.items() ]))

        # constrain the sum of used operators
        if self.max_op_num is not None:
            opt_cegis.synth.add(sum <= self.max_op_num)
        else:
            opt_cegis.synth.minimize(sum)

@dataclass(frozen=True)
class OperatorHaveCostsOptimization(SynthOptimizer):
    # TODO: add support for costs via parameters
    op_to_cost: Dict[int, int]
    max_cost: Optional[int] = None

    def get_op_cost(self, insn,  opt_cegis):
        return opt_cegis.get_var(BitVecSort(8, opt_cegis.ctx), f'insn_{insn}_cost')

    def add_constraint(self, opt_cegis):
        operator_to_const = { trans_op: self.op_to_cost.get(op,  0) for (trans_op, op) in opt_cegis.orig_ops.items() }

        assert(opt_cegis.id is not None)
        
        # set carried cost to 0 for first operator
        opt_cegis.synth.add(self.get_op_cost(opt_cegis.n_inputs - 1, opt_cegis) == 0)
        # For each instruction, set next operator cost based on the previous operator cost
        for insn in range(opt_cegis.n_inputs, opt_cegis.length):
            for op, op_id in opt_cegis.op_enum.item_to_cons.items():
                # add cost for the operator
                opt_cegis.synth.add(Implies(opt_cegis.var_insn_op(insn) == op_id, self.get_op_cost(insn, opt_cegis) == self.get_op_cost(insn - 1, opt_cegis) + operator_to_const[op]))
        
        # minimize the cost of the output instruction
        if self.max_cost is not None:
            opt_cegis.synth.add(self.get_op_cost(opt_cegis.out_insn, opt_cegis) < self.max_cost)
        else:     
            opt_cegis.synth.minimize(self.get_op_cost(opt_cegis.out_insn, opt_cegis))


# requires optimizer as solver
@dataclass(frozen=True)
class LengthOptimizer(SynthOptimizer):
    def get_length_cost(self, insn,  opt_cegis):
        return opt_cegis.get_var(BitVecSort(8, opt_cegis.ctx), f'insn_{insn}_depth')

    def add_constraint(self, opt_cegis):
        # optimization makes no sense without id instruction
        # id operator allows no-cost adding depth
        assert(opt_cegis.id is not None)
        # for all instructions, restrain max value to the number of instructions -> allows QF_FD to restrict integers
        for insn in range(opt_cegis.length):
            opt_cegis.synth.add(And([0 <= self.get_length_cost(insn, opt_cegis), self.get_length_cost(insn, opt_cegis) < opt_cegis.length]))

        # for input instructions, the length cost is 0
        for insn in range(opt_cegis.n_inputs):
            opt_cegis.synth.add(self.get_length_cost(insn, opt_cegis) == 0)

        # for all other instructions, the length cost is the length of the
        # previous instruction + 1, iff the operator is not id
        for insn in range(opt_cegis.n_inputs, opt_cegis.length):
            insn_length = self.get_length_cost(insn, opt_cegis)
            prev_insn = self.get_length_cost(insn - 1, opt_cegis)

            # get operator of instruction
            op_var = opt_cegis.var_insn_op(insn)
            # get the id operator
            id_id = opt_cegis.op_enum.item_to_cons[opt_cegis.id]

            # if the operator is id, The cost is the maximum, else it is the maximum of the operands + 1
            opt_cegis.synth.add(Implies(op_var == id_id, insn_length == prev_insn))
            opt_cegis.synth.add(Implies(op_var != id_id, insn_length == 1 + prev_insn))

        opt_cegis.synth.minimize(self.get_length_cost(opt_cegis.out_insn, opt_cegis))

@dataclass(frozen=True)
class TotalOperatorArityOptimization(SynthOptimizer): 
    max_arity: Optional[int] = None

    def get_cost_at_insn(self, insn, opt_cegis):
        return opt_cegis.get_var(BitVecSort(8, opt_cegis.ctx), f'insn_{insn}_cost')
    
    def add_constraint(self, opt_cegis):
        # for all instructions, restrain max value to the number of instructions times the maximal arity -> allows QF_FD to restrict integers
        for insn in range(opt_cegis.length):
            max_arity = max(op.arity for op in opt_cegis.ops)
            opt_cegis.synth.add(And([0 <= self.get_cost_at_insn(insn, opt_cegis), self.get_cost_at_insn(insn, opt_cegis) < opt_cegis.length * max_arity]))

        # for input instructions, the arity cost is 0
        for insn in range(opt_cegis.n_inputs):
            opt_cegis.synth.add(self.get_cost_at_insn(insn, opt_cegis) == 0)

        # for all other instructions, the arity cost is the arity cost of the
        # previous instruction + the arity of our operator
        for insn in range(opt_cegis.n_inputs, opt_cegis.length):
            insn_cost = self.get_cost_at_insn(insn, opt_cegis)
            prev_insn = self.get_cost_at_insn(insn - 1, opt_cegis)

            # get operator of instruction
            op_var = opt_cegis.var_insn_op(insn)

            for (op, op_id) in opt_cegis.op_enum.item_to_cons.items():
                opt_cegis.synth.add(Implies(op_var == op_id, insn_cost == prev_insn + op.arity))

        if self.max_arity is not None:
            opt_cegis.synth.add(self.get_cost_at_insn(opt_cegis.out_insn, opt_cegis) <= self.max_arity)
        else:
            opt_cegis.synth.minimize(self.get_cost_at_insn(opt_cegis.out_insn, opt_cegis))


OPTIMIZERS = DepthOptimization | OperatorUsageOptimization | OperatorHaveCostsOptimization | LengthOptimizer | TotalOperatorArityOptimization

@dataclass(frozen=True)
class HasOptimizer():
    optimizer: OPTIMIZERS = DepthOptimization()
    """Optimizer to use"""