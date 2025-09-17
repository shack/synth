from z3 import *
from dataclasses import dataclass, field
from typing import Dict, Optional
from math import log2
from synth.util import bv_sort

class SynthOptimizer():
    """Base class for all optimizers"""
    def add_constraint(self, opt_cegis):
        pass

@dataclass(frozen=True)
class Depth(SynthOptimizer):
    max_depth: Optional[int] = None

    # number of bits to represent the length
    def get_bv_ln(self, opt_cegis):
        x = int(log2(opt_cegis.length)) + 1
        # print(x)
        # always unsolvable with calculated length - 8 bits should be fine for now (< 256 instructions are synthesized anyway)
        return x + 1

    # get depth cost variable for an instruction
    def get_depth_cost(self, insn,  opt_cegis):
        return opt_cegis.get_var(BitVecSort(self.get_bv_ln(opt_cegis)), f'insn_{insn}_depth')

    def get_operand_cost(self, insn, opnd,  opt_cegis):
        return opt_cegis.get_var(BitVecSort(self.get_bv_ln(opt_cegis)), f'insn_{insn}_opnd_{opnd}_cost')

    def add_constraint(self, opt_cegis):
        solver = opt_cegis.solver
        # for all instructions, restrain max value to the number of instructions -> allows QF_FD to restrict integers
        for insn in range(opt_cegis.length):
            solver.add(And([0 <= self.get_depth_cost(insn, opt_cegis), self.get_depth_cost(insn, opt_cegis) < opt_cegis.length]))

        # for input instructions, the depth cost is 0
        for insn in range(opt_cegis.n_inputs):
            solver.add(self.get_depth_cost(insn, opt_cegis) == 0)

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
                    solver.add(Implies(opnd == p_insn, self.get_operand_cost(insn, opndn, opt_cegis) == self.get_depth_cost(p_insn, opt_cegis)))

            op_depths = [ If(c, 0, self.get_operand_cost(insn, opnd, opt_cegis)) for opnd, c in zip(range(opt_cegis.arities[insn]), opt_cegis.var_insn_opnds_is_const(insn)) ]

            # id operator allows no-cost adding depth
            if insn < opt_cegis.out_insn and (id := opt_cegis._get_id_insn()):
                # get operator of instruction
                op_var = opt_cegis.var_insn_op(insn)
                # get the id operator
                id_id = opt_cegis.op_enum.item_to_cons[id]
                # if the operator is id, The cost is the maximum, else it is the maximum of the operands + 1
                solver.add(Implies(op_var == id_id, insn_depth == Max(op_depths)))
                solver.add(Implies(op_var != id_id, insn_depth == 1 + Max(op_depths)))
            else:
                solver.add(insn_depth == 1 + Max(op_depths))

        return self.get_depth_cost(opt_cegis.out_insn, opt_cegis)

@dataclass(frozen=True)
class OperatorUsage(SynthOptimizer):
    max_op_num: Optional[int] = None

    # get depth cost variable for an instruction
    def get_operator_used(self, op,  opt_cegis):
        return opt_cegis.get_var(BitVecSort(8), f'op_{op}_used')

    def add_constraint(self, opt_cegis):
        solver = opt_cegis.solver
        for _, op_id in opt_cegis.op_enum.item_to_cons.items():
            # whether the operator is used in any instruction
            used = Or([ op_id == opt_cegis.var_insn_op(insn) for insn in range(opt_cegis.n_inputs, opt_cegis.out_insn) ])

            # opt_cegis.synth.add(And([Implies(used, self.get_operator_used(op_id, opt_cegis) == BitVecVal(1, 8, opt_cegis.ctx)), Implies(Not(used), self.get_operator_used(op_id, opt_cegis) == BitVecVal(0, 8, opt_cegis.ctx))]))
            #opt_cegis.synth.add(And([Implies(used, self.get_operator_used(op_id, opt_cegis) == 1), Implies(Not(used), self.get_operator_used(op_id, opt_cegis) == 0)]))# If(used, 1, 0))
            solver.add(self.get_operator_used(op_id, opt_cegis) == If(used, BitVecVal(1, 8), BitVecVal(0, 8)))

        # calculate sum of used operators
        sum = BitVec('op_usage_sum', 8)

        def sum_bv(operands):
            if len(operands) == 0:
                return 0
            m = operands[0]
            for o in operands[1:]:
                m = m + o
            return m

        solver.add(sum == sum_bv([ self.get_operator_used(op_id, opt_cegis) for _, op_id in opt_cegis.op_enum.item_to_cons.items() ]))

        return sum

@dataclass(frozen=True)
class OperatorCosts(SynthOptimizer):
    op_to_cost: Dict[str, int]
    max_cost: Optional[int] = None

    def get_op_cost(self, insn, opt_cegis):
        return opt_cegis.get_var(BitVecSort(8), f'insn_{insn}_cost')

    def add_constraint(self, opt_cegis):
        name_to_operators = { str(op): op for op in opt_cegis.ops }
        operator_to_cost = { op: 1 for op in opt_cegis.ops }
        if id_op := opt_cegis._get_id_insn():
            operator_to_cost[id_op] = 0
        for name, cost in self.op_to_cost.items():
            if name in name_to_operators:
                operator_to_cost[name_to_operators[name]] = cost
        solver = opt_cegis.solver

        # set carried cost to 0 for first operator
        last_insn = opt_cegis.n_inputs - 1
        solver.add(self.get_op_cost(last_insn, opt_cegis) == 0)
        # For each instruction, set next operator cost based on the previous operator cost
        for insn in range(opt_cegis.n_inputs, opt_cegis.out_insn):
            for op, op_id in opt_cegis.op_enum.item_to_cons.items():
                # add cost for the operator
                solver.add(Implies(opt_cegis.var_insn_op(insn) == op_id, self.get_op_cost(insn, opt_cegis) == self.get_op_cost(insn - 1, opt_cegis) + operator_to_cost[op]))
                last_insn = insn

        return self.get_op_cost(last_insn, opt_cegis)

@dataclass(frozen=True)
class Length(SynthOptimizer):
    def get_length_cost(self, insn,  opt_cegis):
        return opt_cegis.get_var(BitVecSort(8), f'insn_{insn}_depth')

    def add_constraint(self, opt_cegis):
        solver = opt_cegis.solver
        if opt_cegis.n_inputs == 0:
            # nothing to optimize for constant programs
            return
        # optimization makes no sense without id instruction
        # id operator allows no-cost adding depth
        assert(opt_cegis._get_id_insn())
        # for all instructions, restrain max value to the number of instructions -> allows QF_FD to restrict integers
        for insn in range(opt_cegis.length):
            solver.add(And([0 <= self.get_length_cost(insn, opt_cegis), self.get_length_cost(insn, opt_cegis) < opt_cegis.length]))

        # for input instructions, the length cost is 0
        for insn in range(opt_cegis.n_inputs):
            solver.add(self.get_length_cost(insn, opt_cegis) == 0)

        # for all other instructions, the length cost is the length of the
        # previous instruction + 1, iff the operator is not id
        for insn in range(opt_cegis.n_inputs, opt_cegis.length):
            insn_length = self.get_length_cost(insn, opt_cegis)
            prev_insn = self.get_length_cost(insn - 1, opt_cegis)
            assert insn >= 1

            # get operator of instruction
            op_var = opt_cegis.var_insn_op(insn)
            # get the id operator
            id_id = opt_cegis.op_enum.item_to_cons[opt_cegis.id]

            # if the operator is id, The cost is the maximum, else it is the maximum of the operands + 1
            solver.add(Implies(op_var == id_id, insn_length == prev_insn))
            solver.add(Implies(op_var != id_id, insn_length == 1 + prev_insn))

        return self.get_length_cost(opt_cegis.out_insn, opt_cegis)

@dataclass(frozen=True)
class TotalOperatorArity(SynthOptimizer):
    max_arity: Optional[int] = None

    def get_cost_at_insn(self, insn, opt_cegis):
        return opt_cegis.get_var(BitVecSort(8), f'insn_{insn}_cost')

    def add_constraint(self, opt_cegis):
        solver = opt_cegis.solver
        # for all instructions, restrain max value to the number of instructions times the maximal arity -> allows QF_FD to restrict integers
        for insn in range(opt_cegis.length):
            max_arity = max(op.arity for op in opt_cegis.ops)
            solver.add(And([0 <= self.get_cost_at_insn(insn, opt_cegis), self.get_cost_at_insn(insn, opt_cegis) < opt_cegis.length * max_arity]))

        # for input instructions, the arity cost is 0
        for insn in range(opt_cegis.n_inputs):
            solver.add(self.get_cost_at_insn(insn, opt_cegis) == 0)

        # for all other instructions, the arity cost is the arity cost of the
        # previous instruction + the arity of our operator
        for insn in range(opt_cegis.n_inputs, opt_cegis.length):
            insn_cost = self.get_cost_at_insn(insn, opt_cegis)
            prev_insn = self.get_cost_at_insn(insn - 1, opt_cegis)

            # get operator of instruction
            op_var = opt_cegis.var_insn_op(insn)

            for (op, op_id) in opt_cegis.op_enum.item_to_cons.items():
                solver.add(Implies(op_var == op_id, insn_cost == prev_insn + op.arity))

        return self.get_cost_at_insn(opt_cegis.out_insn, opt_cegis)

@dataclass(frozen=True)
class Chips(SynthOptimizer):
    number_of_gates = {
        'not1': 6,

        'nand2': 4,
        'nor2': 4,
        'and2': 4,
        'or2': 4,
        'xor2': 4,

        'and3': 3,
        'or3': 3,
        'nand3': 3,
        'nor3': 3,
        'and3': 3,

        'nand4': 2,
        'and4': 2,
        'nor4': 2,
    }

    def add_constraint(self, opt_cegis):
        assert(opt_cegis.id is not None)
        bv   = bv_sort(len(opt_cegis.ops) * opt_cegis.n_insns)
        zero = BitVecVal(0, bv)
        one  = BitVecVal(1, bv)

        # For each instruction, set next operator cost based on the previous operator cost
        total = zero
        for op, op_id in opt_cegis.op_enum.item_to_cons.items():
            if str(op) in self.number_of_gates:
                op_cost = zero
                for insn in range(opt_cegis.n_inputs, opt_cegis.length):
                    op_cost += If(opt_cegis.var_insn_op(insn) == op_id, one, zero)
                units_per_chip = self.number_of_gates[str(op)]
                total += UDiv(op_cost + units_per_chip - 1, units_per_chip)

        length = zero
        id_id = opt_cegis.op_enum.item_to_cons[opt_cegis.id]
        for insn in range(opt_cegis.n_inputs, opt_cegis.length):
            length += If(opt_cegis.var_insn_op(insn) == id_id, zero, one)

        return total

OPTIMIZERS = Depth | OperatorUsage | OperatorCosts | Length | TotalOperatorArity | Chips

@dataclass(frozen=True)
class HasOptimizer():
    optimizer: OPTIMIZERS
    """Optimizer to use"""