from z3 import *
from typing import Union
from dataclasses import dataclass, field

import enum

from synth.spec import Problem, SynthFunc
from synth.cegis import cegis
from synth.synth_n import LenConstraints, _LenCegisBase, _LenCegisSession
from synth import solvers, util

class ObjectiveConstraints(LenConstraints):
    def __init__(self, obj_options, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.obj_options = obj_options

@dataclass(frozen=True)
class Depth:
    def create_constraints(self, *args, **kwargs):
        return DepthConstraints(None, *args, **kwargs)

class DepthConstraints(ObjectiveConstraints):

    # get depth cost variable for an instruction
    def get_depth_cost(self, insn):
        return self.get_var(util.bv_sort(self.length), f'insn_{insn}_depth')

    def get_operand_cost(self, insn, opnd):
        return self.get_var(util.bv_sort(self.length), f'insn_{insn}_opnd_{opnd}_cost')

    def get_objective(self):
        return self.get_depth_cost(self.out_insn)

    def add_program_constraints(self, solver):
        solver = super().add_program_constraints(solver)

        # for all instructions, restrain max value to the number of instructions -> allows QF_FD to restrict integers
        for insn in range(self.length):
            solver.add(ULE(0, self.get_depth_cost(insn)))
            solver.add(ULT(self.get_depth_cost(insn), self.length))

        # for input instructions, the depth cost is 0
        for insn in range(self.n_inputs):
            solver.add(self.get_depth_cost(insn) == 0)

        def Max(operands):
            if len(operands) == 0:
                return 0
            m = operands[0]
            for o in operands[1:]:
                m = If(o > m, o, m)
            return m

        # for all other instructions, the depth cost is the maximum of the
        # depth costs of the operands plus 1
        for insn in range(self.n_inputs, self.length):
            insn_depth = self.get_depth_cost(insn)

            # depth cost can only be influenced by previous instructions
            for p_insn in range(insn):
                for opndn, opnd in zip(range(self.arities[insn]), self.var_insn_opnds(insn)):
                    solver.add(Implies(opnd == p_insn, self.get_operand_cost(insn, opndn) == self.get_depth_cost(p_insn)))

            op_depths = [ If(c, 0, self.get_operand_cost(insn, opnd)) for opnd, c in zip(range(self.arities[insn]), self.var_insn_opnds_is_const(insn)) ]
            max = Max(op_depths)
            solver.add(insn_depth == If(self.constr_is_nop(insn), max, max + 1))

        return solver

@dataclass(frozen=True)
class OperatorUsage:
    def create_constraints(self, *args, **kwargs):
        return OperatorUsageConstraints(None, *args, **kwargs)

class OperatorUsageConstraints(ObjectiveConstraints):

    # get depth cost variable for an instruction
    def get_operator_used(self, op):
        return self.get_var(BitVecSort(8), f'op_{op}_used')

    def get_objective(self):
        return BitVec('op_usage_sum', 8)

    def add_program_constraints(self, solver):
        solver = super().add_program_constraints(solver)
        for _, op_id in self.op_enum.item_to_cons.items():
            # whether the operator is used in any instruction
            used = Or([ op_id == self.var_insn_op(insn) for insn in range(self.n_inputs, self.out_insn) ])
            solver.add(self.get_operator_used(op_id) == If(used, BitVecVal(1, 8), BitVecVal(0, 8)))

        solver.add(self.get_objective() == sum(self.get_operator_used(op_id) for _, op_id in self.op_enum.item_to_cons.items()))
        return solver

@dataclass(frozen=True)
class OperatorCosts:
    op_to_cost: dict[str, int]

    def create_constraints(self, *args, **kwargs):
        return OperatorCostsConstraints(self.op_to_cost, *args, **kwargs)

class OperatorCostsConstraints(ObjectiveConstraints):

    def get_op_cost(self, insn):
        return self.get_var(BitVecSort(8), f'insn_{insn}_cost')

    def get_objective(self):
        return self.get_op_cost(self.out_insn)

    def add_program_constraints(self, solver):
        solver = super().add_program_constraints(solver)
        name_to_operators = { str(op): op for op in self.ops }
        operator_to_cost = { op: 1 for op in self.ops }
        if id_op := self._get_id_insn():
            operator_to_cost[id_op] = 0
        for name, cost in self.op_to_cost.items():
            if name in name_to_operators:
                operator_to_cost[name_to_operators[name]] = cost
        solver = self.solver

        # set carried cost to 0 for first operator
        last_insn = self.n_inputs - 1
        solver.add(self.get_op_cost(last_insn, self) == 0)
        # For each instruction, set next operator cost based on the previous operator cost
        for insn in range(self.n_inputs, self.out_insn):
            for op, op_id in self.op_enum.item_to_cons.items():
                # add cost for the operator
                solver.add(Implies(self.var_insn_op(insn) == op_id, self.get_op_cost(insn, self) == self.get_op_cost(insn - 1, self) + operator_to_cost[op]))
                last_insn = insn
        return solver

@dataclass(frozen=True)
class TotalOperatorArity:
    def create_constraints(self, *args, **kwargs):
        return TotalOperatorArityConstraints(None, *args, **kwargs)

class TotalOperatorArityConstraints(ObjectiveConstraints):
    def get_cost_at_insn(self, insn):
        return self.get_var(BitVecSort(8), f'insn_{insn}_cost')

    def get_objective(self):
        return self.get_cost_at_insn(self.out_insn)

    def add_program_constraints(self, solver):
        solver = super().add_program_constraints(solver)
        # for all instructions, restrain max value to the number of instructions times the maximal arity -> allows QF_FD to restrict integers
        max_arity = max(op.arity for op in self.ops)
        for insn in range(self.length):
            solver.add(And([0 <= self.get_cost_at_insn(insn, self), self.get_cost_at_insn(insn, self) < self.length * max_arity]))

        # for input instructions, the arity cost is 0
        for insn in range(self.n_inputs):
            solver.add(self.get_cost_at_insn(insn, self) == 0)

        # for all other instructions, the arity cost is the arity cost of the
        # previous instruction + the arity of our operator
        for insn in range(self.n_inputs, self.length):
            insn_cost = self.get_cost_at_insn(insn, self)
            prev_insn = self.get_cost_at_insn(insn - 1, self)

            # get operator of instruction
            op_var = self.var_insn_op(insn)

            for (op, op_id) in self.op_enum.item_to_cons.items():
                solver.add(Implies(op_var == op_id, insn_cost == prev_insn + op.arity))

        return solver

@dataclass(frozen=True)
class Chips:
    def create_constraints(self, *args, **kwargs):
        return ChipsConstraints(None, *args, **kwargs)

class ChipsConstraints(ObjectiveConstraints):
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

    def get_objective(self):
        return BitVec('chip_count', 8)

    def add_program_constraints(self, solver):
        solver = super().add_program_constraints(solver)
        bv   = util.bv_sort(len(self.ops) * self.n_insns)
        zero = BitVecVal(0, bv)
        one  = BitVecVal(1, bv)

        # For each instruction, set next operator cost based on the previous operator cost
        total = zero
        for op, op_id in self.op_enum.item_to_cons.items():
            if str(op) in ChipsConstraints.number_of_gates:
                op_cost = zero
                for insn in range(self.n_inputs, self.length):
                    op_cost += If(self.var_insn_op(insn) == op_id, one, zero)
                units_per_chip = ChipsConstraints.number_of_gates[str(op)]
                total += UDiv(op_cost + units_per_chip - 1, units_per_chip)
        solver.add(self.get_objective() == total)
        return solver

OBJECTIVES = Depth \
           | OperatorCosts \
           | OperatorUsage \
           | TotalOperatorArity \
           | Chips

@dataclass(frozen=True)
class HasObjective:
    obj: OBJECTIVES = field(kw_only=True, default_factory=Depth)
    """Optimization objective."""

class MultiObjectivePriority(enum.Enum):
    LEX = enum.auto()
    PARETO = enum.auto()

class MultiObjective(enum.Enum):
    OBJ_ONLY = enum.auto()
    LEN_FST = enum.auto()
    LEN_SND = enum.auto()

@dataclass(frozen=True, kw_only=True)
class _OptCegis(_LenCegisBase, HasObjective):
    """Cegis synthesizer that finds the optimal program for a given metric."""

    order: MultiObjective = MultiObjective.OBJ_ONLY
    """Order of multi-objective optimization."""

    priority: MultiObjectivePriority = MultiObjectivePriority.LEX
    """Priority for multi-objective optimization."""

    def create_constr(self, name: str, f: SynthFunc, max_len: int, use_nop: bool):
        return self.obj.create_constraints(self, name, f, max_len, use_nop=use_nop)

@dataclass(frozen=True)
class OptSolver(_OptCegis):
    def synth_prgs(self, problem: Problem):
        _, hi  = self.get_range(problem)
        solver = solvers.Z3Opt().create(problem.theory)
        constr = { name: self.create_constr(name, f, hi, use_nop=True) for name, f in problem.funcs.items() }

        for s in constr.values():
            s.add_program_constraints(solver)

        length = sum(s.length_var for s in constr.values())
        goal   = sum(s.get_objective() for s in constr.values())
        match self.order:
            case MultiObjective.LEN_FST:
                solver.minimize(length)
                solver.minimize(goal)
                solver.set(priority=self.priority.name.lower())
            case MultiObjective.LEN_SND:
                solver.minimize(goal)
                solver.minimize(length)
                solver.set(priority=self.priority.name.lower())
            case MultiObjective.OBJ_ONLY:
                solver.minimize(goal)

        syn_constr = problem.constraint
        samples = syn_constr.counterexample_eval.sample_n(self.init_samples)
        prg, stats, _ = cegis(solver, syn_constr,
                              constr, samples,
                              self.debug, self.detailed_stats)
        return prg, stats

class _OptSearchSession(_LenCegisSession):
    def create_constr(self, name: str, f: SynthFunc, n_insns: int):
        return self.options.create_constr(name, f, n_insns, use_nop=(len(self.problem.funcs) > 1))

@dataclass(frozen=True)
class OptSearch(_OptCegis):
    start_search: int | None = 10
    """Starting point for binary search."""

    solver: solvers.SOLVERS = field(default_factory=solvers.Z3)
    """Solver to use for synthesis."""

    def create_session(self, problem, max_len):
        return _OptSearchSession(self, problem, self.solver, max_len)

    def _search_obj(self, problem: Problem):
        def eval(m):
            def add_constraints(constr, _):
                yield sum(s.get_objective() for s in constr.values()) < m
            prgs, stats = super(_OptCegis, self).synth_prgs(problem, add_constraints=add_constraints)
            return prgs, stats
        def is_lt(res):
            return res[0] is not None

        with util.timer() as elapsed:
            lower, upper = util.find_start_interval(eval, is_lt, start=self.start_search, debug=self.debug)
            val, results = util.binary_search(eval, is_lt, lower, upper, debug=self.debug)
            def add_constraints(constr, _):
                yield sum(s.get_objective() for s in constr.values()) == val
            prgs, stats = super().synth_prgs(problem, add_constraints=add_constraints)
            assert prgs is not None
            time = elapsed()
        return val, prgs, {
            'time': time,
            'iterations': results,
            'final': stats
        }

    def synth_prgs(self, problem: Problem):
        match self.order:
            case MultiObjective.LEN_FST:
                # Find the shortest program first
                with util.timer() as elapsed:
                    prgs, initial_stats = super().synth_prgs(problem)
                    start_time = elapsed()
                # if there is none, exit
                if prgs is None:
                    return None, {
                        'time': start_time,
                        'success': False,
                        'iterations': [],
                        'init_stats': initial_stats,
                    }
                else:
                    # now, find the best program according to the other objective
                    val, prgs, stats = self._search_obj(problem)
                    return prgs, {
                        'objective_value': val,
                        'success': True,
                        'time': stats['time'],
                        'init_stats': initial_stats,
                        'obj_stats': stats,
                    }

            case MultiObjective.LEN_SND | MultiObjective.OBJ_ONLY:
                with util.timer() as elapsed:
                    val, prgs, obj_stats = self._search_obj(problem)
                    self.debug('opt', f'found program with optimal objective {val}: {prgs}')
                    if prgs is None:
                        return None, {
                            'time': elapsed(),
                            'success': False,
                            'obj_stats': obj_stats,
                        }
                    else:
                        def add_constraints(constr, _):
                            yield sum(c.get_objective() for c in constr.values()) == val
                        prgs, stats = super().synth_prgs(problem, add_constraints=add_constraints)
                        return prgs, {
                            'time': elapsed(),
                            'success': not prgs is None,
                            'objective_value': val,
                            'obj_stats': obj_stats,
                            'len_stats': stats,
                        }