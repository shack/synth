from dataclasses import dataclass
from functools import cache, reduce

from synth.cegis import cegis

import synth.util as util
import synth.solvers as solvers

from synth.spec import Problem, SynthFunc, Production, Nonterminal, Prg

from z3 import *

class TreeConstraints:
    @dataclass(frozen=True)
    class Op:
        tc: TreeConstraints

        def arity(self):
            return 0

        def constr_prg(self, pos):
            return self.tc.var_pos_nt(pos) == self.valid_nt_mask()

    @dataclass(frozen=True)
    class HasNt(Op):
        nt: Nonterminal

        def valid_nt_mask(self):
            return self.tc.nt_mask(self.nt)

        def var_res(self, pos, instance):
            return self.tc.var_pos_res(self.nt.sort, pos, instance)

    @dataclass(frozen=True)
    class Nop(Op):
        def valid_nt_mask(self):
            return 0

        def constr_size(self, pos):
            return self.tc.var_pos_size(pos) == 0

        def constr_eval(self, pos, instance):
            return BoolVal(True)

    @dataclass(frozen=True)
    class Prod(HasNt):
        prod: Production

        def operands_nt(self):
            return (self.tc.non_terms[name]
                    for name, is_nt in zip(self.prod.operands,
                                           self.prod.operand_is_nt) if is_nt)

        def arity(self):
            return sum(self.prod.operand_is_nt)

        def constr_prg(self, pos):
            x = [ super().constr_prg(pos) ] \
              + [ (self.tc.var_pos_nt(pos + [idx]) & self.tc.nt_mask(nt)) != 0 for idx, nt in enumerate(self.operands_nt()) ]
            return And(x)

        def constr_size(self, pos):
            return self.tc.var_pos_size(pos) == sum(self.tc.var_pos_size(pos + [i]) for i, _ in enumerate(self.operands_nt())) + 1

        def constr_eval(self, pos, instance):
            # TODO: Params
            out_vars = [ self.var_res(pos, instance) ]
            in_vars  = []
            idx = 0
            for name, is_nt in zip(self.prod.operands, self.prod.operand_is_nt):
                if is_nt:
                    var = self.tc.var_pos_res(self.tc.non_terms[name].sort, pos + [ idx ], instance)
                    idx += 1
                else:
                    var = self.tc.var_in(name, instance)
                in_vars.append(var)
            precond, phi = self.prod.op.instantiate(out_vars, in_vars)
            return And(precond, phi)

    @dataclass(frozen=True)
    class Const(HasNt):
        nt: Nonterminal

        def var_const(self, pos):
            return self.tc.var_pos_const(self.nt.sort, pos)

        def constr_prg(self, pos):
            return And(super().constr_prg(pos), self.nt.const_val_constraint(self.var_const(pos)))

        def constr_size(self, pos):
            return self.tc.var_pos_size(pos) == 1

        def constr_eval(self, pos, instance):
            return self.var_res(pos, instance) == self.var_const(pos)

        def as_prg_opnd(self, pos, model):
            return (True, model.evaluate(self.var_const(pos), model_completion=True))

    @dataclass(frozen=True)
    class Param(Op):
        name: str
        sort: SortRef

        def valid_nt_mask(self):
            return self.tc.nt_mask(*(nt for nt in self.tc.non_terms.values() if self.name in nt.parameters))

        def constr_size(self, pos):
            return self.tc.var_pos_size(pos) == 0

        def constr_eval(self, pos, instance):
            return self.tc.var_pos_res(self.sort, pos, instance) == self.tc.var_in(self.name, instance)

        def as_prg_opnd(self, pos, model):
            inputs = list(self.tc.inputs.keys())
            return (False, inputs.index(self.name))

    def __init__(self, options, name: str, func: SynthFunc, n_op: int,
                 input_use: dict[str, int] = None):
        """Synthesize a program that computes the given functions.

        Attributes:
        options: Options to the synthesis.
        task: The synthesis task.
        n_op: Maximum number of operators in the tree.
        input_use: An optional dictionary to specify how much each input may be used.

        """
        self.name      = name
        self.func      = func
        self.options   = options
        self.n_nodes   = n_op
        self.input_use = input_use

        self.non_terms = self.func.nonterminals
        self.nt_idx    = { nt: i for i, nt in enumerate(self.non_terms.values()) }
        self.types     = set(nt.sort for nt in self.non_terms.values())

        self.input_ops = { name: TreeConstraints.Param(self, name, sort) for name, sort in self.func.inputs }

        self.ops = [ TreeConstraints.Nop(self) ] \
                 + [ p for p in self.input_ops.values() ] \
                 + [ TreeConstraints.Const(self, nt) for nt in self.non_terms.values() ] \
                 + [ TreeConstraints.Prod(self, nt, prod) for nt in self.non_terms.values() for prod in nt.productions ]

        assert len(self.ops) > 0, 'no operators to synthesize with'
        assert len(self.func.result_nonterminals) == 1, 'cannot synthesize multi-result functions'

        self.in_tys     = self.func.in_types
        self.out_nt     = self.func.result_nonterminals[0]
        self.out_ty     = self.non_terms[self.out_nt].sort
        self.inputs     = { name: sort for name, sort in self.func.inputs }
        self.n_inputs   = len(self.in_tys)
        self.max_arity  = max(op.arity() for op in self.ops)

        # TODO: This is an upper bound for now
        self.depth      = self.n_nodes + 1
        self.root_pos   = [ 0 ]

        # prepare operator enum sort
        self.op_enum = util.BitVecEnum('Operations', self.ops)
        # create map of types to their id
        self.nt_enum = util.BitVecEnum('Nonterminals', self.non_terms.keys())

        # get the sorts for the variables used in synthesis
        self.sz_sort = util.bv_sort(self.max_arity ** self.depth)
        self.nt_sort = self.nt_enum.sort
        self.op_sort = self.op_enum.sort

        # set options
        self.d = options.debug

    def nt_mask(self, *nts):
        return reduce(lambda acc, nt: acc | (1 << self.nt_idx[nt]), nts, 0)

    @cache
    def get_var(self, ty, name, instance=None):
        name = f'|{self.name}_{name}' + (f'_{instance}|' if instance is not None else '|')
        # name = f'|{prefix}_{instance}|' if not instance is None else f'|{prefix}|'
        return Const(name, ty)

    def get_var_pos(self, ty, name, pos, instance=None):
        return self.get_var(ty, '.'.join(str(p) for p in pos) + f'_{name}', instance)

    def var_pos_op(self, pos):
        return self.get_var_pos(self.op_sort, 'op', pos)

    def var_pos_nt(self, pos):
        return self.get_var_pos(BitVecSort(len(self.non_terms)), 'nt', pos)

    def var_pos_const(self, ty, pos):
        return self.get_var_pos(ty, 'const', pos)

    def var_pos_size(self, pos):
        return self.get_var_pos(self.sz_sort, 'size', pos)

    def var_pos_res(self, ty, pos, instance):
        return self.get_var_pos(ty, 'res', pos, instance)

    def var_in(self, name, instance):
        return self.get_var(self.inputs[name], f'in_{name}', instance)

    def var_out(self, instance):
        return self.var_pos_res(self.out_ty, self.root_pos, instance)

    def foreach_pos(self):
        def walk(pos, depth):
            if depth < self.depth:
                yield pos
                for i in range(self.max_arity):
                    yield from walk(pos + [i], depth + 1)
        yield from walk(self.root_pos, 0)

    def foreach_pos_and_op(self, res, f):
        for pos in self.foreach_pos():
            self.op_enum.add_ite(res, self.var_pos_op(pos), lambda op, _: f(pos, op))

    def op_var_list(self):
        m = { tuple(pos): self.var_pos_op(pos) for pos in self.foreach_pos() }
        return [ m[p] for p in sorted(m) ]

    def _add_constr_input_use(self, res):
        if not self.input_use:
            return res

        inp_var   = lambda pos, inp: self.get_var_pos(self.sz_sort, f'input_use_{inp}', pos)
        one       = BitVecVal(1, self.sz_sort)
        zero      = BitVecVal(0, self.sz_sort)

        for pos in self.foreach_pos():
            for name, op in self.input_ops.items():
                res.append(inp_var(pos, name) == self.op_enum.get_ite(op, self.var_pos_op(pos), one, zero))

        for inp, n in self.input_use.items():
            res.append(ULE(sum(inp_var(pos, inp) for pos in self.foreach_pos()), BitVecVal(n, self.sz_sort)))

        return res

    def add_program_constraints(self, res):
        f = lambda pos, op: And(op.constr_prg(pos),
                                op.constr_size(pos),
                                BoolVal(op.arity() == 0 or len(pos) < self.depth))
        # Add well-formedness constraints and size constraints
        self.foreach_pos_and_op(res, f)
        # Add operator bounds
        for pos in self.foreach_pos():
            self.op_enum.add_range_constr(self.var_pos_op(pos), res)
        # Add size bound
        res.append(ULE(self.var_pos_size(self.root_pos), self.n_nodes))
        # Set non-terminal of root
        root_nt = self.non_terms[self.func.result_nonterminals[0]]
        res.append((self.var_pos_nt(self.root_pos) & self.nt_mask(root_nt)) != 0)
        self._add_constr_input_use(res)
        return res

    def instantiate(self, instance, args, res):
        self.foreach_pos_and_op(res, lambda pos, op: op.constr_eval(pos, instance))
        inst_ins = [ self.var_in(name, instance) for name in self.inputs ]
        for var, val in zip(inst_ins, args):
            res.append(var == val)
        return res, [ self.var_out(instance) ]

    def create_prg(self, model):
        insns = []
        def place(pos):
            var   = self.var_pos_op(pos)
            idx   = model[var].as_long()
            op    = self.ops[idx]
            opnds = [ place(pos + [ i ]) for i in range(op.arity()) ]
            if len(opnds) > 0:
                pos = len(insns)
                insns.append((op.prod, opnds))
                return (False, self.n_inputs + pos)
            else:
                return op.as_prg_opnd(pos, model)
        out = place(self.root_pos)
        return Prg(self.func, insns, [ out ], weights={})

@dataclass(frozen=True)
class TreeCegis(util.HasDebug, solvers.HasSolver):
    max_size: int = 10
    verbose: bool = False

    def synth_prgs(self, problem: Problem):
        with util.timer() as elapsed:
            iterations = []
            for size in range(1, self.max_size):
                self.debug('len', f'(size {size})')
                solver = self.solver.create(problem.theory)
                constr = { name: TreeConstraints(self, name, f, size) \
                           for name, f in problem.funcs.items() }
                for c in constr.values():
                    c.add_program_constraints(solver)
                prgs, stats, _ = cegis(solver, problem.constraints,
                                 constr, [], self.debug, self.verbose)
                iterations.append(stats)
                if prgs is not None:
                    break
            return prgs, { 'time': elapsed(), 'iterations': iterations }

@dataclass(frozen=True)
class KBO(util.HasDebug):
    max_size: int = 10
    verbose: bool = False

    def synth_tree(self, problem: Problem, input_use: dict[str, int] = None):
        assert len(problem.funcs) == 1, "can only do single-function problems"
        with util.timer() as elapsed:
            iterations = []
            res = None
            for size in range(1, self.max_size):
                self.debug('len', f'(size {size})')
                solver = solvers.Z3Opt().create(problem.theory)
                solver.set(priority='lex')
                constr = { name: TreeConstraints(self, name, f, size, input_use) \
                           for name, f in problem.funcs.items() }
                for c in constr.values():
                    c.add_program_constraints(solver)
                    for v in c.op_var_list():
                        solver.minimize(v)
                prgs, stats, _ = cegis(solver, problem.constraints,
                                 constr, [], self.debug, self.verbose)
                iterations.append(stats)
                res = next(iter(prgs.values())) if prgs is not None else None
                if res is not None:
                    break
            return res, { 'time': elapsed(), 'iterations': iterations }
