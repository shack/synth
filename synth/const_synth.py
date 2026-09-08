"""Re-synthesis of the constants of programs with a fixed shape.

The instructions, their operand wiring and the output selection of a program
are kept; every constant operand (of an instruction or of an output) becomes a
free variable of the sort the production expects, and the literal stored in
the program is ignored.  The literal may even have another sort, e.g. a
narrower bit vector after downscaling.  The values are found by CEGIS against
the constraints of a problem.

`max_const` needs no re-check here: the number of constant slots (and the
`n_inlined_consts` of the productions) is that of the given program, which was
synthesized under the same bound.

Used by `synth.abstraction` (concretising abstract programs) and
`synth.transform` (lifting programs found on a transformed problem).
"""
from typing import Any

from z3 import *

from synth import util
from synth.cegis import cegis
from synth.solvers import SOLVERS, Z3
from synth.spec import Nonterminal, Prg, Problem, SynthFunc


class ConstantSynth:
    """Constant synthesizer for one function with a fixed program shape.

    Duck-types the `synths` protocol of `synth.cegis.cegis`:
    `instantiate(instance_id, args, res)` and `create_prg(model)`.
    """

    def __init__(self, name: str, func: SynthFunc, base_prg: Prg):
        self.name     = name
        self.func     = func
        self.prg      = base_prg
        # constant outputs are reported by Prg.eval_clauses with this instruction index
        self.out_insn = len(base_prg)
        # (insn, opnd) -> solver variable, one per constant slot of the program
        self.vars: dict[tuple[int, int], ExprRef] = {}
        for insn, (_, args) in enumerate(base_prg.insns):
            for opnd, (is_const, _) in enumerate(args):
                if is_const:
                    self._add_var(insn, opnd)
        for opnd, (is_const, _) in enumerate(base_prg.outputs):
            if is_const:
                self._add_var(self.out_insn, opnd)

    def _sort(self, insn: int, opnd: int) -> SortRef:
        if insn == self.out_insn:
            return self.func.out_types[opnd]
        prod, _ = self.prg.insns[insn]
        # operands are indexed by the argument position of the production's function
        return prod.op.inputs[opnd].sort()

    def _nonterminal(self, insn: int, opnd: int) -> Nonterminal | None:
        """The non-terminal that owns constant slot `opnd` of `insn`, or None
           for productions the grammar does not know (e.g. the nop instruction
           that `LenConstraints` adds for multi-function problems)."""
        if insn == self.out_insn:
            name = self.func.result_nonterminals[opnd]
        else:
            prod, _ = self.prg.insns[insn]
            name = prod.operands[opnd]
        return self.func.nonterminals.get(name)

    def _add_var(self, insn: int, opnd: int):
        # the function name makes the variable unique across the functions
        # of a problem (cf. LenConstraints.get_var)
        name = f'|{self.name}_insn_{insn}_opnd_{opnd}_const|'
        self.vars[(insn, opnd)] = Const(name, self._sort(insn, opnd))

    def const_var(self, insn: int, opnd: int) -> ExprRef:
        return self.vars[(insn, opnd)]

    def _const_translate(self, insn, opnd, ty, _value):
        return self.vars[(insn, opnd)]

    def const_set_constraints(self):
        """Constraints restricting each constant to the values its
           non-terminal allows (`Nonterminal.const_val_constraint`)."""
        for (insn, opnd), var in self.vars.items():
            nt = self._nonterminal(insn, opnd)
            if nt is not None and nt.constants is not None:
                yield nt.const_val_constraint(var)

    def instantiate(self, instance_id, args, res):
        out_vars = [ Const(f'{self.name}_out_{i}_{instance_id}', ty)
                     for i, ty in enumerate(self.func.out_types) ]
        for c in self.prg.eval_clauses(args, out_vars, instance_id=instance_id,
                                       const_translate=self._const_translate):
            res.append(c)
        return res, out_vars

    def create_prg(self, model) -> Prg:
        def lookup(insn, opnd, is_const, value):
            if is_const:
                return (True, model.evaluate(self.vars[(insn, opnd)], model_completion=True))
            return (False, value)
        insns = [ (prod, [ lookup(insn, opnd, c, v) for opnd, (c, v) in enumerate(args) ])
                  for insn, (prod, args) in enumerate(self.prg.insns) ]
        outputs = [ lookup(self.out_insn, opnd, c, v)
                    for opnd, (c, v) in enumerate(self.prg.outputs) ]
        return Prg(self.func, insns, outputs, weights=self.prg.weights)


def solve_constants(problem: Problem, base_prgs: dict[str, Prg],
                    solver: SOLVERS = Z3(), d: util.Debug = util.Debug(),
                    verbose: bool = False) -> tuple[dict[str, Prg] | None, dict[str, Any]]:
    """Find constants for the programs `base_prgs` (one per function of
       `problem`) such that they satisfy the constraints of `problem`.
       Returns the programs with the constants filled in (None if no such
       constants exist) and the statistics of the CEGIS loop."""
    synths = { name: ConstantSynth(name, func, base_prgs[name])
               for name, func in problem.funcs.items() }
    s = solver.create(problem.theory)
    for cs in synths.values():
        for c in cs.const_set_constraints():
            s.add(c)
    prgs, stats, _ = cegis(s, problem.constraints, synths, initial_samples=[],
                           d=d, verbose=verbose)
    return prgs, stats
