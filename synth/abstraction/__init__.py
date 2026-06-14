from dataclasses import dataclass
from typing import Any, final

from z3 import *

from synth import util
from synth.cegis import cegis
from synth.solvers import Z3
from synth.spec import *
from synth.synth_n import LenCegis

class _ConstantSynth:
    """Interface for constant solvers"""

    def __init__(self, func: SynthFunc, base_program: Prg):
        self.prg       = base_program
        self.func      = func
        self.out_insn  = len(self.prg)

    @cache
    def get_const_var(self, ty, insn, opnd):
        return Const(f'|insn_{insn}_opnd_{opnd}_{ty}_const_val|', ty)

    def const_to_var(self, insn, opnd, ty, _):
        return self.get_const_var(ty, insn, opnd)

    def instantiate(self, instance_id, args, res):
        out_vars = [ Const(f'out_{i}_{instance_id}', ty)
                     for i, ty in enumerate(self.func.out_types) ]
        for c in self.prg.eval_clauses(args, out_vars, instance_id=instance_id,
                                       const_translate=self.const_to_var):
            res.append(c)
        return res, out_vars

    def create_prg(self, model):
        def lookup(insn, opnd, is_const, value):
            if is_const:
                if insn == self.out_insn:
                    ty = self.prg.sig.out_types[opnd]
                else:
                    (prod, _) = self.prg.insns[insn]
                    ty = prod.op.inputs[opnd].sort()
                var = self.get_const_var(ty, insn, opnd)
                return (True, model.evaluate(var, model_completion=True))
            else:
                return (False, value)

        insns = [
            (op, [ lookup(insn, opnd, is_const, value) for (opnd, (is_const, value)) in enumerate(args) ])
                for (insn, (op, args)) in enumerate(self.prg.insns)
        ]
        outputs = [
            lookup(self.out_insn, opnd, is_const, value)
                for (opnd, (is_const, value)) in enumerate(self.prg.outputs)
        ]
        return Prg(self.func, insns, outputs)

def _solve_constants(problem: Problem, base_prgs: dict[str, Prg],
                     solver: Solver = Z3(), d: util.Debug = util.Debug(), verbose: bool = False):
    synths = { name: _ConstantSynth(func, base_prgs[name]) for name, func in problem.funcs.items() }
    prgs, stats, _ = cegis(solver.create(problem.theory), problem.constraints, synths,
                           initial_samples=[], d=d, verbose=verbose)
    return prgs, stats

@dataclass(frozen=True)
class AbstractedProblem:
    original_problem: Problem
    abstract_problem: Problem
    abstract_to_concrete_production_map: dict[Production, Production]
    topped: dict[Production, set[ExprRef]]

    def verify_programs(self, abstract_prgs: dict[str, Prg]):
        def concretize_program(name: str, prg: Prg) -> Prg:
            insns = [ (self.abstract_to_concrete_production_map.get(op, op), args) for (op, args) in prg.insns ]
            return Prg(self.original_problem.funcs[name], insns, prg.outputs)

        concrete_prgs = { name: concretize_program(name, prg) for name, prg in abstract_prgs.items() }
        prgs, stats = _solve_constants(self.original_problem, concrete_prgs)
        return prgs

@dataclass(frozen=True)
class _AbstractConstraint(Constraint):
    abs: 'Abstraction'

    def verify(self, prgs: dict[str, Prg], d: Debug=no_debug, verbose=False):
        verif = Solver()
        outputs_differ = []
        for (name, ins), outs in self.function_applications.items():
            abs_ins  = [ self.abs.beta(i) for i in ins  ]
            abs_outs = [ self.abs.get_const_for(o) for o in outs ]
            verif.add(prgs[name].eval_term(abs_ins, abs_outs))
            outputs_differ += [ Not(self.abs.gamma(c, a)) for a, c in zip(abs_outs, outs) ]
        verif.add(self.phi)
        verif.add(Or(outputs_differ))
        stat = {}
        if verbose:
            d('verif_constr', f'(verif-assert {verif.sexpr()})')
            stat['verif_constraint'] = str(verif)
        with timer() as elapsed:
            res = verif.check()
            verif_time = elapsed()
        stat['verif_time'] = verif_time
        d('verif_time', f'(verif-time {verif_time / 1e9:.3f})')
        if res == sat:
            m = verif.model()
            counterexample = eval_model(m, self.params)
            if verbose:
                d('verif_model', f'(verif-model {m}')
                stat['verif_model'] = str(m)
            stat['counterexample'] = [ str(v) for v in counterexample ]
            return counterexample, stat
        else:
            # we found no counterexample, the program is therefore correct
            stat['counterexample'] = []
            return None, stat

    def add_instance_constraints(self, instance_id: str, synths: dict[str, Any], args: Sequence[ExprRef], res):
        param_subst = list(zip(self.params, args))
        out_subst = []
        tmp = []

        for k, ((name, ins), outs) in enumerate(self.function_applications.items()):
            id = f'{instance_id}_{k}'
            inst_args = [ simplify(self.abs.beta(substitute(i, param_subst))) for i in ins ]
            # print(inst_args)
            _, inst_outs = synths[name].instantiate(id, inst_args, tmp)
            new_outs = [ FreshConst(o.sort(), str(o)) for o in outs ]
            tmp += [ self.abs.gamma(c, a) for c, a in zip(new_outs, inst_outs) ]
            # tmp += [ self.abs.beta(c) == a for c, a in zip(new_outs, inst_outs) ]
            out_subst += list(zip(outs, new_outs))

        phi = substitute(self.phi, param_subst)
        phi = substitute(phi, out_subst)
        res.append(simplify(phi))
        for c in tmp:
            res.append(substitute(simplify(c), out_subst))
        return res

class Abstraction:
    def abstracts_from(self, s: SortRef) -> bool: ...
    def get_sort_for(self, s: SortRef) -> SortRef: ...
    def beta(self, concrete: ExprRef) -> ExprRef: ...
    def gamma(self, concrete: ExprRef, abstract: ExprRef) -> ExprRef: ...
    def abstract_func(self, f: Func, topped: set[ExprRef]) -> Func: ...

    @final
    def get_const_for(self, t: ExprRef, name: str = None):
        sort = self.get_sort_for(t.sort())
        return Const(name, sort) if name else FreshConst(sort)

    @final
    def check_beta_gamma_consistency(self, concrete_sort):
        s = Solver()
        c = FreshConst(concrete_sort)
        s.add(Not(self.gamma(c, self.beta(c))))
        return s.check() == unsat

    @final
    def check_transformer_sound(self, cf: Func) -> bool:
        af = self.abstract_func(cf, {})
        s  = Solver()
        s.add(cf.precond)
        for c, a in zip(cf.inputs, af.inputs):
            s.add(self.gamma(c, a))
        s.add(Not(self.gamma(cf.func, af.func)))
        return s.check() == unsat

    def abstract_const(self, k: ExprRef) -> ExprRef:
        s = Solver()
        c = self.get_const_for(k)
        s.add(c == self.beta(k))
        assert s.check() == sat
        val = s.model()[c]
        assert val is not None
        return val

    def is_pertinent(self, spec: Iterable[Constraint]) -> bool:
        s = Solver()
        all_params = set(x for c in spec for x in c.params)
        in_subst = [ (x, FreshConst(x.sort())) for x in all_params ]
        diff = []
        for c in spec:
            out_subst  = [ (a, FreshConst(a.sort())) for t in c.function_applications.values() for a in t  ]
            diff      += out_subst
            s.add(c.phi)
            s.add(substitute(c.phi, in_subst + out_subst))
        s.add(And(self.beta(a) == self.beta(b) for a, b in in_subst))
        s.add(Or(self.beta(a) != self.beta(b) for a, b in diff))
        return s.check() == unsat

    def get_abstract_problem(self, problem: Problem) -> AbstractedProblem:
        prod_map = {}
        new_funcs = {}
        topped = {}
        for name, func in problem.funcs.items():
            new_nts = {}
            for nt_name, nt in func.nonterminals.items():
                prods = ()
                for prod in nt.productions:
                    this_topped = set()
                    t_op = self.abstract_func(prod.op, this_topped)
                    if len(this_topped):
                        topped[prod] = this_topped
                    new_prod = Production(
                        op=t_op,
                        operands=prod.operands,
                        operand_is_nt=prod.operand_is_nt,
                        sexpr=prod.sexpr,
                        attributes=prod.attributes)
                    prods += (new_prod,)
                    prod_map[prod] = new_prod
                if nt.constants is not None:
                    new_consts = { self.abstract_const(k): v for k, v in nt.constants.items() }
                else:
                    new_consts = None
                new_nts[nt_name] = Nonterminal(
                    name=nt.name,
                    sort=self.get_sort_for(nt.sort),
                    parameters=nt.parameters,
                    productions=prods,
                    constants=new_consts)

            new_funcs[name] = SynthFunc(
                outputs=[ (o[0], self.get_sort_for(o[1])) for o in func.outputs ],
                inputs=[ (i[0], self.get_sort_for(i[1])) for i in func.inputs ],
                nonterminals=new_nts,
                result_nonterminals=func.result_nonterminals,
                weights=func.weights,
                max_const=func.max_const
            )

        new_problem = Problem(
            constraints=[ _AbstractConstraint(c.phi, c.params, c.function_applications, self) for c in problem.constraints ],
            funcs=new_funcs,
            theory='QF_BV'
        )

        return AbstractedProblem(
            original_problem=problem,
            abstract_problem=new_problem,
            abstract_to_concrete_production_map={v: k for k, v in prod_map.items()},
            topped=topped,
        )

@dataclass(frozen=True)
class Identity(Abstraction):
    def __str__(self):
        return 'concrete'

    def abstracts_from(self, s):
        return True

    def get_sort_for(self, s: SortRef) -> SortRef:
        return s

    def abstract_func(self, f: Func, topped: set[ExprRef]):
        return f

    def beta(self, concrete: ExprRef) -> ExprRef:
        return concrete

    def gamma(self, concrete: ExprRef, abstract: ExprRef) -> bool:
        return concrete == abstract

@dataclass(frozen=True)
class CannotAbstract(Exception):
    func: Func
    expr: ExprRef

@dataclass(frozen=True)
class AbstractLenCegis(LenCegis):
    abstractions: Iterable[Abstraction]
    max_spurious: int = 8

    def synth_prgs(self, problem: Problem) -> Tuple[Prg, dict[str, Any]]:
        iterations = []
        settings = dict(vars(self))
        settings['init_samples'] = 0
        del settings['abstractions']
        del settings['max_spurious']
        concrete_prgs = None
        lo, hi = self.size_range
        with util.timer() as elapsed:
            for abs in self.abstractions + [ Identity() ]:
                per_abstraction_stats = []
                iterations.append(per_abstraction_stats)
                self.debug('abs', f'(abstraction "{abs}")')
                if not abs.is_pertinent(problem.constraints):
                    self.debug('abs', f'(not-pertinent)')
                    continue
                try:
                    problems = abs.get_abstract_problem(problem)
                except CannotAbstract as e:
                    self.debug('abs', f'(cannot-abstract "{e.expr.sexpr()}")')
                    continue
                if len(problems.topped) > 0:
                    self.debug('abs', f'(topped)')
                    continue
                settings['size_range'] = (lo, hi)
                spurious = 0
                for prgs, stats in LenCegis(**settings).synth_all_prgs(problems.abstract_problem):
                    assert prgs is not None
                    per_abstraction_stats.append(stats)
                    concrete_prgs = problems.verify_programs(prgs)
                    if concrete_prgs is None:
                        s = ' '.join(p.sexpr(name) for name, p in prgs.items())
                        self.debug('abs', f'(spurious {s})')
                        spurious += 1
                        if spurious >= self.max_spurious:
                            self.debug('abs', f'(max-spurious {spurious})')
                            break
                    else:
                        return concrete_prgs, { 'time': elapsed(), 'iterations': iterations }

        return None, { 'time': elapsed(), 'iterations': iterations }