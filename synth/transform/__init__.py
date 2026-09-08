"""Problem transformations.

A `ProblemTransform` rewrites a synthesis `Problem` into a related problem
over other sorts (e.g. narrower bit vectors, or bit vectors instead of
integers) while keeping the structure of the grammar: every production of the
original grammar has a counterpart in the transformed grammar (or is dropped
if it cannot be expressed), and a program found for the transformed problem
is lifted back to the original productions with `TransformedProblem.lift_prgs`.
The constants of a lifted program are only placeholders; they are meant to be
re-synthesized against the original problem (see `synth.const_synth`).

The transformation is a heuristic: nothing guarantees that a program of the
transformed problem generalises to the original one.

A concrete transform supplies `transform_sort`, `transform_value`,
`lift_value`, `transform_theory` and an operator table `OPS` mapping z3
operator kinds to constructors over the transformed sorts.  Expression
rewriting, the rebuild of functions, grammars and constraints, and lifting are
generic.
"""
from dataclasses import dataclass
from functools import reduce
from typing import Callable, ClassVar, Iterable
import operator

from z3 import *

from synth.spec import Constraint, Func, Nonterminal, Prg, Problem, Production, SynthFunc
from synth.util import no_debug


class CannotTransform(Exception):
    """An expression, production or constraint cannot be expressed in the
       transformed problem."""
    def __init__(self, what, reason: str):
        super().__init__(f'{reason}: {what}')
        self.what   = what
        self.reason = reason


# A handler rebuilds one application `e` from its already transformed
# children.  `ctx` gives access to the transform (`ctx.t`) and to the
# memoised recursion (`ctx.go`).
Handler = Callable[['_Rewrite', ExprRef, list[ExprRef]], ExprRef]

def apply_fn(f) -> Handler:
    """Handler that applies `f` to the transformed children."""
    return lambda ctx, e, cs: f(*cs)

def fold_fn(f) -> Handler:
    """Handler for n-ary operators: left fold of the binary `f`."""
    return lambda ctx, e, cs: reduce(f, cs)


class _Rewrite:
    """State of one `ProblemTransform.transform_expr` call."""

    def __init__(self, t: 'ProblemTransform', var_map: Iterable[tuple[ExprRef, ExprRef]]):
        self.t = t
        # keyed by AST id: ExprRef.__eq__ builds a term (and raises for
        # different sorts), so expressions must not be dictionary keys
        self.memo = { v.get_id(): w for v, w in var_map }

    def go(self, e: ExprRef) -> ExprRef:
        key = e.get_id()
        if (res := self.memo.get(key)) is not None:
            return res
        res    = self._rewrite(e)
        target = self.t.transform_sort(e.sort())
        if not res.sort().eq(target):
            raise CannotTransform(e, f'transformed to sort {res.sort()} instead of {target}')
        self.memo[key] = res
        return res

    def _rewrite(self, e: ExprRef) -> ExprRef:
        t = self.t
        if is_quantifier(e):
            raise CannotTransform(e, 'quantifier')
        if is_var(e):
            raise CannotTransform(e, 'bound variable')
        if is_const(e):
            if e.decl().kind() == Z3_OP_UNINTERPRETED:
                if t.changes_sort(e.sort()):
                    raise CannotTransform(e, 'unmapped variable')
                return e
            return t.transform_value(e)
        children = [ self.go(c) for c in e.children() ]
        if not t.changes_sort(e.sort()) and \
           all(not t.changes_sort(c.sort()) for c in e.children()):
            # no sort involved changes: the declaration can be reused; this
            # covers boolean connectives, uninterpreted functions and all
            # operators of untouched theories
            if all(c.eq(d) for c, d in zip(children, e.children())):
                return e
            return e.decl()(*children)
        handler = t.OPS.get(e.decl().kind())
        if handler is None:
            raise CannotTransform(e, f'unsupported operator {e.decl().name()}')
        return handler(self, e, children)


@dataclass(frozen=True)
class TransformedProblem:
    original: Problem
    transformed: Problem
    transform: 'ProblemTransform'

    production_map: dict[Production, Production]
    """Maps the productions of the transformed grammar to the original ones."""

    dropped: dict[str, tuple[tuple[Production, str], ...]]
    """Per function: the original productions that could not be transformed,
       with the reason."""

    def lift_prgs(self, prgs: dict[str, Prg]) -> dict[str, Prg]:
        """Programs over the original productions with the same shape as
           `prgs`.  Constants are placeholders (`ProblemTransform.lift_value`)
           of the original sorts; re-synthesize them with
           `synth.const_synth.solve_constants`."""
        res = {}
        for name, prg in prgs.items():
            sig   = self.original.funcs[name]
            insns = []
            for prod, args in prg.insns:
                # productions unknown to the map pass through, e.g. the nop
                # instruction that LenConstraints adds to multi-function problems
                orig = self.production_map.get(prod, prod)
                insns.append((orig, [
                    (True, self.transform.lift_value(v, orig.op.inputs[i].sort())) if is_const else (False, v)
                    for i, (is_const, v) in enumerate(args) ]))
            outputs = [
                (True, self.transform.lift_value(v, sig.out_types[i])) if is_const else (False, v)
                for i, (is_const, v) in enumerate(prg.outputs) ]
            res[name] = Prg(sig, insns, outputs, weights=prg.weights)
        return res


class ProblemTransform:
    """Base class of problem transformations.  Subclasses supply the hooks
       in the first section and extend `OPS`."""

    OPS: ClassVar[dict[int, Handler]] = {
        # sort-polymorphic operators
        Z3_OP_EQ:       apply_fn(operator.eq),
        Z3_OP_DISTINCT: lambda ctx, e, cs: Distinct(*cs),
        Z3_OP_ITE:      apply_fn(If),
        Z3_OP_AND:      lambda ctx, e, cs: And(*cs),
        Z3_OP_OR:       lambda ctx, e, cs: Or(*cs),
        Z3_OP_NOT:      apply_fn(Not),
        Z3_OP_IMPLIES:  apply_fn(Implies),
        Z3_OP_XOR:      apply_fn(Xor),
        Z3_OP_IFF:      apply_fn(operator.eq),
    }

    suffix: str = ''
    """Appended to the names of variables whose sort changes."""

    # --- hooks --------------------------------------------------------------

    def transform_sort(self, s: SortRef) -> SortRef:
        """The sort that `s` is mapped to (`s` itself if unchanged)."""
        raise NotImplementedError

    def transform_value(self, v: ExprRef) -> ExprRef:
        """Translate a literal.  The default keeps literals of unchanged sorts."""
        if self.changes_sort(v.sort()):
            raise CannotTransform(v, 'cannot transform value')
        return v

    def lift_value(self, v: ExprRef, sort: SortRef) -> ExprRef:
        """Placeholder of `sort` for the transformed literal `v`."""
        if not v.sort().eq(sort):
            raise CannotTransform(v, f'cannot lift value to sort {sort}')
        return v

    def transform_theory(self, theory: str | None) -> str | None:
        return theory

    # --- generic ------------------------------------------------------------

    def changes_sort(self, s: SortRef) -> bool:
        return not self.transform_sort(s).eq(s)

    def transform_var(self, v: ExprRef) -> ExprRef:
        """Variable of the transformed sort.  Deterministic (name based) so
           that the same variable in several constraints or functions maps to
           the same transformed variable, and the identity for variables
           whose sort does not change."""
        new_sort = self.transform_sort(v.sort())
        if new_sort.eq(v.sort()):
            return v
        return Const(f'{v.decl().name()}{self.suffix}', new_sort)

    def transform_expr(self, e: ExprRef, var_map: Iterable[tuple[ExprRef, ExprRef]] = ()) -> ExprRef:
        """Rewrite `e`; `var_map` gives the transformed variable for each
           free variable of `e` whose sort changes."""
        return _Rewrite(self, var_map).go(e)

    def transform_func(self, f: Func) -> Func:
        new_inputs = tuple(self.transform_var(v) for v in f.inputs)
        var_map    = list(zip(f.inputs, new_inputs))
        phi        = simplify(self.transform_expr(f.func, var_map))
        precond    = simplify(self.transform_expr(f.precond, var_map))
        # pass the inputs explicitly: deriving them from the free variables
        # would drop unused inputs and reorder them
        return Func(f.name, phi, precond=precond, inputs=new_inputs)

    def transform_production(self, p: Production) -> Production:
        return Production(op=self.transform_func(p.op),
                          operands=p.operands,
                          operand_is_nt=p.operand_is_nt,
                          sexpr=p.sexpr,
                          attributes=dict(p.attributes),
                          n_inlined_consts=p.n_inlined_consts)

    def transform_nonterminal(self, nt: Nonterminal, prod_map: dict, dropped: list, d) -> Nonterminal:
        prods = []
        for p in nt.productions:
            try:
                q = self.transform_production(p)
            except CannotTransform as ex:
                dropped.append((p, str(ex)))
                d('transform', f'(dropped "{p.sexpr}" "{ex}")')
                continue
            prods.append(q)
            prod_map[p] = q
        if nt.constants is None:
            consts = None
        else:
            # several constants may map to the same value; merge their bounds
            by_id = {}
            for c, w in nt.constants.items():
                try:
                    k = self.transform_value(c)
                except CannotTransform as ex:
                    d('transform', f'(dropped-constant "{c}" "{ex}")')
                    continue
                if (old := by_id.get(k.get_id())) is not None:
                    _, w0 = old
                    w = None if w is None or w0 is None else max(w, w0)
                by_id[k.get_id()] = (k, w)
            consts = { k: w for k, w in by_id.values() }
        return Nonterminal(name=nt.name,
                           sort=self.transform_sort(nt.sort),
                           parameters=nt.parameters,
                           productions=tuple(prods),
                           constants=consts)

    def transform_synth_func(self, name: str, f: SynthFunc, prod_map: dict, dropped: dict, d) -> SynthFunc:
        dropped_here = []
        nts = { nt_name: self.transform_nonterminal(nt, prod_map, dropped_here, d)
                for nt_name, nt in f.nonterminals.items() }
        if dropped_here:
            dropped[name] = tuple(dropped_here)
        had_prods = any(nt.productions for nt in f.nonterminals.values())
        if had_prods and not any(nt.productions for nt in nts.values()):
            raise CannotTransform(name, 'all productions dropped')
        return SynthFunc(outputs=[ (n, self.transform_sort(s)) for n, s in f.outputs ],
                         inputs=[ (n, self.transform_sort(s)) for n, s in f.inputs ],
                         nonterminals=nts,
                         result_nonterminals=f.result_nonterminals,
                         weights=f.weights,
                         max_const=f.max_const)

    def transform_constraint(self, c: Constraint) -> Constraint:
        params  = tuple(self.transform_var(p) for p in c.params)
        var_map = list(zip(c.params, params))
        # output variables first: applications may be nested (f(g(x))), so
        # the inputs of one application can refer to the outputs of another
        new_outs = [ tuple(self.transform_var(o) for o in outs)
                     for outs in c.function_applications.values() ]
        for outs, new in zip(c.function_applications.values(), new_outs):
            var_map += zip(outs, new)
        appls = {}
        for ((name, ins), _), new in zip(c.function_applications.items(), new_outs):
            appls[(name, tuple(self.transform_expr(i, var_map) for i in ins))] = new
        return Constraint(phi=self.transform_expr(c.phi, var_map),
                          params=params,
                          function_applications=appls)

    def is_pertinent(self, problem: Problem) -> bool:
        """True iff the transformation changes any sort of the problem."""
        for f in problem.funcs.values():
            if any(self.changes_sort(s) for _, s in f.inputs + f.outputs):
                return True
            if any(self.changes_sort(nt.sort) for nt in f.nonterminals.values()):
                return True
        for c in problem.constraints:
            if any(self.changes_sort(p.sort()) for p in c.params):
                return True
        return False

    def transform_problem(self, problem: Problem, d=no_debug) -> TransformedProblem:
        """Transform `problem`.  Productions that cannot be transformed are
           dropped (see `TransformedProblem.dropped`); a constraint that
           cannot be transformed raises `CannotTransform`."""
        prod_map = {}
        dropped  = {}
        funcs = { name: self.transform_synth_func(name, f, prod_map, dropped, d)
                  for name, f in problem.funcs.items() }
        constraints = []
        for c in problem.constraints:
            nc = self.transform_constraint(c)
            try:
                nc.check_signatures(funcs)
            except AssertionError as ex:
                raise CannotTransform(c, f'signature mismatch after transformation ({ex})')
            constraints.append(nc)
        transformed = Problem(constraints=constraints,
                              funcs=funcs,
                              theory=self.transform_theory(problem.theory),
                              name=problem.name)
        return TransformedProblem(original=problem,
                                  transformed=transformed,
                                  transform=self,
                                  production_map={ q: p for p, q in prod_map.items() },
                                  dropped=dropped)
