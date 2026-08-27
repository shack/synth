"""Check a solution against a SyGuS problem.

`check` decides for a solution (one define-fun per synth-fun, as returned by
`util.sygus.read_solution`) whether

1. the body of every define-fun is derivable from the grammar of its
   synth-fun, and
2. the solution satisfies all synthesis constraints of the problem.

Grammar membership is decided by matching the body (with all lets inlined)
top-down against the s-expression patterns of the productions
(`Production.sexpr`).  The placeholder of a non-terminal operand matches
every term the non-terminal derives; parameters (`Nonterminal.parameters`)
and constants (`Nonterminal.constants`) are the leaves.  A successful match
is a derivation, which is turned into a `Prg` over the productions of the
grammar.  The semantics of the solution is therefore the one that the
grammar assigns to it (`Production.op`), so functions defined in the problem
file need not be known here: the parser has already inlined them into the
productions.  Weights declared for a synth-fun get the value determined by
the derivation, computed like `LenConstraints._add_constr_weights` does.

The constraints are then verified with `Constraint.verify`.  The solution
term is interpreted with its SMT-LIB semantics: operator preconditions
(e.g. non-zero divisors), which the synthesizer uses to avoid partial
operations, are not part of the meaning of a solution.

If a function does not follow its grammar, the constraints are still checked
if its define-fun can be parsed without the grammar (using the SyGuS parser),
so that syntactic and semantic problems can be told apart.
"""

from collections import UserString
from contextlib import contextmanager
from dataclasses import dataclass, field, replace
from io import StringIO
from itertools import islice, product

import math
import re
import sys
import tinysexpr

from tinysexpr import SExpr
from z3 import *

from synth.spec import Constraint, Nonterminal, Problem, Production, Prg, SynthFunc
from synth.util import free_vars
from util.size import inline_let
from util.sygus import SyGuS, SyGuSError, get_sort, parse_literal

# --------------------------------------------------------------------------
# terms

# The body of a define-fun is represented as nested tuples of strings.

def _plain(s):
    """Turn an s-expression into nested tuples of plain strings."""
    if isinstance(s, (str, UserString)):
        return str(s)
    return tuple(_plain(c) for c in s)

def _strip_annotations(term):
    """Remove all annotations `(! t attr ...)` from a term."""
    if isinstance(term, str):
        return term
    if len(term) >= 2 and term[0] == '!':
        return _strip_annotations(term[1])
    return tuple(_strip_annotations(c) for c in term)

def _to_sexpr(term) -> str:
    if isinstance(term, str):
        return term
    return '(' + ' '.join(_to_sexpr(c) for c in term) + ')'

def _subterms(term):
    """All proper subterms of a term."""
    if not isinstance(term, str):
        for c in term:
            yield c
            yield from _subterms(c)

def _to_real(v):
    return v if is_real(v) else ToReal(v)

def _literal(term) -> ExprRef | None:
    """The value of `term` if it is a literal in one of the notations SMT-LIB
       uses for constants: numerals and decimals (`1`, `1.5`, and also
       `-1`), `(- 1)`, rationals `(/ 1 2)`, bit-vectors `#x1f`, `#b101` and
       `(_ bv5 8)`, and `true`/`false`.  None if it is no literal."""
    match term:
        case str(a):
            try:
                return parse_literal(a)
            except ValueError:
                return None
        case ('-', t):
            v = _literal(t)
            return simplify(-v) if v is not None and is_arith(v) else None
        case ('/', a, b):
            va, vb = _literal(a), _literal(b)
            if va is not None and vb is not None and is_arith(va) and is_arith(vb):
                return simplify(_to_real(va) / _to_real(vb))
            return None
        case ('_', str(bv), str(width)) if bv.startswith('bv') and bv[2:].isdigit() and width.isdigit():
            return BitVecVal(int(bv[2:]), int(width))
    return None

def _free_identifiers(term, bound: set[str]) -> set[str]:
    """The identifiers of a let-free term that are neither in `bound` nor
       literals.  Operators (the head of an application) do not count."""
    if _literal(term) is not None:
        return set()
    if isinstance(term, str):
        return set() if term in bound else { term }
    return set().union(*(_free_identifiers(c, bound) for c in term[1:]))

def _same_value(a: ExprRef, b: ExprRef) -> bool:
    """Compare two constants (Int and Real constants are compared by value)."""
    if a.sort() == b.sort() or (is_arith(a) and is_arith(b)):
        return is_true(simplify(a == b))
    return False

@contextmanager
def _deep_recursion(limit=20000):
    """Terms are processed recursively; allow for deeply nested solutions."""
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(max(old, limit))
    try:
        yield
    finally:
        sys.setrecursionlimit(old)

# --------------------------------------------------------------------------
# derivations

@dataclass(frozen=True)
class Derivation:
    """A derivation of a term from a non-terminal of a grammar.
       A leaf derives a parameter or a constant; an inner node applies a
       production to the derivations of its non-terminal operands."""

    nt: str
    """The non-terminal that derives the term."""

    leaf: str | ExprRef | None
    """The parameter name or the constant if this is a leaf."""

    prod: Production | None
    """The production applied if this is an inner node."""

    children: tuple['Derivation', ...]
    """The derivations of the non-terminal operands of the production."""

    weights: tuple[int, ...]
    """The accumulated weights of the derivation (one per declared weight
       of the synth-fun, in declaration order)."""

    def to_prg(self, fun: SynthFunc) -> Prg:
        """The program over the productions of `fun` that this derivation denotes."""
        param_idx = { name: i for i, (name, _) in enumerate(fun.inputs) }
        insns = []
        def build(d: Derivation):
            if d.prod is None:
                return (True, d.leaf) if isinstance(d.leaf, ExprRef) else (False, param_idx[d.leaf])
            opnds = d.prod.operand_vector([ build(c) for c in d.children ],
                                          lambda param: (False, param_idx[param]))
            insns.append((d.prod, opnds))
            return (False, len(param_idx) + len(insns) - 1)
        out = build(self)
        weights = { var: IntVal(w) for (_, var), w in zip(fun.weights.values(), self.weights) }
        return Prg(fun, insns, [ out ], weights=weights)

_PLACEHOLDER = re.compile(r'\{(\d+)\}')

class _Grammar:
    """Decides which terms the non-terminals of a synth-fun derive."""

    def __init__(self, fun: SynthFunc):
        self.fun = fun
        self.nts = fun.nonterminals
        self.zero = (0,) * len(fun.weights)
        # (non-terminal, term) -> derivations indexed by their weights
        self.memo: dict[tuple[str, object], dict[tuple[int, ...], Derivation]] = {}
        self.patterns: dict[Production, object] = {}

    def pattern(self, prod: Production):
        """The s-expression pattern of a production as nested tuples;
           `{i}` stands for the i-th non-terminal operand.  Like the
           solution, the pattern has no annotations and no lets."""
        if prod not in self.patterns:
            p = _strip_annotations(_plain(next(tinysexpr.read(StringIO(prod.sexpr)))))
            self.patterns[prod] = inline_let(p, set())
        return self.patterns[prod]

    def prod_weights(self, prod: Production) -> tuple[int, ...]:
        # like LenConstraints._add_constr_weights: the attribute of the
        # production or the default of the weight
        return tuple(int(str(prod.attributes.get(name, default)))
                     for name, (default, _) in self.fun.weights.items())

    def constant(self, term, nt: Nonterminal) -> ExprRef | None:
        """The constant that `term` denotes if `nt` allows it."""
        if (v := _literal(term)) is None:
            return None
        if nt.sort == RealSort() and is_int(v):
            v = simplify(ToReal(v))
        if v.sort() != nt.sort:
            return None
        if nt.constants is None or any(_same_value(v, c) for c in nt.constants):
            return v
        return None

    def match(self, pattern, term, holes: list) -> bool:
        """Match `term` against `pattern`.  The subterms at the non-terminal
           placeholders are collected in `holes` as (placeholder index, subterm)."""
        if isinstance(pattern, str):
            if m := _PLACEHOLDER.fullmatch(pattern):
                holes.append((int(m[1]), term))
                return True
            if pattern == term:
                return True
        elif not isinstance(term, str) and len(pattern) == len(term):
            return all(self.match(p, t, holes) for p, t in zip(pattern, term))
        # e.g. the constant 1 written as (- 1) in the grammar and as -1 in the solution
        pv, tv = _literal(pattern), _literal(term)
        return pv is not None and tv is not None and _same_value(pv, tv)

    def derive(self, nt_name: str, term, chain: frozenset = frozenset()) -> dict[tuple[int, ...], Derivation]:
        """The derivations of `term` from non-terminal `nt_name`; one per
           achievable weight assignment (a single one if the synth-fun
           declares no weights).  Empty if the term is not derivable.
           `chain` holds the non-terminals that have been passed through by
           unit productions (productions consisting of a single non-terminal)
           to derive this very term; cycles of unit productions are cut."""
        key = (nt_name, term)
        if not chain and key in self.memo:
            return self.memo[key]
        nt = self.nts[nt_name]
        res: dict[tuple[int, ...], Derivation] = {}
        def add(leaf, prod, children, weights):
            res.setdefault(weights, Derivation(nt_name, leaf, prod, children, weights))
        def add_weights(*ws):
            return tuple(map(sum, zip(*ws)))

        if isinstance(term, str) and term in nt.parameters:
            add(term, None, (), self.zero)
        if (c := self.constant(term, nt)) is not None:
            add(c, None, (), self.zero)
        for prod in nt.productions:
            pattern = self.pattern(prod)
            nt_opnds = list(prod.nonterminal_operands())
            w = self.prod_weights(prod)
            if pattern == '{0}':
                # unit production: the same term derived from another non-terminal
                (_, other), = nt_opnds
                if other == nt_name or other in chain:
                    continue
                for d in self.derive(other, term, chain | { nt_name }).values():
                    add(None, prod, (d,), add_weights(w, d.weights))
                continue
            holes = []
            if not self.match(pattern, term, holes):
                continue
            # a placeholder may occur several times in a pattern (if the
            # production had a let); all its occurrences must be equal
            subs = {}
            if any(subs.setdefault(i, sub) != sub for i, sub in holes):
                continue
            assert sorted(subs) == list(range(len(nt_opnds))), \
                f'placeholders of production {prod.sexpr} do not match its non-terminal operands'
            children = [ self.derive(other, subs[i]) for i, (_, other) in enumerate(nt_opnds) ]
            if not all(children):
                continue
            for ds in product(*(c.values() for c in children)):
                add(None, prod, ds, add_weights(w, *(d.weights for d in ds)))
        if not chain:
            self.memo[key] = res
        return res

    def explain_failure(self, term) -> str:
        """Describe why `term` could not be derived: the smallest subterms
           that could not be derived from the non-terminal they were needed for."""
        failed = { (nt, t) for (nt, t), ds in self.memo.items() if not ds }
        failed_terms = { t for _, t in failed }
        minimal = sorted(((nt, t) for nt, t in failed
                          if not any(s in failed_terms for s in _subterms(t))),
                         key=lambda x: (len(_to_sexpr(x[1])), str(x)))
        msgs = [ f'{_to_sexpr(t)} is not derivable from {nt}' for nt, t in minimal[:3] ]
        if len(minimal) > 3:
            msgs.append('...')
        return '; '.join(msgs) if msgs else f'{_to_sexpr(term)} is not derivable'

# --------------------------------------------------------------------------
# results

@dataclass
class FuncResult:
    """Result of checking the define-fun of one synth-fun against its grammar."""

    name: str

    prgs: list[Prg] = field(default_factory=list)
    """Grammar-conforming programs for the define-fun; one for each
       achievable weight assignment.  Empty if the define-fun does not
       follow the grammar."""

    error: str | None = None
    """Why the define-fun does not follow the grammar."""

    @property
    def follows_grammar(self) -> bool:
        return self.error is None

    def __str__(self):
        return f'{self.name}: ' + ('follows grammar' if self.follows_grammar
                                   else f'does not follow grammar: {self.error}')

@dataclass
class ConstraintResult:
    """Result of verifying one synthesis constraint."""

    index: int
    constraint: Constraint

    result: str
    """'valid', 'violated', or 'unknown' (the solver could not decide)."""

    counterexample: list[ExprRef] | None = None
    """Values of the constraint's parameters that violate it."""

    @property
    def valid(self) -> bool:
        return self.result == 'valid'

    def __str__(self):
        res = f'constraint {self.index}: {self.result}'
        if self.counterexample is not None:
            cex = ', '.join(f'{p} = {v}' for p, v in zip(self.constraint.params, self.counterexample))
            res += f' for {cex}' if cex else ''
        return res

@dataclass
class CheckResult:
    funcs: dict[str, FuncResult]
    """For each synth-fun of the problem the result of the grammar check."""

    constraints: list[ConstraintResult] | None = None
    """For each constraint of the problem the result of its verification.
       None if the constraints could not be checked."""

    notes: list[str] = field(default_factory=list)
    """Additional remarks."""

    @property
    def follows_grammar(self) -> bool:
        return all(f.follows_grammar for f in self.funcs.values())

    @property
    def satisfies_constraints(self) -> bool:
        return self.constraints is not None and all(c.valid for c in self.constraints)

    def __bool__(self):
        return self.follows_grammar and self.satisfies_constraints

    def __str__(self):
        lines = [ str(f) for f in self.funcs.values() ]
        lines += [ str(c) for c in self.constraints or [] ]
        lines += self.notes
        lines += [ 'solution is correct' if self else 'solution is NOT correct' ]
        return '\n'.join(lines)

# --------------------------------------------------------------------------
# checking

def _signature_error(fun: SynthFunc, define_fun: SExpr) -> str | None:
    """Check the parameter and result sorts of a define-fun against a synth-fun."""
    if len(define_fun) != 5:
        return 'malformed define-fun'
    _, _, params, ret, _ = define_fun
    try:
        param_sorts = [ get_sort(s) for _, s in params ]
        ret_sort = get_sort(ret)
    except (SyGuSError, ValueError, TypeError) as e:
        return f'cannot parse signature: {e}'
    if param_sorts != list(fun.in_types):
        return f'parameter sorts {param_sorts} do not match the synth-fun {list(fun.in_types)}'
    if ret_sort != fun.out_types[0]:
        return f'result sort {ret_sort} does not match the synth-fun {fun.out_types[0]}'
    return None

def follows_grammar(fun: SynthFunc, define_fun: SExpr) -> FuncResult:
    """Check that the body of `define_fun` is derivable from the grammar of `fun`.
       If so, the result carries the programs (one per achievable weight
       assignment) that realize the define-fun with the productions of the grammar."""
    name = str(define_fun[1])
    if err := _signature_error(fun, define_fun):
        return FuncResult(name, error=err)
    _, _, params, _, body = define_fun
    sol_params = [ str(p) for p, _ in params ]
    try:
        with _deep_recursion():
            body = inline_let(_strip_annotations(_plain(body)), set())
            if free := _free_identifiers(body, set(sol_params)):
                return FuncResult(name, error=f'unbound identifiers: {", ".join(sorted(free))}')
            # a synthetic let renames the parameters of the solution to those
            # of the synth-fun
            term = inline_let(('let', tuple(zip(sol_params, (n for n, _ in fun.inputs))), body), set())
            grammar = _Grammar(fun)
            if derivs := grammar.derive(fun.result_nonterminals[0], term):
                return FuncResult(name, prgs=[ d.to_prg(fun) for d in derivs.values() ])
            return FuncResult(name, error=grammar.explain_failure(term))
    except RecursionError:
        return FuncResult(name, error='term is nested too deeply')

class _Semantics:
    """Adapts a solution to the interface `Constraint.verify` expects of a
       program: `eval_term(ins, outs)` states that `outs` is the result of
       the solution applied to `ins`."""

    def __init__(self, term):
        """`term(ins)` is the Z3 term of the solution applied to `ins`."""
        self.term = term

    @staticmethod
    def of_prg(prg: Prg):
        # the SMT-LIB semantics of the program: without the preconditions of
        # the operators
        return _Semantics(lambda ins: prg.to_exp(list(ins))[1][0])

    @staticmethod
    def of_define_fun(define_fun: SExpr, fun: SynthFunc):
        """Interpret a define-fun with the SyGuS parser (fails if it refers
           to functions defined in the problem file)."""
        sy = SyGuS()
        sy.parse_command(define_fun)
        body, inputs = sy.funs[str(define_fun[1])]
        if [ i.sort() for i in inputs ] != list(fun.in_types) or body.sort() != fun.out_types[0]:
            raise SyGuSError(f'signature of {define_fun[1]} does not match the synth-fun', None)
        return _Semantics(lambda ins: substitute(body, list(zip(inputs, ins))))

    def eval_term(self, ins, outs):
        return outs[0] == self.term(ins)

def verify_constraints(constraints: list[Constraint],
                       prgs: dict[str, _Semantics],
                       weights: dict[ExprRef, ExprRef] = {}) -> list[ConstraintResult]:
    """Verify each constraint against the programs.
       `weights` gives the values of the weight variables of the synth-funs."""
    subst = list(weights.items())
    res = []
    for i, c in enumerate(constraints):
        if subst:
            c = replace(c, phi=substitute(c.phi, subst))
        cex, stat = c.verify(prgs)
        if cex is not None:
            res.append(ConstraintResult(i, c, 'violated', cex))
        elif stat.get('verif_result') == 'unknown':
            res.append(ConstraintResult(i, c, 'unknown'))
        else:
            res.append(ConstraintResult(i, c, 'valid'))
    return res

def _refers_to(constraints: list[Constraint], vars) -> bool:
    """Does any constraint mention one of the variables?"""
    ids = { v.get_id() for v in vars }
    return any(v.get_id() in ids for c in constraints for v in free_vars(c.phi))

def check(problem: Problem, solution: dict[str, SExpr], max_weight_assignments: int = 64) -> CheckResult:
    """Check that `solution` solves `problem`: the define-fun of every
       synth-fun follows the grammar of the synth-fun and the solution
       satisfies all synthesis constraints.

       `solution` maps the names of the synth-funs to their define-funs (see
       `util.sygus.read_solution`).  The result is truthy iff the solution
       is correct; it contains the details per function and constraint.

       If the derivation of a solution from the grammar is ambiguous and the
       ambiguity affects the declared weights, all weight assignments (up to
       `max_weight_assignments`) are tried and the solution is accepted if
       one of them satisfies the constraints."""
    funcs = {}
    for name, fun in problem.funcs.items():
        if name in solution:
            funcs[name] = follows_grammar(fun, solution[name])
        else:
            funcs[name] = FuncResult(name, error='no define-fun in solution')
    res = CheckResult(funcs)
    if extra := [ n for n in solution if n not in problem.funcs ]:
        res.notes.append(f'solution defines functions that are not synth-funs: {", ".join(extra)}')

    # For each function, the candidate semantics with the weights they
    # imply.  A function that follows the grammar has one candidate per
    # derivation (they differ in weights only, so only one is needed if
    # the constraints do not refer to weights).
    weights_matter = _refers_to(problem.constraints,
                                [ var for f in problem.funcs.values() for _, var in f.weights.values() ])
    candidates = {}
    without_grammar = []
    for name, fun in problem.funcs.items():
        if funcs[name].follows_grammar:
            prgs = funcs[name].prgs if weights_matter else funcs[name].prgs[:1]
            candidates[name] = [ (_Semantics.of_prg(p), p.weights) for p in prgs ]
            continue
        # the define-fun does not follow the grammar; if it can be parsed
        # nonetheless, the constraints can still be checked
        if name not in solution:
            res.notes.append(f'constraints not checked: no define-fun for {name}')
            return res
        if _refers_to(problem.constraints, [ var for _, var in fun.weights.values() ]):
            res.notes.append(f'constraints not checked: they refer to weights of {name}, which need a derivation')
            return res
        try:
            candidates[name] = [ (_Semantics.of_define_fun(solution[name], fun), {}) ]
        except (SyGuSError, Z3Exception, ValueError, IndexError, TypeError) as e:
            res.notes.append(f'constraints not checked: {e}')
            return res
        without_grammar.append(name)
    if without_grammar:
        res.notes.append(f'constraints checked without the grammar for {", ".join(without_grammar)}')

    names = list(candidates)
    n_combos = math.prod(len(candidates[n]) for n in names)
    if n_combos > max_weight_assignments:
        res.notes.append(f'only {max_weight_assignments} of {n_combos} weight assignments were tried')
    for combo in islice(product(*(candidates[n] for n in names)), max_weight_assignments):
        sem = { n: s for n, (s, _) in zip(names, combo) }
        weights = { var: val for _, ws in combo for var, val in ws.items() }
        res.constraints = verify_constraints(problem.constraints, sem, weights)
        if all(c.valid for c in res.constraints):
            break
    return res
