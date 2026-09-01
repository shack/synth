import sys

from collections import defaultdict
from itertools import combinations as comb
from itertools import permutations as perm
from functools import cache, cached_property
from dataclasses import dataclass, field
from collections.abc import Sequence, Mapping

import itertools

from typing import Tuple

from z3 import *

from synth.util import IgnoreList, eval_model, get_max_used_bit_width, timer, Debug, no_debug, is_val, subst_with_number
from tinysexpr import SExpr

class Eval:
    def __init__(self, inputs, outputs, solver):
        self.inputs = inputs
        self.outputs = outputs
        self.solver = solver

    def __call__(self, input_vals):
        s = self.solver
        s.push()
        for var, val in zip(self.inputs, input_vals):
            s.add(var == val)
        assert s.check() == sat
        res = eval_model(s.model(), self.outputs)
        s.pop()
        return res

    def sample_n(self, n):
        """Samples the specification n times.
           The result is a list that contains n lists of
           input values that are unique.
           The list may contain less than n elements if there
           are less than n unique inputs.
        """
        res = []
        s = self.solver
        s.push()
        for _ in range(n):
            if s.check() == sat:
                ins  = eval_model(s.model(), self.inputs)
                res += [ ins ]
                s.add(Or([ v != iv for v, iv in zip(self.inputs, ins) ]))
            else:
                return res
        s.pop()
        return res

@dataclass(frozen=True)
class Signature:
    outputs: list[tuple[str, SortRef]]
    """The output variable names and their types."""

    inputs: list[tuple[str, SortRef]]
    """The input variable names and their types."""

    @cached_property
    def out_types(self):
        return [ s for _, s in self.outputs ]

    @cached_property
    def in_types(self):
        return [ s for _, s in self.inputs ]

@dataclass(frozen=True)
class Constraint:
    """\
    A class that represents a specification constraint.

    A specification constraint consists of a
    constraint (phi) over several variables (parameters).
    Phi uses the output variables of functions to be synthesized (function_applications).

    The inputs to these functions can be expressions that use the inputs (parameters)
    of phi. These expressions are given by inputs.
    """

    phi: BoolRef
    """The specification constraint."""

    params: tuple[Const]
    """The parameters of the synthesis constraint."""

    function_applications: dict[tuple[str, tuple[ExprRef]], tuple[ExprRef]] = field(compare=False)
    """\
    In the constraint, there are applications of functions that are to be synthesized.
    Each function application has a tuple of output variables and a tuple of input expressions.
    The output variables are variables that appear in phi.
    The input expressions are expressions over the parameters of the constraint.
    The function applications are given in this dictionary.
    The key of the dictionary is the name of the function.
    The value of the dictionary is a list of applications of the function.
    """

    def check_signatures(self, signatures: dict[str, Signature]):
        def eq(a, b):
            return len(a) == len(b) and all(x == y for x, y in zip(a, b))
        for (name, ins), outs in self.function_applications.items():
            assert name in signatures, f'function {name} not in signatures'
            sig = signatures[name]
            assert eq(tuple(o.sort() for o in outs), sig.out_types), \
                f'function {name} application has wrong output types'
            assert eq(tuple(i.sort() for i in ins), sig.in_types), \
                f'function {name} application has wrong input types'

    @cached_property
    def counterexample_eval(self):
        s = Solver()
        s.add(Not(self.phi))
        return Eval(self.params, self.params, s)

    def verify(self, prgs: dict[str, 'Prg'], d: Debug=no_debug, verbose=False):
        verif = Solver()
        verif.add(Not(self.phi))
        for (name, ins), outs in self.function_applications.items():
            verif.add(prgs[name].eval_term(ins, outs))
        if verbose:
            d('verif_constr', f'(verif-assert {verif.sexpr()})')
        stat = {}
        if verbose:
            stat['verif_constraint'] = str(verif)
        with timer() as elapsed:
            res = verif.check()
            verif_time = elapsed()
        stat['verif_time'] = verif_time
        stat['verif_result'] = str(res)
        d('verif_time', f'(verif-time {verif_time / 1e9:.3f})')
        if res == sat:
            # there is a counterexample
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
            inst_args = [ substitute(i, param_subst) for i in ins ]
            _, inst_outs = synths[name].instantiate(id, inst_args, tmp)
            out_subst.extend(zip(outs, inst_outs))

        phi = substitute(self.phi, param_subst + out_subst)
        res.append(simplify(phi))
        for c in tmp:
            res.append(substitute(simplify(c), out_subst))
        return res

class Spec(Constraint):
    def __init__(self, name: str,
                 phi: BoolRef, outputs: tuple[Const], inputs: tuple[Const],
                 precond: BoolRef = BoolVal(True)):
        """
        Create a specification.

        A specification object represents n specifications each given
        by a Z3 expression (phi).

        inputs is the list of input variables that the n formulas use.
        outputs is the list of output variables that the n formulas use.
        There must be as many variables in outputs as there are formulas in phi.
        Each specification can optionally have a precondition (preconds)
        to express partial functions.
        If preconds is None, all preconditions are True.

        Specifications can be non-deterministic.

        Attributes:
        name: Name of the specification.
        phi: Z3 expression that represents the specification
        outputs: List of output variables in phi.
        inputs: List of input variables in phi.
        precond: A precondition for the specification
            (if None, the precondition is True).

        Note that the names of the variables don't matter because when
        used in the synthesis process their names are substituted by internal names.
        """
        inputs = tuple(inputs)
        outputs = tuple(outputs)
        Constraint.__init__(
            self,
            phi=Implies(precond, phi),
            params=inputs,
            function_applications={ (name, inputs): outputs },
        )
        self.name = name

    def __repr__(self):
        return f'Spec({self.name}, phi={self.phi}, inputs={self.inputs}, outputs={self.outputs})'

    @cached_property
    def precond(self):
        return self.phi.arg(0)

    @cached_property
    def postcond(self):
        return self.phi.arg(1)

    @cached_property
    def arity(self):
        return len(self.params)

    @cached_property
    def inputs(self):
        return self.params

    @cached_property
    def outputs(self):
        return next(iter(self.function_applications.values()))

    @cached_property
    def in_types(self):
        return tuple(s.sort() for s in self.inputs)

    @cached_property
    def out_types(self):
        return tuple(s.sort() for s in self.outputs)

    @cached_property
    def is_identity(self):
        if not (len(self.inputs) == 1 and len(self.outputs) == 1 and \
                self.inputs[0].sort() == self.outputs[0].sort()):
            return False
        solver = Solver()
        solver.add(self.precond)
        solver.add(self.phi)
        solver.add(self.inputs[0] != self.outputs[0])
        return solver.check() == unsat

    @cached_property
    def is_functional(self):
        outs, ins, pre, post = self.instantiate_with_fresh_vars()
        s = Solver()
        s.add(pre)
        s.add(self.precond)
        s.add(post)
        s.add(self.postcond)
        s.add(And(x0 == x1 for x0, x1 in zip(self.inputs, ins)))
        s.add(Or(y0 != y1 for y0, y1 in zip(self.outputs, outs)))
        return s.check() == unsat

    def instantiate(self, outs, ins):
        assert len(outs) == len(self.outputs)
        assert len(ins) == len(self.inputs)
        # this should actually be self.precond but this is ok, too
        phi = substitute(self.phi, list(zip(self.outputs + self.inputs, outs + ins)))
        pre = substitute(self.precond, list(zip(self.inputs, ins)))
        return pre, phi

    def instantiate_with_fresh_vars(self):
        outs = [ FreshConst(v.sort(), str(v)) for v in self.outputs ]
        ins  = [ FreshConst(v.sort(), str(v)) for v in self.inputs ]
        pre, phi = self.instantiate(outs, ins)
        return outs, ins, pre, phi

class Func(Spec):
    def _collect_vars(expr):
        res = set()
        def collect(expr):
            if len(expr.children()) == 0 and expr.decl().kind() == Z3_OP_UNINTERPRETED:
                res.add(expr)
            else:
                for c in expr.children():
                    collect(c)
        collect(expr)
        return res

    def __repr__(self):
        return f'Func({self.name}, phi={self.phi}, inputs={self.inputs})'

    def __init__(self, name, phi, precond=BoolVal(True), inputs=None):
        """Creates an Op from a Z3 expression.

        Attributes:
        name: Name of the operator.
        phi: Z3 expression that represents the semantics of the operator.
        precond: Z3 expression that represents the precondition of the operator.
        inputs: List of input variables in phi. If [] is given, the inputs
            are taken in lexicographical order.
        """
        # if no inputs are specified, we take the identifiers in
        # lexicographical order. That's just a convenience
        if inputs is None:
            input_vars = Func._collect_vars(phi)
            inputs = tuple(sorted(input_vars, key=lambda v: str(v)))
        input_names = set(str(v) for v in inputs)
        names = tuple(n for n in 'yzr' if not n in input_names)
        res_ty = phi.sort()
        out = Const(names[0], res_ty) if names else FreshConst(res_ty, 'y')
        super().__init__(name, out == phi, (out,), inputs, precond=precond)

    @cached_property
    def func(self):
        # Z3 reorders the arguments of an equation if one of them is a
        # numeral (the numeral comes first), so we cannot rely on the
        # output variable being the left-hand side.
        eq = self.phi.arg(1)
        lhs, rhs = eq.arg(0), eq.arg(1)
        return rhs if lhs.eq(self.outputs[0]) else lhs

    @cached_property
    def out_type(self):
        return self.out_types[0]

    def is_symmetric_of(self, other: 'Func'):
        # if the operator inputs have different sorts, it cannot be symmetric
        if len(self.in_types) != len(other.in_types) or \
           self.out_type != other.out_type or \
           any(a != b for a, b in zip(self.in_types, other.in_types)) or \
           len(set(self.in_types)) > 1 or len(self.inputs) > 3 or \
           len(self.inputs) < 2:
            return False
        precond1 = self.precond
        func1    = self.func
        precond2 = other.precond
        func2    = other.func
        ins      = self.params
        subst    = lambda f, i: substitute(f, list(zip(ins, i)) + list(zip(other.params, i)))
        fs = [ And([ subst(precond1, a), subst(precond2, b), \
                     subst(func1, a) != subst(func2, b) ]) \
                for a, b in comb(perm(ins), 2) ]
        s = Solver()
        s.add(Or(fs))
        return s.check() == unsat

    @cached_property
    def is_commutative(self):
        return len(self.params) >= 2 and self.is_symmetric_of(self)

@dataclass(frozen=True)
class Production:
    """A production rule in a sygus grammar."""

    """The function corresponding to this production."""
    op: Func

    """
    The operands of the production.
    Each element can be either the name of a parameter or of a non-terminal.
    """
    operands: tuple[str]

    """
    Indicates if operand is non-terminal or function parameter.
    """
    operand_is_nt: tuple[Bool]

    """
    Original sexpr string representation for dumping.
    The placeholder {k} stands for the k-th *non-terminal* operand, in the
    order of `nonterminal_operands`; parameter operands are spelled out in
    the string.  So the placeholders are exactly {0}..{n-1} for
    n = `nonterminal_arity`, which is what `Prg.sexpr` relies on when it
    formats the string and what `util.check` requires of a solution.
    """
    sexpr: str

    """
    Additional attributes for the production.
    Could be number of maximum occurrences, or a weight.
    """
    attributes: dict[str, Any] = field(default_factory=lambda: {}, compare=False)

    def __repr__(self):
        return f'{self.op.name}{self.operands}'

    def nonterminal_operands(self):
        for i, (is_nt, op) in enumerate(zip(self.operand_is_nt, self.operands)):
            if is_nt:
                yield (i, op)

    def parameter_operands(self):
        for i, (is_nt, op) in enumerate(zip(self.operand_is_nt, self.operands)):
            if not is_nt:
                yield (i, op)

    def nonterminal_arity(self):
        return sum(1 for _ in self.nonterminal_operands())

    def is_unit(self):
        """True iff this production's term is syntactically nothing but its
           single non-terminal operand, i.e. it is a unit/chain production
           `A ::= B`.  Only such a production can be dropped from a program
           without changing the term that `Prg.sexpr` prints."""
        return len(self.operands) == 1 \
           and self.nonterminal_arity() == 1 \
           and self.sexpr.strip() == '{0}'

    def operand_vector(self, nt_values, param_value):
        """Arrange values for the inputs of the production's function:
           `nt_values` gives the values of the non-terminal operands (in the
           order of `nonterminal_operands`), `param_value(name)` the value of
           a parameter operand."""
        res = [ None ] * self.op.arity
        for (idx, _), val in zip(self.nonterminal_operands(), nt_values, strict=True):
            res[idx] = val
        for idx, param in self.parameter_operands():
            res[idx] = param_value(param)
        assert None not in res
        return res

    def contains_nonterminal(self, nt: str):
        return nt in self.operands

    def _inline(self, lhs: Nonterminal, operands: list[int], non_terminals: dict[str, 'Nonterminal']):
        """
        'Inline' all productions of the non-terminals whose parameter index
        are given in the operands list into this production.
        """
        if not operands:
            return (False, (self,))

        # all to-be inlined operands have to be non-terminals
        assert all(self.operands[i] in non_terminals for i in operands)

        operands = [ (i, non_terminals[self.operands[i]]) for i in operands ]

        # the to-be inlined non-terminals cannot have unspecified many constants
        assert all(nt.constants is not None for _, nt in operands)

        productions = [
            [ (i, e) for e in
                list(nt.productions) +
                list(nt.constants.keys()) +
                list(nt.parameters)
            ] for i, nt in operands
        ]

        # `sexpr` numbers its placeholders over the non-terminal operands only,
        # so the substitution vector has to be built in that index space and not
        # in the one of `operands`.  The two coincide only if every operand is a
        # non-terminal.
        nt_index = { opnd: k for k, (opnd, _) in enumerate(self.nonterminal_operands()) }

        prods = []
        seen = set()
        if productions:
            for inl in itertools.product(*productions):
                inl = { i: e for i, e in inl }
                res_func = self.op.func
                res_precond = self.op.precond
                res_opnds = [ ]
                res_inputs = [ ]
                res_opnd_is_nt = [ ]
                # one entry per non-terminal operand: the text that replaces its
                # placeholder, which is the inlined constant for the operands
                # that go away and the renumbered placeholder for those that stay
                subst = [ None ] * self.nonterminal_arity()
                for i, v in enumerate(self.op.inputs):
                    if i in inl:
                        opnd = inl[i]
                        match opnd:
                            case Production(args):
                                assert False, "not yet tested"
                                # res_func = substitute(res_func, (v, op.func))
                                # res_opnds += opnds
                                # res_inputs += op.inputs
                            case ExprRef():
                                # constant: it takes the place of the operand in
                                # the sexpr str, in the formula and in the precondition
                                subst[nt_index[i]] = opnd.sexpr()
                                res_func = substitute(res_func, (v, opnd))
                                res_precond = substitute(res_precond, (v, opnd))
                            case str(name):
                                # parameters
                                assert False, "not yet tested"
                                # res_opnds[i] = (name,)
                                # res_inputs[i] = (FreshConst(parameters[name], name),)
                    else:
                        res_inputs += [ v ]
                        res_opnds += [ self.operands[i] ]
                        res_opnd_is_nt += [ self.operand_is_nt[i] ]
                        if self.operand_is_nt[i]:
                            # the operand keeps its position among the surviving
                            # non-terminal operands
                            subst[nt_index[i]] = f'{{{sum(res_opnd_is_nt) - 1}}}'
                res_func = simplify(res_func)
                if not is_val(res_func) or \
                   (lhs.constants is not None and res_func not in lhs.constants):
                    res_opnds = tuple(res_opnds)
                    res_inputs = tuple(res_inputs)
                    assert None not in subst
                    res_sexpr = self.sexpr.format(*subst)
                    res_opnd_is_nt = tuple(res_opnd_is_nt)
                    f = Func(self.op.name, res_func,
                             precond=simplify(res_precond), inputs=res_inputs)
                    # clones that differ only in their printed term are
                    # redundant, e.g. (+ 1 2) and (+ 2 1) of a folded (+ C C)
                    key = (str(res_func), str(f.precond), res_opnds, res_opnd_is_nt)
                    if key not in seen:
                        seen.add(key)
                        # each clone gets its own attribute dict so that no
                        # clone aliases the attributes of another production
                        p = Production(f, res_opnds, res_opnd_is_nt, res_sexpr,
                                       dict(self.attributes))
                        prods.append(p)
        return (True, tuple(prods)) if prods else (False, (self,))

    def optimize(self, lhs: Nonterminal, all_non_terminals: dict[str, 'Nonterminal']):
        operands = []
        # inlining replaces this production by one clone per combination of
        # the inlined constants, so bound the product of the set sizes, not
        # just each factor
        n_clones = 1
        for i, op in enumerate(self.operands):
            if op in all_non_terminals and (op_nt := all_non_terminals[op]).produces_only_constants():
                # only inline pure constant sets: inlining a non-terminal's rules
                # can fold them into nullary productions, which leaves
                # produces_only_constants() true while productions remain --
                # and _inline can only ingest constants, not productions
                if len(op_nt.productions) == 0 and \
                   op_nt.constants is not None and len(op_nt.constants) < 5 and \
                   n_clones * len(op_nt.constants) <= 16:
                    operands.append(i)
                    n_clones *= len(op_nt.constants)
        return self._inline(lhs, operands, all_non_terminals)

@dataclass(frozen=True)
class Nonterminal:
    """A non-terminal in a sygus grammar."""

    """The name of the non-terminal."""
    name: str

    """The sort of the non-terminal."""
    sort: SortRef

    """The parameters of the non-terminal."""
    parameters: tuple[str]

    """The parameters of the non-terminal."""
    productions: tuple[Production]

    """The constants of the non-terminal.
       None means that any constant of the sort is allowed."""
    constants: dict[ExprRef, int | None] | None

    def is_cyclic(self):
        return any(p.contains_nonterminal(self.name) for p in self.productions)

    def produces_only_constants(self):
        operands = set([ op for prod in self.productions for op in prod.operands])
        return operands <= set([ self.name ]) \
            and len(self.parameters) == 0 \
            and (self.constants is None or len(self.constants) > 0)

    def referenced_non_terminals(self):
        return set(n for p in self.productions for (_, n) in p.nonterminal_operands())

    def optimize(self, all_non_terminals: dict[str, 'Nonterminal']):
        if self.produces_only_constants() and len(self.productions) > 0:
            # if the only nt referenced from the productions in this nt
            # is the nt itself and if there are only constants,
            # replace the non-terminal by just constants
            # TODO: Strictly speaking, this violates the grammar.
            return Nonterminal(
                name=self.name,
                sort=self.sort,
                parameters=[],
                productions=[],
                constants=None)

        # Let's optimise productions.
        changed = False
        prods = ()
        for p in self.productions:
            c, p = p.optimize(self, all_non_terminals)
            changed |= c
            prods += p
        if changed:
            return Nonterminal(
                name=self.name,
                sort=self.sort,
                productions=prods,
                parameters=self.parameters,
                constants=self.constants,
            )

        return self

    @cache
    def _constants_are_interval(consts):
        # check for contiguous range of values so that we can make an interval constraint
        vals = sorted([ c.as_long() for c in consts ])
        if all(b == a + 1 for a, b in itertools.pairwise(vals)):
            return vals[0], vals[-1]
        else:
            None

    def const_val_constraint(self, var: ExprRef):
        """
        Returns a Z3 constraint that ensures that `var` takes
        one of the allowed constant values of this non-terminal.
        """
        if self.constants is None:
            return BoolVal(True)
        elif len(self.constants) == 0:
            return BoolVal(False)
        elif 'as_long' in dir((consts := tuple(self.constants.keys()))[0]):
            if lu := Nonterminal._constants_are_interval(consts):
                l, u = lu
                dummy = FreshConst(self.sort, '')
                if is_int(dummy):
                    return And(l <= var, var <= u)
                elif is_bv(dummy):
                    width = self.sort.size()
                    ll, uu = BitVecVal(l, width), BitVecVal(u, width)
                    if l >= 0:
                        return And(ULE(ll, var), ULE(var, uu))
                    else:
                        return And(ll <= var, var <= uu)
        # the default: enumerate them all
        return Or([ var == c for c in self.constants ])

@dataclass(frozen=True)
class SynthFunc(Signature):
    """A function to be synthesized."""

    nonterminals: dict[str, Nonterminal]
    """The grammar."""

    result_nonterminals: tuple[str]
    """The non-terminals for the result variables."""

    weights: dict[str, Tuple[int, ExprRef]]
    """Defined weights with default value."""

    max_const: int | None = None
    """Limit the number of constants used in the synthesis.
       The default is None which means unbounded."""

    def all_funcs(self):
        for nt in self.nonterminals.values():
            for prod in nt.productions:
                yield prod.op

    def optimize_grammar(self):
        # post-order dfs over the grammar and optimise productions
        # if deemed profitable
        optimized = self.nonterminals.copy()
        def optimize(nt, visited):
            visited.add(nt.name)
            for other in nt.referenced_non_terminals():
                if other not in visited:
                    optimize(self.nonterminals[other], visited)
            optimized[nt.name] = nt.optimize(optimized)
        for name in self.result_nonterminals:
            optimize(self.nonterminals[name], set())

        # find non-terminals reachable from the start
        new = {}
        q = list(self.result_nonterminals)
        visited = set()
        while q:
            name = q.pop()
            nt = optimized[name]
            new[name] = nt
            for other in nt.referenced_non_terminals():
                if other not in visited:
                    q.append(other)
                    visited.add(other)

        return SynthFunc(
            outputs=self.outputs,
            inputs=self.inputs,
            nonterminals=new,
            result_nonterminals=self.result_nonterminals,
            weights=self.weights,
            max_const=self.max_const
        )

    def flatten_grammar(self):
        ops = {}
        consts = {}
        for nt in self.nonterminals.values():
            if nt.constants is None:
                consts = None
            elif consts is not None:
                consts |= nt.constants
            for p in nt.productions:
                ops[p.op] = None
        return synth_func_from_ops(
            in_types=self.in_types,
            out_types=self.out_types,
            ops=ops,
            const_map=consts,
            max_const=self.max_const)

def synth_func_from_ops(
        in_types: Sequence[SortRef],
        out_types: Sequence[SortRef],
        ops: Mapping[Func, int] | Sequence[Func],
        const_map: dict[ExprRef, int | None] | None = None,
        max_const: int | None = None) -> SynthFunc:

    ins = { f'x{i}': s for i, s in enumerate(in_types) }
    # a map from sorts to the operators that produce them
    sorts = defaultdict(list)
    # add all sorts that appear as result types of operators
    if not isinstance(ops, Mapping):
        ops = { op: None for op in ops }
    for op, mx in ops.items():
        sorts[op.out_type].append((op, mx))
        # also make sure that all input types are present
        for op_ty in op.in_types:
            sorts[op_ty] += []
    if const_map is not None:
        # if there are constants, also registers the sorts of the constants
        for c in const_map:
            sorts[c.sort()] += []
    # finally, there also need to be sorts for the input and output types of the spec
    # they might not be there in the case that no operator produces/consumes them
    for t in in_types + out_types:
        sorts[t] += []

    # create non-terminals for all sorts and their operators
    nts = {}
    for ty, ops in sorts.items():
        name = str(ty)
        prods = tuple(Production(
            op=op,
            operands=tuple(str(t) for t in op.in_types),
            operand_is_nt=tuple(True for _ in op.in_types),
            sexpr=subst_with_number(f'({op.name} {" ".join(str(x) for x in op.in_types)})', op.in_types),
            attributes=({} if mx is None else { 'max': mx })) for op, mx in ops)
        nts[name] = Nonterminal(
            name=name,
            sort=ty,
            constants=None if const_map is None else {c: v for c, v in const_map.items() if c.sort() == ty},
            parameters=tuple(n for n, s in ins.items() if s == ty),
            productions=prods,
        )

    return SynthFunc(
        inputs=[ (n, s) for n, s in ins.items() ],
        outputs=[ ( f'r{i}', s) for i, s in enumerate(out_types) ],
        nonterminals=nts,
        result_nonterminals=tuple(map(str, out_types)),
        weights={},
        max_const=max_const
    )

@dataclass(frozen=True)
class Problem:
    constraints: list[Constraint]
    funcs: dict[str, SynthFunc]
    theory: str | None = None
    name: str | None = None

    def is_deterministic(self, abs) -> bool:
        """Check, if the specification constraint forces a deterministic function."""
        new_var = lambda v: FreshConst(v.sort(), str(v))
        s = Solver()
        all_params = set(x for c in self.constraints for x in c.params)
        apps       = { p: ys for c in self.constraints \
                      for p, ys in c.function_applications.items() }
        in_subst   = [ (x, new_var(x)) for x in all_params ]
        out_subst  = [ (y, new_var(y)) for ys in apps.values() for y in ys ]
        for c in self.constraints:
            s.add(c.phi)
            s.add(substitute(c.phi, in_subst + out_subst))
        s.add(And(abs.beta(a) == abs.beta(b) for a, b in in_subst))
        s.add(Or (abs.beta(a) != abs.beta(b) for a, b in out_subst))
        return s.check() == unsat

    def get_max_used_bit_width(self) -> int:
        """Get the maximum used bit width.
           Returns 0 if not a bit vector problem."""
        return max((get_max_used_bit_width(f.func) \
                    for sf in self.funcs.values() \
                    for f in sf.all_funcs()), default=0)

def Task(spec: Spec, ops, const_map=None, max_const=None, theory=None):
    out_types=[ v.sort() for v in spec.outputs ]
    in_types=[ v.sort() for v in spec.inputs ]
    func = synth_func_from_ops(
        in_types=in_types,
        out_types=out_types,
        ops=ops,
        const_map=const_map)
    return Problem(constraints=[ spec ], funcs={ spec.name: func })

class Prg:
    def __init__(self, sig: Signature, insns, outputs, weights={}):
        """Creates a program.

        Attributes:
        func: The function that this program implements.
        insns: List of instructions.
            This is a list of pairs where each pair consists
            of an Op and a list of pairs that denotes the arguments to
            the instruction. The first element of the pair is a boolean
            that indicates whether the argument is a constant or not.
            The second element is either the variable number of the
            operand or the constant value of the operand.
        outputs: List of outputs.
            For each output variable in `spec` there is a tuple
            `(is_const, v)` in this list. `is_const` indicates that
            the output is constant. In this case, `v` is a Z3 constant
            that gives the value of the constant output. If `is_const`
            is false, `v` is a Python int that indicates the number of
            the instruction in this program whose value is the output.
            Note that the first n numbers are taken by the n inputs
            of the program.
        """
        self.sig          = sig
        self.insns        = insns
        self.outputs      = outputs
        self.weights      = weights
        self.output_names = [ n for n, _ in sig.outputs ]
        self.input_names  = [ n for n, _ in sig.inputs ]
        self.n_inputs     = len(self.input_names)
        # this map gives for every temporary/input variable
        # which output variables are set to it
        self.output_map = { }
        for (is_const, v), name in zip(outputs, self.output_names):
            if not is_const:
                self.output_map.setdefault(v, []).append(name)

    def var_name(self, i):
        if i < self.n_inputs:
            return self.input_names[i]
        elif i in self.output_map:
            return self.output_map[i][0]
        else:
            s = f'x{i}'
            j = 0
            while s in self.input_names or s in self.output_names:
                s = f'x{i}_{j}'
                j = j + 1
            return s

    def __eq__(self, other):
        return self.insns == other.insns and \
               self.outputs == other.outputs

    def __len__(self):
        return len(self.insns)

    def _is_insn(self, v):
        return self.n_inputs <= v < self.n_inputs + len(self.insns)

    def _get_insn(self, v):
        return self.insns[v - self.n_inputs] if self._is_insn(v) else None

    def eval_clauses(self, in_vars, out_vars, instance_id=None,
                     const_translate=lambda ins, n, ty, v: v,
                     intermediate_vars=IgnoreList()):
        suffix = f'_{instance_id}' if instance_id else ''
        vars = list(in_vars)
        n_inputs = len(vars)
        def get_val(ins, n_input, ty, p):
            is_const, v = p
            assert is_const or v < len(vars), f'variable out of range: {v}/{len(vars)}'
            return const_translate(ins, n_input, ty, v) if is_const else vars[v]
        for ins, (prod, opnds) in enumerate(self.insns):
            subst = [ (i, get_val(ins, n_input, i.sort(), p)) \
                      for (n_input, (i, p)) in enumerate(zip(prod.op.inputs, opnds)) ]
            res = FreshConst(prod.op.func.sort(), f'{self.var_name(ins + n_inputs)}{suffix}')
            vars.append(res)
            intermediate_vars.append(res)
            yield And([substitute(prod.op.precond, subst), res == substitute(prod.op.func, subst)])
        for n_out, (o, p) in enumerate(zip(out_vars, self.outputs)):
            yield o == get_val(len(self.insns), n_out, o.sort(), p)
        for var, val in self.weights.items():
            yield var == val

    def eval_term(self, in_vars, out_vars, instance_id=None,
                  const_translate=lambda ins, n, ty, v: v):
        tmp = list()
        clauses = And(c for c in self.eval_clauses(in_vars, out_vars,
                                                   instance_id=instance_id,
                                                   const_translate=const_translate,
                                                   intermediate_vars=tmp))
        tmp = list(set(tmp).difference(out_vars).difference(in_vars))
        return Exists(tmp, clauses) if tmp else clauses

    def to_exp(self, ins: list[ExprRef]):
        assert len(self.outputs) == 1
        var_to_exp = ins + [ 0 ] * len(self.insns)
        precond = BoolVal(True)
        for i, (prod, opnds) in enumerate(self.insns):
            op = prod.op
            assert len(op.inputs) == len(opnds)
            assert len(op.outputs) == 1
            subst = tuple((v, op if is_const else var_to_exp[op]) for v, (is_const, op) in zip(op.inputs, opnds))
            var_to_exp[len(ins) + i] = substitute(op.func, *subst)
            precond = And(precond, substitute(op.precond, *subst))
        return precond, tuple(v if is_const else var_to_exp[v] for is_const, v in self.outputs)

    def copy_propagation(self):
        @cache
        def prop(val):
            if res := self._get_insn(val):
                prod, args = res
                if prod.is_unit():
                    c, v = args[0]
                    if not c:
                        return prop(v)
            return val

        new_insns = [ (op, [ (c, prop(v) if not c else v) for c, v in args ])
                        for op, args in self.insns ]
        new_outs  = [ (c, prop(v) if not c else v) for c, v in self.outputs ]
        return Prg(self.sig, new_insns, new_outs)

    def dce(self):
        live = set(insn for is_const, insn in self.outputs if not is_const)
        get_idx = lambda i: i + self.n_inputs
        for i, (_, args) in reversed(list(enumerate(self.insns))):
            if get_idx(i) in live:
                live.update([ v for c, v in args if not c ])
        m = { i: i for i in range(self.n_inputs) }
        new_insns = []
        map_args = lambda args: [ (c, m[v]) if not c else (c, v) for c, v in args ]
        for i, (op, args) in enumerate(self.insns):
            idx = get_idx(i)
            if idx in live:
                m[idx] = get_idx(len(new_insns))
                new_insns.append((op, map_args(args)))
        new_outs = map_args(self.outputs)
        return Prg(self.sig, new_insns, new_outs)

    @cached_property
    def eval(self):
        s = Solver()
        for p in self.eval_clauses():
            s.add(p)
        return Eval(self.in_vars, self.out_vars, s)

    def to_string(self, sep='\n'):
        all_names  = [ self.var_name(i) for i in range(len(self) + self.n_inputs) ]
        max_len    = max(map(len, all_names), default=0)
        max_op_len = max(map(lambda x: len(x[0].op.name), self.insns), default=0)
        jv = lambda args: ', '.join(str(v) if c else self.var_name(v) for c, v in args)
        res = []
        for i, names in self.output_map.items():
            if i < self.n_inputs:
                res += [ f'{n:{max_len}} = {self.input_names[i]}' for n in names ]
        for i, (prod, args) in enumerate(self.insns):
            y = self.var_name(i + self.n_inputs)
            res += [ f'{y:{max_len}} = {prod.op.name:{max_op_len}} ({jv(args)})' ]
        for names in self.output_map.values():
            for n in names[1:]:
                res += [ f'{n:{max_len}} = {names[0]}']
        for n, (is_const, v) in zip(self.output_names, self.outputs):
            if is_const:
                res += [ f'{n:{max_len}} = {v}' ]
        return sep.join(res)

    def __str__(self):
        return self.to_string(sep='; ')

    def sexpr(self, name, sep=' '):
        def arg_to_sexpr(is_const, v):
            return v.sexpr() if is_const else self.var_name(v)
        def insn_to_sexpr(prod, args):
            # the placeholders {i} of the sexpr denote the non-terminal
            # operands; parameter operands are spelled out in the sexpr
            return prod.sexpr.format(*[arg_to_sexpr(*args[i]) for i, _ in prod.nonterminal_operands()])
        res = [ f'(define-fun {name} (' ]
        res[0] += ' '.join([ f'({n} {ty.sexpr()})' for n, ty in self.sig.inputs ])
        res[0] += f') {self.sig.outputs[0][1].sexpr()}'
        to_close = 1
        for i, names in self.output_map.items():
            if i < self.n_inputs:
                res += [ f'(let (({n} {self.input_names[i]}))' for n in names ]
                to_close += 1
        for i, (op, args) in enumerate(self.insns):
            y = self.var_name(i + self.n_inputs)
            res += [ f'(let (({y} {insn_to_sexpr(op, args)}))' ]
            to_close += 1
        for n, (is_const, v) in zip(self.output_names, self.outputs):
            if is_const:
                res += [ f'(let (({n} {v.sexpr()}))' ]
                to_close += 1
        if len(self.output_names) > 1:
            res += [ "(" + " ".join(self.output_names) + ")" ]
        else:
            res += [ self.output_names[0] ]
        res = sep.join(res)
        return res + ')' * to_close

    def print_graphviz(self, file):
        constants = {}
        def print_arg(node, i, is_const, v):
            if is_const:
                if not v in constants:
                    constants[v] = f'const{len(constants)}'
                    print(f'  {constants[v]} [label="{v}"];')
                v = constants[v]
            print(f'  {node} -> {v} [label="{i}"];')

        save_stdout, sys.stdout = sys.stdout, file
        n_inputs = len(self.input_names)
        print(f"""digraph G {{
  rankdir=BT
  {{
    rank = same;
    edge[style=invis];
    rankdir = LR;
""")
        for i, inp in enumerate(self.input_names):
            print(f'    {i} [label="{inp}"];')
        print(f"""
    { ' -> '.join([str(i) for i in range(n_inputs)])};
  }}""")

        for i, (prod, args) in enumerate(self.insns):
            node = i + n_inputs
            print(f'  {node} [label="{prod.op.name}",ordering="out"];')
            for i, (is_const, v) in enumerate(args):
                print_arg(node, i, is_const, v)
        print(f'  return [label="return",ordering="out"];')
        for i, (is_const, v) in enumerate(self.outputs):
            print_arg('return', i, is_const, v)
        print('}')
        sys.stdout = save_stdout

def create_bool_func(func):
    import re
    def is_power_of_two(x):
        return (x & (x - 1)) == 0
    if re.match('^0[bodx]', func):
        base = { 'b': 2, 'o': 8, 'd': 10, 'x': 16 }[func[1]]
        func = func[2:]
    else:
        base = 16
    assert is_power_of_two(base), 'base of the number must be power of two'
    bits_per_digit = int(math.log2(base))
    n_bits = len(func) * bits_per_digit
    bits = bin(int(func, base))[2:].zfill(n_bits)
    assert len(bits) == n_bits
    assert is_power_of_two(n_bits), 'length of function must be power of two'
    n_vars  = int(math.log2(n_bits))
    vars    = [ Bool(f'x{i}') for i in range(n_vars) ]
    clauses = []
    binary  = lambda i: bin(i)[2:].zfill(n_vars)
    for i, bit in enumerate(bits):
        if bit == '1':
            clauses += [ And([ vars[j] if b == '1' else Not(vars[j]) \
                            for j, b in enumerate(binary(i)) ]) ]
    return Func(func, Or(clauses) if len(clauses) > 0 else BoolVal(False), inputs=vars)
