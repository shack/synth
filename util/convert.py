from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import re
import tinysexpr
from tinysexpr import SExpr

@dataclass(frozen=True)
class NewToOld:
    remove_type_underscores: bool = True
    """(_ type ...) -> (type ...)"""

    remove_non_terminal_list: bool = True
    """Remove the list of non-terminals right after the return type of a synth-fun."""

    negative_literals: bool = True
    """(- n) -> -n for numerals n (some SyGuS 1.0 solvers have no unary minus in grammars)"""

    def rewrite(self, sexpr: Any) -> SExpr:
        if not isinstance(sexpr, SExpr):
            return sexpr
        children = [ self.rewrite(s) for s in sexpr ]
        match children:
            case ['-', str() as n] if self.negative_literals and re.fullmatch(r'\d+(\.\d+)?', n):
                return f'-{n}'
            case ['_', ty, *rest] if self.remove_type_underscores:
                children = [ ty, *rest ]
            case ['synth-fun', *rest] if self.remove_non_terminal_list:
                name, params, res_ty = rest[:3]
                # if we have a grammar definition
                if len(children) > 4:
                    # get the grammar definition
                    rest = children[4:]
                    match rest:
                        case [_, comps]:
                            # we have a list of non-terminals and their sorts,
                            # and a list of components per nonterminal
                            # as described in the SyGuS spec
                            pass
                        case [comps]:
                            # we only have a list of components, so create a default non-terminal
                            # this seems to appear in older files. Not really spec-conforming.
                            pass
                        case _:
                            assert len(rest) == 1, 'expecting only one more s-expr'
                else:
                    comps = ()
                children = [ 'synth-fun', name, params, res_ty, comps ]
        return SExpr(s=tuple(children), range=sexpr.range)

    def __call__(self, input, output):
        for s in tinysexpr.read(input):
            print(self.rewrite(s), file=output)

@dataclass(frozen=True)
class OldToNew:
    def rewrite(self, sexpr: Any, nullary: frozenset[str] = frozenset()) -> SExpr:
        """nullary: the functions without parameters, whose applications (f) become f"""
        if not isinstance(sexpr, SExpr):
            return sexpr
        children = [ self.rewrite(s, nullary) for s in sexpr ]
        match children:
            case ['BitVec', n]:
                children = ['_', 'BitVec', n]
            case ['constraint' | 'define-fun', *_] if nullary:
                # only in terms: in grammars, (x) is a list of rules
                children[-1] = _nullary_apps_to_symbols(children[-1], nullary)
            case ['synth-fun', *rest]:
                name, params, res_ty = rest[:3]
                # if we have a grammar definition
                if len(rest) == 4:
                    # we have a grammar definition but no non-terminals list
                    grammar = rest[3]
                    no_range = ((0, 0), (0, 0))
                    non_terms = tuple(SExpr((elm[0], elm[1]), no_range) for elm in grammar)
                    children = [ 'synth-fun', name, params, res_ty, SExpr(non_terms, no_range), grammar ]
        return SExpr(s=tuple(children), range=sexpr.range)

    def __call__(self, input, output):
        sexprs = list(tinysexpr.read(input))
        nullary = frozenset(s[1] for s in sexprs
                            if isinstance(s, SExpr) and len(s) > 2
                            and s[0] in ('synth-fun', 'define-fun', 'declare-fun')
                            and isinstance(s[2], SExpr) and len(s[2]) == 0)
        for s in sexprs:
            print(self.rewrite(s, nullary), file=output)

def _nullary_apps_to_symbols(sexpr: Any, nullary: frozenset[str]) -> Any:
    """(f) -> f for the functions f in nullary (SMT-LIB has no empty applications)."""
    if not isinstance(sexpr, SExpr):
        return sexpr
    if len(sexpr) == 1 and isinstance(sexpr[0], str) and sexpr[0] in nullary:
        return sexpr[0]
    return SExpr(s=tuple(_nullary_apps_to_symbols(s, nullary) for s in sexpr), range=sexpr.range)