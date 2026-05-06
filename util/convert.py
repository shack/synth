from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

import tinysexpr
from tinysexpr import SExpr

@dataclass(frozen=True)
class NewToOld:
    remove_type_underscores: bool = True
    """(_ type ...) -> (type ...)"""

    remove_non_terminal_list: bool = True
    """Remove the list of non-terminals right after the return type of a synth-fun."""

    def rewrite(self, sexpr: Any) -> SExpr:
        if not isinstance(sexpr, SExpr):
            return sexpr
        children = [ self.rewrite(s) for s in sexpr ]
        match children:
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
    def rewrite(self, sexpr: Any) -> SExpr:
        if not isinstance(sexpr, SExpr):
            return sexpr
        children = [ self.rewrite(s) for s in sexpr ]
        match children:
            case ['BitVec', n]:
                children = ['_', 'BitVec', n]
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
        for s in tinysexpr.read(input):
            print(self.rewrite(s), file=output)