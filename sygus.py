from pathlib import Path

from typing import Annotated
import tinysexpr
import tyro
import json

from dataclasses import dataclass, field

from tyro.conf import UseCounterAction

from synth.abstraction import AbstractLenCegis
from synth.abstraction.bv import LowerBitsAbstraction
from synth.spec import Constraint, Problem
from synth.synth_n import LenCegis, Opt

from z3 import *

from synth.util import Debug

from util.convert import OldToNew, NewToOld
from util.size import solution_sizes
from util.sygus import SyGuSError, sygus_read_problem

@dataclass(frozen=True)
class Synth:
    """Solve a SyGuS task."""

    file: tyro.conf.PositionalRequiredArgs[Path]
    """SyGuS input file."""

    stats: Path | None = None
    """File to record statistics."""

    opt: set[Opt] = field(default_factory=lambda: set(Opt))
    """Optimizations constraints."""

    verbose: Annotated[UseCounterAction[int], tyro.conf.arg(aliases=["-v"])] = 0
    """Show statistics while solving."""

    size_range: tuple[int, int] = (0, 20)
    """Range of program sizes on which synthesis is tried."""

    fuse_constraints: bool = False
    """Fuse all synthesis constraints to a single conjunct."""

    flatten_grammar: bool = False
    """Remove syntactical structure and have only one non-terminal per sort."""

    opt_grammar: bool = True
    """Inline certain rules."""

    print_problem: bool = False
    """Print the problem."""

    bv_abstract: bool = False
    """Use abstraction for bit-vector problems."""

    def __call__(self):
        problem = sygus_read_problem(self.file)
        if problem is None:
            print(f'could not read problem {self.file}')
            return 1

        fuse        = self.fuse_constraints
        constraints = problem.constraints
        funcs       = problem.funcs

        if self.flatten_grammar:
            funcs = { name: f.flatten_grammar() for name, f in funcs.items() }
        if self.opt_grammar:
            funcs = { name: f.optimize_grammar() for name, f in funcs.items() }
        if len(funcs) > 1:
            fuse = True
        if fuse:
            c = Constraint(
                And(c.phi for c in problem.constraints),
                params=next(iter(problem.constraints)).params,
                function_applications={k: v for d in problem.constraints for k, v in d.function_applications.items()}
            )
            constraints = [c]

        problem = Problem(
            constraints=constraints,
            funcs=funcs,
            theory=problem.theory,
            name=problem.name)

        if self.print_problem:
            print(problem)

        params = {}
        params['opt'] = self.opt
        params['size_range'] = self.size_range
        debug_what = []
        if self.verbose >= 1:
            debug_what += [ 'len', 'cex', 'abs' ]
        if self.verbose >= 2:
            debug_what += [ 'prg' ]
        params['debug'] = Debug(what='|'.join(debug_what))

        # check
        max_width = problem.get_max_used_bit_width()
        if self.bv_abstract and max_width > 0:
            log2_max_width = math.ceil(math.log2(max_width))
            widths = [ 2 ** i for i in range(2, log2_max_width) ]
            params['abstractions'] = [
                LowerBitsAbstraction(bit_width=w) for w in widths
            ]
            sy = AbstractLenCegis(**params)
        else:
            sy = LenCegis(**params)

        prgs, synth_stats = sy.synth_prgs(problem)
        if self.stats:
            with open(self.stats, 'w') as f:
                json.dump(synth_stats, f, indent=4)

        if prgs is None:
            print('fail')
            return 0
        else:
            print('(')
            for name, p in prgs.items():
                p = p.copy_propagation().dce()
                print(p.sexpr(name, sep='\n\t'))
            print(')')
            return 0


@dataclass(frozen=True)
class Size:
    """Print the size of a SyGuS solution."""

    file: tyro.conf.PositionalRequiredArgs[Path]
    """File with SyGuS solution (define-fun)."""

    count_const: bool = False
    """Count a constant as 1 or 0."""

    def __call__(self):
        with open(self.file) as f:
            for sexpr in tinysexpr.read(f):
                for name, sz in solution_sizes(sexpr, self.count_const):
                    print(f'({name} {sz})')
        return 0

@dataclass(frozen=True)
class Show:
    """Print the internal data-structure for a SyGuS problem."""

    file: tyro.conf.PositionalRequiredArgs[Path]

    def __call__(self):
        if p := sygus_read_problem(self.file):
            print(p)
            return 0
        return 1

@dataclass(frozen=True)
class Syntax:
    """Check the syntax of a SyGuS file."""

    file: tyro.conf.PositionalRequiredArgs[Path]

    def __call__(self):
        try:
            sygus_read_problem(self.file)
            return 0
        except SyGuSError as e:
            print(e)
            return 1

@dataclass(frozen=True)
class Convert:
    """Convert SyGuS files."""

    conv: OldToNew | NewToOld
    """Conversion."""

    file: tyro.conf.PositionalRequiredArgs[Path]
    """The input file."""

    output: Path | None = None
    """Output file. Stdout if not provided."""

    def __call__(self):
        inp = open(self.file, 'rt') if self.file else sys.stdin
        out = open(self.output, 'wt') if self.output else sys.stdout
        return self.conv(inp, out)

if __name__ == '__main__':
    try:
        sys.exit(tyro.cli(Synth | Syntax | Show | Size | Convert, config=(tyro.conf.CascadeSubcommandArgs,))())
    except FileNotFoundError as e:
        print(str(e), file=sys.stderr)
        sys.exit(1)
    except SyGuSError as e:
        print(str(e), file=sys.stderr)
        sys.exit(2)