#! /usr/bin/env python3
from dataclasses import dataclass
from typing import Optional, List

import pathlib

from z3 import *
import tyro

from synth.oplib import Bl
from synth import SYNTHS, spec
from synth.spec import Spec, Task, create_bool_func
from synth.synth_n import LenCegis

def read_pla(file, name='func', outputs=None, debug=0):
    for n, line in enumerate(file):
        line = line.strip().split('#')[0]
        if (have_o := line.startswith(".o ")) or line.startswith(".ob "):
            if have_o:
                num_outs = int(line.split()[1])
                names    = [ f'y{i}' for i in range(num_outs) ]
            else:
                names    = line.split()[1:]
                num_outs = len(names)
            if outputs is None:
                outputs = set(range(num_outs))
            else:
                assert all(i < num_outs for i in outputs), \
                           f'output index out of range: {i} >= {num_outs}'
            outs    = [ Bool(names[i]) for i in range(num_outs) ]
            clauses = [ ([], []) for _ in range(num_outs) ]
            continue
        elif line.startswith(".i "):
            num_vars = int(line.split()[1])
            ins      = [ Bool(f'x{i}') for i in range(num_vars) ]
            continue
        elif line.startswith(".ilb "):
            in_names = line.split()[1:]
            num_vars = len(in_names)
            ins      = [ Bool(n) for n in in_names ]
            continue
        elif line.startswith(".e"):
            break
        elif line.startswith(".") or line.startswith('#') or line == "":
            continue

        assert num_vars != -1, "PLA needs to contain number of inputs"

        constraint, result = line.split()

        clause = []
        if debug >= 1 and n % 1000 == 0:
            print(f"reading clause {n}")

        for param, literal in zip(ins, constraint):
            match literal:
                case "-":
                    continue
                case "1":
                    clause.append(param)
                case "0":
                    clause.append(Not(param))
                case _:
                    assert False, "invalid character in constraint"

        for i, literal in enumerate(result):
            if not i in outputs:
                continue
            cl, dl = clauses[i]
            match literal:
                case "0":
                    continue # 0-lines are also often omitted.
                case "1" | "4":
                    cl.append(And(clause))
                case "-" | "2":
                    dl.append(And(clause))
                case _:
                    assert False, "unknown result in clause"

    precond = And([ Not(Or(dl)) \
                    for i, (_, dl) in enumerate(clauses) \
                    if i in outputs ])
    spec    = And([ res == Or(cl) \
                    for i, (res, (cl, _)) in enumerate(zip(outs, clauses)) \
                 if i in outputs ])
    outs = [ o for i, o in enumerate(outs) if i in outputs ]
    return Spec(name, spec, outs, ins, precond=precond)

_avail_ops = { name: op for name, op in vars(Bl).items() if isinstance(op, spec.Func) }
_avail_ops_names = ', '.join(_avail_ops.keys())
_default_ops = 'not1,and2,or2,xor2'

@dataclass(frozen=True)
class File:
    """Read boolean functions from a file, one per line."""
    file: pathlib.Path
    """The file."""

    def get_functions(self):
        with open(self.file, 'r') as f:
            return [ create_bool_func(line.strip()) for line in f.readlines() ]

@dataclass(frozen=True)
class Pla:
    """Read a espresso pla description from a file."""
    file: pathlib.Path
    """The file."""
    outs: Optional[str] = None
    """Output variables to consider."""
    debug: bool = False
    """Enable diagnostic output."""

    def get_functions(self):
        outputs = set(int(i) for i in args.outs.split(',')) if self.outs else None
        with open(self.file, 'r') as f:
            return [ read_pla(f, name=str(self.file),
                              outputs=outputs, debug=self.debug) ]

@dataclass(frozen=True)
class Func:
    """Specify boolean function to synthesize on the command line"""
    func: str

    def get_functions(self):
        return [ create_bool_func(self.func) ]

@dataclass(frozen=True)
class Settings:
    op: File | Pla | Func
    synth: SYNTHS = LenCegis()

    consts: int = 1
    """The maximum number of constants allowed."""

    ops: str = _default_ops
    """The operators to synthesize with."""

    stats: bool = False
    """Dump statistics about synthesis to a JSON file."""

    graph: bool = False
    """Dump a .dot graph of the synthesized function."""

if __name__ == "__main__":
    args = tyro.cli(Settings)
    functions = args.op.get_functions()

    ops = { }
    for name in args.ops.split(','):
        match name.split(':'):
            case [name]:
                ops[_avail_ops[name]] = None
            case [name, freq]:
                ops[_avail_ops[name]] = int(freq)

    next = ''
    for spec in functions:
        func = spec.name
        print(f'{next}{func}:')
        task = Task(spec, ops, args.consts, None, 'QF_BV')
        prg, stats = args.synth.synth(task)
        print(prg)
        total_time = sum(s['time'] for s in stats)
        print(f'synthesis time: {total_time / 1e9:.3f}s')
        if args.stats:
            import json
            with open(f'{func}.stats.json', 'w') as f:
                json.dump(stats, f, indent=4)
        if prg and args.graph:
            with open(f'{func}.dot', 'w') as f:
                prg.print_graphviz(f)
        next = '\n'