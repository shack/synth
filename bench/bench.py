#! /usr/bin/env python3

import json
import enum

from typing import Optional
from dataclasses import dataclass

from z3 import *

import tyro

import context
from synth.spec import Task
from synth import synth_n

from util import Bench

import base, hackdel

# list benchmark sets here
BENCH_SETS = base.Base | hackdel.Hackdel
# list synthesizers here
SYNTHS     = synth_n.LenCegis | synth_n.LenFA

class ConstMode(enum.Enum):
    NONE      = enum.auto()   # like free, but take the hint if consts are disabled
    FREE      = enum.auto()   # no constraint on constants
    COUNT     = enum.auto()   # give an upper bound on how many constants can be used
    SET       = enum.auto()   # give the set of constants
    SET_COUNT = enum.auto()   # give the set of constants and an upper bound on how many can be used

    def __str__(self):
        return self.name

    @staticmethod
    def from_string(s):
        try:
            return ConstMode[s]
        except KeyError:
            raise ValueError()

@dataclass(frozen=True)
class Run:
    set: BENCH_SETS
    """Benchmark set"""

    synth: SYNTHS
    """Synthesizer"""

    tests: Optional[str] = None
    """Comma-separated list of tests (all if '')"""

    stats: bool = False
    """Write file with statistics"""

    graph: bool = False
    """Write a dot file with the ddg of the program"""

    timeout: int = 0
    """Set a timeout in seconds (0 for none)"""

    difficulty: int = 0
    """Set difficulty level"""

    ignore_op_freq: False = 0
    """Ignore specified operator frequencies."""

    const_mode: ConstMode = ConstMode.NONE
    """Const mode. (NONE means synthesize constants)"""

    def bench_to_task(self, bench: Bench):
        # if entire library is not specified, use the given operator library
        all_ops = bench.all_ops if not bench.all_ops is None else bench.ops
        # if operator library does not specify counts, set all to maximum
        # or if exact operator count is not enabled, set operator count to maximum
        if type(bench.ops) == list or type(bench.ops) == set or self.ignore_op_freq:
            ops = { op: None for op in bench.ops }
        else:
            ops = dict(bench.ops)
        # figure out operator library based on difficulty
        rest_ops = [ op for op in all_ops if op not in ops ]
        for o in rest_ops[:self.difficulty]:
            ops[o] = None

        consts = bench.consts
        m = lambda: sum(f for f in consts.values())
        s = lambda: { c for c in consts }
        match self.const_mode:
            case ConstMode.NONE:
                if not consts is None and len(consts) == 0:
                    max_const = 0
                    const_set = {}
                else:
                    max_const = None
                    const_set = None
            case ConstMode.FREE:
                max_const = None
                const_set = None
            case ConstMode.COUNT:
                assert not consts is None, 'COUNT mode requires consts to be set'
                max_const = m()
                const_set = None
            case ConstMode.SET:
                assert not consts is None, 'SET mode requires consts to be set'
                max_const = None
                const_set = s()
            case ConstMode.SET_COUNT:
                assert not consts is None, 'SET_COUNT mode requires consts to be set'
                max_const = m()
                const_set = s()

        return Task(spec=bench.spec, ops=ops, max_const=max_const, consts=const_set)

    def _exec_bench(self, b: Bench):
        name = b.name
        desc = f' ({b.desc})' if b.desc else ''
        print(f'{name}{desc}: ', end='', flush=True)
        task = self.bench_to_task(b)
        prg, stats = self.synth.synth(task)
        total_time = sum(s['time'] for s in stats)
        print(f'{total_time / 1e9:.3f}s')
        if self.stats:
            with open(f'{name}.json', 'w') as f:
                json.dump(stats, f, indent=4)
        if self.graph:
            with open(f'{name}.dot', 'w') as f:
                prg.print_graphviz(f)
        print(prg)
        dce = prg.dce() if prg is not None else None
        if prg != dce:
            print('dead code eliminated:')
            print(dce)
        return total_time

    def exec(self):
        # iterate over all methods in this class that start with 'test_'
        if self.tests is None:
            tests = [ name for name in dir(self.set) if name.startswith('test_') ]
        else:
            tests = [ 'test_' + s for s in self.tests.split(',') ]
        tests.sort()
        total_time = 0
        for name in tests:
            bench = getattr(self.set, name)()
            total_time += self._exec_bench(bench)
            print('')
        print(f'total time: {total_time / 1e9:.3f}s')

@dataclass(frozen=True)
class List:
    set: BENCH_SETS
    """Benchmark set"""

    def exec(self):
        for name in dir(self.set):
            if name.startswith('test_'):
                print(name)

if __name__ == "__main__":
    # Z3 settings
    set_option("sat.random_seed", 0);
    set_option("smt.random_seed", 0);
    set_option("parallel.enable", True);
    set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

    args = tyro.cli(Run | List)
    args.exec()