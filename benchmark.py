#! /usr/bin/env python3

import json
import enum
import re

from typing import Optional
from dataclasses import dataclass, field

from z3 import *

import tyro

from synth.spec import Task
from synth import SYNTHS
from synth import synth_n

from bench.util import Bench, timeout
from bench import base, hackdel_light, hackdel_heavy, random, hackdel_sygus, hackdel_sygus_own_spec, rulesynth

# list benchmark sets here
BENCH_SETS = base.Base \
           | rulesynth.RulerBool \
           | rulesynth.RulerBitVec \
           | rulesynth.Herbie \
           | random.Random \
           | hackdel_light.HackdelLight \
           | hackdel_heavy.HackdelHeavy \
           | hackdel_sygus_own_spec.HackdelSygusOwnSpec \
           | hackdel_sygus.HackdelSygus

class ConstMode(enum.Enum):
    EMPTY     = enum.auto()
    """Like FREE but take into account if the benchmark specifies no constants."""
    FREE      = enum.auto()
    """The synthesizer has to find constants on its own."""
    COUNT     = enum.auto()   # give an upper bound on how many constants can be used
    """Take into account if the benchmark specifies an upper bound on the total number of constants."""
    SET       = enum.auto()   # give the set of constants
    """Take into account if the benchmark specifies a set of constants."""
    SET_COUNT = enum.auto()   # give the set of constants and an upper bound on how many can be used
    """SET and COUNT."""

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
    """Run a benchmark set."""

    set: BENCH_SETS
    """Benchmark set"""

    synth: SYNTHS = field(kw_only=True, default=synth_n.LenCegis())
    """Synthesizer"""

    tests: Optional[str] = None
    """Regular expression of tests to include (all if '')"""

    exclude: Optional[str] = None
    """Regular expression of tests to exclude (none if '')"""

    stats: Optional[str] = None
    """Write file with statistics"""

    graph: bool = False
    """Write a dot file with the ddg of the program"""

    timeout: Optional[int] = None
    """Set a timeout in seconds (0 for none)"""

    difficulty: int = 0
    """Set difficulty level"""

    op_freq: bool = True
    """Use specified operator frequencies."""

    print_prg: bool = False
    """Print the synthesized program."""

    print_desc: bool = False
    """Print benchmark description."""

    const_mode: ConstMode = ConstMode.EMPTY
    """Const mode. (FREE means synthesize constants)"""

    def bench_to_task(self, bench: Bench):
        # if entire library is not specified, use the given operator library
        all_ops = bench.all_ops if not bench.all_ops is None else bench.ops
        # if operator library does not specify counts, set all to maximum
        # or if exact operator count is not enabled, set operator count to maximum
        if type(bench.ops) == list or type(bench.ops) == set or not self.op_freq:
            ops = { op: None for op in bench.ops }
        else:
            ops = dict(bench.ops)
        # figure out operator library based on difficulty
        rest_ops = [ op for op in all_ops if op not in ops ]
        for o in rest_ops[:self.difficulty]:
            ops[o] = None

        consts = bench.consts
        m = lambda: sum(f for f in consts.values())
        s = lambda: consts
        match self.const_mode:
            case ConstMode.EMPTY:
                if not consts is None and len(consts) == 0:
                    max_const = 0
                    const_map = {}
                else:
                    max_const = None
                    const_map = None
            case ConstMode.FREE:
                max_const = None
                const_map = None
            case ConstMode.COUNT:
                assert not consts is None, 'COUNT mode requires consts to be set'
                max_const = m()
                const_map = None
            case ConstMode.SET:
                assert not consts is None, 'SET mode requires consts to be set'
                max_const = None
                const_map = s()
            case ConstMode.SET_COUNT:
                assert not consts is None, 'SET_COUNT mode requires consts to be set'
                max_const = m()
                const_map = s()

        return Task(spec=bench.spec, ops=ops, max_const=max_const,
                    const_map=const_map, theory=bench.theory)

    def _exec_bench(self, b: Bench):
        name = b.get_name()
        desc = f' ({b.desc})' if self.print_desc and b.desc else ''
        print(f'{name}{desc}: ', end='', flush=True)
        task = self.bench_to_task(b)
        # reset_params()
        prgs, stats = self.synth.synth_prgs(task)
        assert prgs and len(prgs) == 1
        prg = prgs.get(b.spec.name)
        dce = prg.copy_propagation().dce() if prg is not None else None
        # total_time = sum(s['time'] for s in stats)
        total_time = stats['time']
        print(f'{total_time / 1e9:.3f}s', end='')
        if not prg is None:
            print(f', len: {len(prg)}, dce: {len(dce)}')
        else:
            print()
        if self.graph:
            with open(f'{name}.dot', 'w') as f:
                prg.print_graphviz(f)
        if self.print_prg:
            print(prg.to_string(sep='\n') if not prg is None else 'no program found')
            if prg != dce:
                print('dead code eliminated:')
                print(dce.to_string(sep='\n'))
            print('')
        return total_time, stats

    def exec(self):
        # iterate over all methods in this class that start with 'test_'
        exclude = re.compile(self.exclude if self.exclude else "^$")
        include = re.compile(self.tests   if self.tests   else ".*")
        all_stats = {}

        total_time = 0
        for name in sorted(name for name in dir(self.set) if name.startswith('test_')):
            for bench in getattr(self.set, name)():
                name = bench.get_name()
                if include.match(name) and not exclude.match(name):
                    with timeout(self.timeout):
                        try:
                            time, stats = self._exec_bench(bench)
                            total_time += time
                            all_stats[name] = stats
                        except TimeoutError:
                            total_time += self.timeout
                            print('timeout')
                if not self.stats is None:
                    with open(self.stats, 'w') as f:
                        json.dump(all_stats, f, indent=4)
        print(f'total time: {total_time / 1e9:.3f}s')

@dataclass(frozen=True)
class List:
    """List all available benchmarks in a benchmark set."""

    set: BENCH_SETS
    """Benchmark set"""

    def exec(self):
        for name in sorted(name for name in dir(self.set) if name.startswith('test_')):
            for bench in getattr(self.set, name)():
                print(bench.get_name())


if __name__ == "__main__":
    args = tyro.cli(Run | List)
    args.exec()