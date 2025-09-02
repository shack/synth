from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional, Dict, Any
from functools import cache

import os
import json
import subprocess
import time
import datetime
import tempfile
import shlex

import tyro

@cache
def get_commit():
    return subprocess.check_output('git rev-parse HEAD', shell=True).decode('utf-8').strip()

@dataclass(frozen=True)
class Run:
    set: str
    bench: str
    synth: str
    iteration: int
    timeout: Optional[int]
    solver: Optional[str] = 'external-z3'
    run_opts: Dict[str, Any] = field(default_factory=dict)
    set_opts: Dict[str, Any] = field(default_factory=dict)
    syn_opts: Dict[str, Any] = field(default_factory=dict)

    def prepare_opts(opts, prefix=None):
        prefix = f'{prefix}.' if prefix else ''
        for k, v in opts.items():
            if isinstance(v, bool):
                yield f'--{prefix}' + ('' if v else 'no-') + k
            else:
                yield f'--{prefix}{k} {v}'

    def get_args(self):
        run_opts = ' '.join(Run.prepare_opts(self.run_opts))
        set_opts = ' '.join(Run.prepare_opts(self.set_opts, prefix='set'))
        syn_opts = ' '.join(Run.prepare_opts(self.syn_opts, prefix='synth'))
        return f'--tests {self.bench} {run_opts} set:{self.set} {set_opts} synth:{self.synth} {syn_opts} synth.solver:{self.solver}'

    def get_results_filename(self, output_dir: Path):
        name = self.get_args().replace(' ', '_').replace('--', '') + f'{self.iteration:04d}.json'
        return output_dir / Path(name)

    def result_file_exists(self, output_dir: Path):
        return self.get_results_filename(output_dir).exists()

    def read_result(self, output_dir: Path):
        assert self.result_file_exists(output_dir)
        with open(self.get_results_filename(output_dir), 'rt') as f:
            return json.load(f)

    def read_stats(self, stats_file: Path):
        with open(stats_file, 'rt') as f:
            return json.load(f)

    def get_cmd(self, stats_file: Path):
        args = self.get_args()
        return f'python benchmark.py run --stats {stats_file} {args}'

    def run(self, output_dir: Path):
        result_file = self.get_results_filename(output_dir)
        with tempfile.NamedTemporaryFile(suffix='.json') as f:
            print(f'Run: {self} {f.name}')
            cmd = self.get_cmd(f.name)
            args = shlex.split(cmd)
            try:
                start = time.perf_counter_ns()
                p = subprocess.run(args, timeout=self.timeout, check=True,
                                   capture_output=True, text=True)
                duration = (time.perf_counter_ns() - start)
                # if p.returncode != 0:
                #     raise Exception(f'Non-zero exit code {p.returncode}: {p.stdout} {p.stderr}')
                stats = {
                    'timeout': False,
                    'wall_time': duration,
                    'output': p.stdout,
                    'stats': self.read_stats(Path(f.name)),
                }
            except subprocess.TimeoutExpired as e:
                stats = { 'timeout': True, 'wall_time': self.timeout * 1_000_000_000 }
            except Exception as e:
                stats = {}
                print(f'Error {e} in {cmd}', file=os.sys.stderr)
        if stats:
            assert output_dir.exists() and output_dir.is_dir()
            with open(result_file, 'wt') as f:
                json.dump(stats, f, indent=4)

    def dispatch(self, pool, output_dir: Path):
        pool.apply_async(self.run, (output_dir, ))

class Experiment:
    def get_name(self):
        return self.__class__.__name__

    def get_output_filename(self, output_dir: Path, suffix=''):
        return output_dir / Path(f'{self.get_name()}{suffix}.txt')

    def map(self, f):
        def _map(exp, f):
            match exp:
                case dict():
                    return { k: _map(v, f) for k, v in exp.items() }
                case list():
                    return [ _map(e, f) for e in exp ]
                case Run():
                    return f(exp)
        return _map(self.exp, f)

    def runs(self):
        def _iter(exp):
            match exp:
                case dict():
                    for v in exp.values():
                       yield from _iter(v)
                case list():
                    for e in exp:
                        yield from _iter(e)
                case Run():
                    yield exp
        yield from _iter(self.exp)

    def to_run(self, output_dir: Path):
        for run in self.runs():
            if not run.result_file_exists(output_dir):
                yield run

class ComparisonExperiment(Experiment):
    def evaluate(self, stats_dir: Path, output_dir: Path, width=16):
        output_file = self.get_output_filename(output_dir)
        with open(output_file, 'wt') as f:
            get_wall_time = lambda t: t['wall_time'] / 1_000_000_000
            res = self.map(lambda r: r.read_result(stats_dir))
            heads = [f'{'bench':{width}}'] + list(next(iter(res.values())).keys())
            print(' '.join(f'{h:>{width}}' for h in heads), file=f)
            for bench, competitors in res.items():
                times = [ sum(map(get_wall_time, trials)) / len(trials) for trials in competitors.values() ]
                times = ' '.join(f'{t:>{width}.5f}' for t in times)
                print(f'{bench:{width}} {times}', file=f)

def run(
    dir: Path,
    trials: int = 3,
):

    stats_dir = dir / Path('stats')
    if not stats_dir.exists():
        stats_dir.mkdir(parents=True)
    elif not stats_dir.is_dir():
        raise NotADirectoryError(f'{stats_dir} exists and is not a directory')

    exps = experiments(trials)

    max_time = 0
    to_run = []
    for exp in exps:
        for run in exp.to_run(stats_dir):
            to_run.append(run)
            max_time += (run.timeout if run.timeout else 0)

    delta = datetime.timedelta(seconds=max_time)

    n_to_run = len(to_run)
    for run in to_run:
        print(f'experiments to run: {n_to_run}, max time: {delta}')
        run.run(stats_dir)
        n_to_run -= 1
        delta -= datetime.timedelta(seconds=(run.timeout if run.timeout else 0))

def eval(
    dir: Path,
    trials: int = 3,
):
    stats_dir = dir / Path('stats')
    data_dir = dir / Path('data')
    data_dir.mkdir(parents=True, exist_ok=True)
    exps = experiments(trials)
    for exp in exps:
        exp.evaluate(stats_dir, data_dir)


hackdel_light = ('hackdel-light', [ f'p{i:02d}' for i in range(1, 19) ])

# hackdel-light (10min timeout, —difficulty 100, —no-op-freq, —set.bit-width 8): len-cegis, brahma-iterate, brahma-paper, brahma-exact
class SynthComparison(ComparisonExperiment):
    def __init__(self, iterations, timeout=10*60, set=hackdel_light):
        set, benches = set

        run_opts = {
            'difficulty': 100,
            'op-freq': False,
            'const-mode': 'FREE',
        }

        synths = [
            'len-cegis',
            'brahma-iterate',
            'brahma-paper',
        ]

        self.exp = {
            b: {
                s: [
                    Run(set=set, bench=b, synth=s, iteration=i,
                        timeout=timeout,
                        run_opts=run_opts)
                    for i in range(iterations)
                ] for s in synths
            } for b in benches
        }

# hackdel-light (timeout ?): downscale from 16, 32, 64 mit const cegis
class Downscale(ComparisonExperiment):
    def __init__(self, iterations, timeout=10*60, set=hackdel_light):
        set, benches = set

        run_opts = {
            'difficulty': 100,
            'op-freq': False,
            'const-mode': 'FREE',
        }

        bit_widths = [16, 32, 64]

        self.exp = {
            b: {
                w: [
                    Run(set=set, bench=b, synth='downscale', iteration=i, timeout=timeout,
                        run_opts=run_opts,
                        set_opts={'bit-width': w},
                        syn_opts={'solver': 'external-z3'})
                    for i in range(iterations)
                ] for w in bit_widths
            } for b in benches
        }

# hackdel-light (timout 10min): len-cegis. different solvers (Yices, etc.) 8-bit
class Solvers(ComparisonExperiment):
    def __init__(self, iterations, timeout=10*60, set=hackdel_light):
        try:
            with open('solvers.json', 'rt') as f:
                solvers = json.load(f)
        except Exception as e:
            print(f'Could not load solvers.json: {e}')
            return {}

        set, benches = set

        run_opts = {
            'difficulty': 100,
            'op-freq': False,
            'const-mode': 'FREE',
        }

        self.exp = {
            b: {
                s: [
                    Run(set=set, bench=b, synth='len-cegis', iteration=i, timeout=timeout,
                        run_opts=run_opts,
                        syn_opts={'solver': s, 'solver.path': os.path.expandvars(path)})
                    for i in range(iterations)
                ] for s, path in solvers.items()
            } for b in benches
        }

def experiments(trials):
    return [
        SynthComparison(trials),
        Downscale(trials),
        Solvers(trials),
    ]


# hackdel-light opt: len/opcost/depth, 8-bit, z3opt vs linsearch
# ruler-bool, ruler-bv, herbie (timeout 10min, —difficulty 100, —no-op-freq, 8bit), len-cegis vs brahma-iterate (bei letzterem kommt vermutlich nix vernünftiges).
# SyGuS (10min timeout): len-cegis, CVC5, brahma-iterate, brahma-paper
# hackdel-heavy (timeout 6h, difficulty 100, —no-op-freq, 8bit): len-cegis, brahma-paper
# hackdel-heavy (timeout 6h, 8bit): len-cegis, brahma-exact

if __name__ == '__main__':
    tyro.extras.subcommand_cli_from_dict(
        {
            "run": run,
            "eval": eval,
        }
    )
