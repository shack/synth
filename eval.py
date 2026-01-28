from pathlib import Path

import datetime
import re
from typing import Annotated

import tyro

from eval.util import ComparisonExperiment, Cvc5SygusRun, SygusRun

SYGUS_DIR = 'resources/sygus_sel'

class Sygus(ComparisonExperiment):
    def __init__(self, iterations: int, timeout=5*60):
        benches = sorted(Path(SYGUS_DIR).glob('**/*.sl'))
        self.exp = {
            b: {
                'std': [
                    SygusRun(bench=b, iteration=i, timeout=timeout)
                    for i in range(iterations)
                ],
                'no-opt': [
                    SygusRun(bench=b, iteration=i, timeout=timeout,
                             synth='synth:len-cegis',
                             synth_flags='--synth.no-opt-no-dead-code --synth.no-opt-cse --synth.no-opt-const --synth.no-opt-commutative --synth.no-opt-insn-order')
                    for i in range(iterations)
                ],
                'cvc5': [
                    Cvc5SygusRun(bench=b, iteration=i, timeout=timeout)
                    for i in range(iterations)
                ],
            } for b in benches
        }

class SygusNoSplit(ComparisonExperiment):
    def __init__(self, iterations: int, timeout=5*60):
        benches = sorted(b for b in Path(SYGUS_DIR).glob('**/*.sl') if
                         sum(1 for l in open(b)) > 1)
        self.exp = {
            b: {
                'std': [
                    SygusRun(bench=b, iteration=i, timeout=timeout)
                    for i in range(iterations)
                ],
                'split': [
                    SygusRun(bench=b, iteration=i, timeout=timeout,
                             flags='--no-fuse-constraints')
                    for i in range(iterations)
                ],
            } for b in benches
        }

class SygusNoDownscale(ComparisonExperiment):
    def __init__(self, iterations: int, timeout=5*60):
        benches = sorted(b for b in Path(SYGUS_DIR).glob('**/*.sl') if
                         any(re.search(r'set-logic\s+BV', l) for l in open(b)))
        self.exp = {
            b: {
                'std': [
                    SygusRun(bench=b, iteration=i, timeout=timeout)
                    for i in range(iterations)
                ],
                'downscale': [
                    SygusRun(bench=b, iteration=i, timeout=timeout,
                             flags='--bv-downscale 4')
                    for i in range(iterations)
                ],
            } for b in benches
        }

EXPERIMENTS = { Sygus, SygusNoSplit, SygusNoDownscale }

def exp_cons(sets: tuple[str, ...]) -> list['type']:
    return [ s for s in EXPERIMENTS if s.__name__ in sets ]

def run(
    dir: Path,
    bench: Annotated[list['type'], tyro.conf.arg(constructor=exp_cons)],
    trials: int = 1,
    timeout: int = 5*60,
    dry: bool = False
):
    stats_dir = dir / Path('stats')
    if not dry:
        if not stats_dir.exists():
            stats_dir.mkdir(parents=True)
        elif not stats_dir.is_dir():
            raise NotADirectoryError(f'{stats_dir} exists and is not a directory')

    max_time = 0
    to_run = []
    print(bench)
    for exp in bench:
        for run in exp(trials, timeout).to_run(stats_dir):
            to_run.append(run)
            max_time += (run.timeout if run.timeout else 0)

    delta = datetime.timedelta(seconds=max_time)

    n_to_run = len(to_run)
    for run in to_run:
        if dry:
            stats_file = run.get_results_filename(stats_dir)
            print(run.get_cmd(stats_file))
        else:
            print(f'to go: #{n_to_run} ({delta}) {run} ', end='')
            stats = run.run(stats_dir)
            print(stats['status'], '{:.3f}'.format(stats.get('wall_time', 0) / 1e9))
            n_to_run -= 1
            delta -= datetime.timedelta(seconds=(run.timeout if run.timeout else 0))

def eval(
    dir: Path,
    bench: Annotated[list['type'], tyro.conf.arg(constructor=exp_cons)],
    trials: int = 3,
    timeout = 5*60,
):
    stats_dir = dir / Path('stats')
    data_dir = dir / Path('data')
    data_dir.mkdir(parents=True, exist_ok=True)
    for b in bench:
        print(b)
        b(trials, timeout).evaluate(stats_dir, data_dir)
        # for exp in b(trials, timeout).exp:
        #     print(exp)
        #     exp.evaluate(stats_dir, data_dir)

if __name__ == '__main__':
    tyro.extras.subcommand_cli_from_dict(
        {
            "run": run,
            "eval": eval,
        }
    )