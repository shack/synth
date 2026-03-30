from pathlib import Path

import datetime
import re
from typing import Annotated

import tyro

from eval.util import *

SYGUS_DIR = 'resources/sygus_sel'

no_opt = lambda i, t, b: SygusRun(bench=b, iteration=i, timeout=t, name='no_opt',
                                  synth_flags=['--synth.no-opt-no-dead-code',
                                               '--synth.no-opt-cse',
                                               '--synth.no-opt-const',
                                               '--synth.no-opt-commutative',
                                               '--synth.no-opt-insn-order'])

fuse = lambda i, t, b: SygusRun(bench=b, iteration=i, timeout=t, name='fuse',
                                flags='--fuse-constraints')

class Sygus(Experiment):
    def __init__(self, iterations: int, timeout=5*60):
        benches = sorted(Path(SYGUS_DIR).glob('**/*.sl'))
        super().__init__(iterations, timeout, benches, {
                'std': SygusRun,
                'no-opt': no_opt,
                'cvc5': Cvc5SygusRun,
        })

class SygusFuse(Experiment):
    def __init__(self, iterations: int, timeout=5*60):
        benches = sorted(b for b in Path(SYGUS_DIR).glob('**/*.sl') if
                         sum(1 for _ in open(b)) > 1)
        super().__init__(iterations, timeout, benches, {
            'std': SygusRun,
            'fuse': fuse,
        })

class Simple(Experiment):
    def __init__(self, iterations: int, timeout=5*60):
        benches = sorted(b for b in Path('resources/simple').glob('**/*.sl'))
        super().__init__(iterations, timeout, benches, {
            'std': SygusRun,
            'no-opt': no_opt,
            'fuse': fuse,
            'cvc5': Cvc5SygusRun,
        })

EXPERIMENTS = { Sygus, SygusFuse, Simple }

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
    trials: int = 1,
    timeout = 5*60,
):
    results = {
        'time': aggregate_wall_time,
        'size': aggregate_result_size,
    }
    stats_dir = dir / Path('stats')
    data_dir = dir / Path('data')
    data_dir.mkdir(parents=True, exist_ok=True)
    for Exp in bench:
        exp: Experiment = Exp(trials, timeout)
        for name, aggregate in results.items():
            with open(data_dir / f'{exp.get_name()}-{name}.txt', 'wt') as f:
                format_by_bench_row_competitor_col(f, exp.get_aggregated_results(stats_dir, aggregate))


if __name__ == '__main__':
    tyro.extras.subcommand_cli_from_dict(
        {
            "run": run,
            "eval": eval,
        }
    )