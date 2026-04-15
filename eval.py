from pathlib import Path

import enum

import tyro

from eval.util import *

# defaults

BASE_DIR: Path = Path('resources')
TRIALS: int = 1
TIMEOUT: int = 5*60

# Benchmark sets

def bench_file(subdir, name):
    return BASE_DIR / subdir / f'{name}.sl'

def all_files_in(subdir: str):
    return sorted((BASE_DIR / subdir).glob('*.sl'))

def from_dirs(*dirs):
    return { d: all_files_in(d) for d in dirs }

select = {
}

Benchmarks = enum.Enum('Benchmarks',
                       from_dirs('simple', 'sygus_sel',
                                 'crypto', 'lobster',
                                 'deobfusc'))

# Competitors

type RunFactory = Callable[[int, int, str], Run]

class Competitors(enum.Enum):
    @enum.member
    def std(iteration: int, timeout: int, bench: str):
        return SygusRun(iteration, timeout, bench, name='std')

    @enum.member
    def no_opt(iteration: int, timeout: int, bench: str):
        return SygusRun(iteration, timeout, bench, name='no_opt',
                        synth_flags=['--synth.no-opt-no-dead-code',
                                    '--synth.no-opt-cse',
                                    '--synth.no-opt-const',
                                    '--synth.no-opt-commutative',
                                    '--synth.no-opt-insn-order'])

    @enum.member
    def no_fuse(iteration: int, timeout: int, bench: str):
        return SygusRun(iteration, timeout, bench, name='no_opt',
                        synth_flags=['--no-fuse-constraints'])

    @enum.member
    def cvc5(iteration: int, timeout: int, bench: str):
        return ExternalSygusRun(iteration, timeout, bench, 'cvc5', '{bench}')


def eval_experiment(
    dir: Path,
    exp: Experiment
):
    results = {
        'time': aggregate_wall_time,
        'size': aggregate_result_size,
    }
    stats_dir = dir / Path('stats')
    data_dir = dir / Path('data')
    data_dir.mkdir(parents=True, exist_ok=True)
    for name, aggregate in results.items():
        with open(data_dir / f'{exp.get_name()}-{name}.txt', 'wt') as f:
            format_by_bench_row_competitor_col(f, exp.get_aggregated_results(stats_dir, aggregate))

def run_and_eval_experiments(dir: Path, dry: bool, exps: Sequence[Experiment]):
    run_experiments(dir, dry, exps)
    if not dry:
        for exp in exps:
            eval_experiment(dir, exp)

def experiments_from_selection(
    benchmark: list[Benchmarks],
    competitors: list[Competitors],
    trials: int,
    timeout: int):
    cs = { c.name: c.value for c in competitors }
    prefix = '-'.join(c.name for c in competitors)
    return [ Experiment(f'{prefix}_{b.name}', trials, timeout, b.value, cs) for b in benchmark ]

def selection(
    dir: Path,
    benchmarks: list[Benchmarks],
    competitors: list[Competitors],
    trials: int = TRIALS,
    timeout: int = TIMEOUT,
    dry: bool = False):
    experiments = experiments_from_selection(benchmarks, competitors, trials, timeout)
    run_and_eval_experiments(dir, dry, experiments)

def all():
    pass

if __name__ == '__main__':
    tyro.extras.subcommand_cli_from_dict(
        {
            "selection": selection,
        }
    )