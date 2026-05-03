from functools import partial
from pathlib import Path

import enum
import sys

import tyro

from eval.util import *

# defaults

DEFAULT_BENCHMARK_BASE_DIR   = Path('resources/sygus')
DEFAULT_COMPETITORS_BASE_DIR = Path('eval/competitors')
TRIALS: int = 1
TIMEOUT: int = 5*60

def all_dirs(base_dir: Path) -> list[Path]:
    if not base_dir.exists() or not base_dir.is_dir():
        return []
    return sorted([p for p in base_dir.iterdir() if p.is_dir()])

# Competitors

type RunFactory = Callable[[int, int, str], Run]

class Competitors(enum.Enum):
    @enum.member
    def std(iteration: int, timeout: int, bench: str):
        return SygusRun(iteration, timeout, bench, name='std')

    @enum.member
    def no_opt(iteration: int, timeout: int, bench: str):
        return SygusRun(iteration, timeout, bench, name='no_opt', flags='--opt')

    @enum.member
    def fuse(iteration: int, timeout: int, bench: str):
        return SygusRun(iteration, timeout, bench, name='fuse',
                        flags='--fuse-constraints')

    @enum.member
    def flatten(iteration: int, timeout: int, bench: str):
        return SygusRun(iteration, timeout, bench, name='flatten',
                        flags='--flatten-grammar')

def eval_experiment(
    dir: Path,
    exp: Experiment
):
    results = {
        'time': aggregate_wall_time,
        'size': aggregate_result_size,
    }
    data_dir = dir / Path('data')
    stats_dir = dir / Path('stats')
    stats_dir.mkdir(parents=True, exist_ok=True)
    for name, aggregate in results.items():
        with open(stats_dir / f'{exp.get_name()}-{name}.txt', 'wt') as f:
            format_by_bench_row_competitor_col(f, exp.get_aggregated_results(data_dir, aggregate))

@dataclass(frozen=True)
class Base:
    def get_experiments(self, settings: "Main", competitors: dict[str, RunFactory], prefix: str=None):
        if not prefix:
            prefix = '-'.join(competitors)
        benchmarks = { b.name: sorted(b.glob('*.sl')) for b in self.get_benchmarks(settings) }
        if sum(len(f) for f in benchmarks.values()) == 0:
            raise ValueError(f'benchmark set empty: {self.get_benchmarks(settings)}')
        return [ Experiment(f'{prefix}_{b}', settings.trials, settings.timeout,
                            files, competitors) for b, files in benchmarks.items() ]

@dataclass(frozen=True)
class WithBenchmarks(Base):
    benchmarks: list[str]

    def get_benchmarks(self, settings: "Main"):
        res = []
        for b in self.benchmarks:
            d = settings.base / b
            if not d.exists() or not d.is_dir():
                raise FileNotFoundError(f'benchmark directory {d} does not exist')
            res.append(d)
        return res

@dataclass(frozen=True)
class Opt(WithBenchmarks):
    def get_experiments(self, settings: "Main"):
        flags = {
            'd': 'DCE',
            'e': 'CSE',
            'c': 'CON',
            'm': 'COM',
            'o': 'ORD'
        }
        n_opts = len(flags)
        competitors = {}
        for mask in range(1 << n_opts):
            on = lambda i: ((1 << i) & mask) != 0
            name  = ''.join(f if on(i) else '-' for i, f in enumerate(flags))
            args = '--opt ' + ' '.join(f for i, f in enumerate(flags.values()) if on(i))
            competitors[name] = partial(SygusRun, name=name, flags=args)
        return super().get_experiments(settings, competitors, prefix='opt')

@dataclass(frozen=True)
class Configs(WithBenchmarks):
    competitors: list[Competitors] = field(default_factory=lambda: list(Competitors.__members__.values()))
    """List of competitors."""

    def get_experiments(self, settings: "Main"):
        competitors = { c.name: c.value for c in self.competitors }
        return super().get_experiments(settings, competitors)

@dataclass(frozen=True)
class Tools(WithBenchmarks):
    competitors: list[Path]
    """All executable files in this directory will be used as competitors."""

    def __post_init__(self):
        for p in self.competitors:
            assert p.exists(), f'{str(p)} does not exist'
            assert p.is_file(), f'{str(p)} is not a file'
            assert os.access(p, os.X_OK), f'{str(p)} is not executable'

    def get_experiments(self, settings: "Main"):
        competitors = { 'tool': Competitors.std.value }
        for c in self.competitors:
            competitors[c.name] = partial(ExternalSygusRun, name=c.name, path=c.absolute(), args='{filename}')
        return super().get_experiments(settings, competitors)

@dataclass(frozen=True)
class Main:
    dir: Path
    """Directory to place the result files."""

    exp: Tools | Configs | Opt
    """Experiments to carry out."""

    base: Path = DEFAULT_BENCHMARK_BASE_DIR
    """Base directory of the benchmarks sub-directories."""

    trials: int = TRIALS
    """Number of trials per experiment."""

    timeout: int = TIMEOUT
    """Timeout for each experiment."""

    dry: bool = False
    """Dry run. Just print, don't execute the experiment."""

    force: bool = False
    """Force to do the experiment even if results are already available."""

    def run(self):
        exps = self.exp.get_experiments(self)
        run_experiments(self.dir, self.dry, self.force, exps)
        if not self.dry:
            for exp in exps:
                eval_experiment(self.dir, exp)

if __name__ == '__main__':
    try:
        tyro.cli(Main).run()
    except Exception as e:
        print('error:', str(e))
        sys.exit(1)