from functools import partial
from pathlib import Path

import enum

import tyro

from eval.util import *
from synth.util import get_file_path

# defaults

DEFAULT_BENCHMARK_BASE_DIR   = Path('resources')
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
        return SygusRun(iteration, timeout, bench, name='no_opt',
                        synth_flags=['--synth.no-opt-no-dead-code',
                                    '--synth.no-opt-cse',
                                    '--synth.no-opt-const',
                                    '--synth.no-opt-commutative',
                                    '--synth.no-opt-insn-order'])

    @enum.member
    def fuse(iteration: int, timeout: int, bench: str):
        return SygusRun(iteration, timeout, bench, name='fuse',
                        synth_flags=['--fuse-constraints'])

    @enum.member
    def flatten(iteration: int, timeout: int, bench: str):
        return SygusRun(iteration, timeout, bench, name='flatten',
                        synth_flags=['--flatten-grammar'])

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
    benchmarks: list[str]

    def get_benchmarks(self, settings: "Main"):
        return [ settings.base / b for b in self.benchmarks ]

    def get_experiments(self, settings: "Main", competitors: dict[str, RunFactory]):
        prefix = '-'.join(competitors)
        benchmarks = { b.name: sorted(b.glob('*.sl')) for b in self.get_benchmarks(settings) }
        return [ Experiment(f'{prefix}_{b}', settings.trials, settings.timeout,
                            files, competitors) for b, files in benchmarks.items() ]

@dataclass(frozen=True)
class Opt(Base):
    def get_experiments(self, settings: "Main"):
        flags = {
            'd': 'no-dead-code',
            'e': 'cse',
            'c': 'const',
            'm': 'commutative',
            'o': 'insn-order'
        }
        n_opts = len(flags)
        competitors = {}
        for mask in range(1 << n_opts):
            on = lambda i: ((1 << i) & mask) != 0
            name  = ''.join(f if on(i) else '-' for i, f in enumerate(flags))
            args = [ '--synth.' + ('opt-' if on(i) else 'no-opt-') + f for i, f in enumerate(flags.values()) ]
            competitors[name] = partial(SygusRun, name=name, synth_flags=args)
        return super().get_experiments(settings, competitors)

@dataclass(frozen=True)
class Configs(Base):
    competitors: list[Competitors] = field(default_factory=lambda: list(Competitors.__members__.values()))
    """List of competitors."""

    def get_experiments(self, settings: "Main"):
        competitors = { c.name: c.value for c in self.competitors }
        return super().get_experiments(settings, competitors)

@dataclass(frozen=True)
class Tools(Base):
    dir: Path = DEFAULT_COMPETITORS_BASE_DIR
    """All executable files in this directory will be used as competitors."""

    exclude: set[str] = field(default_factory=lambda: set())
    """Competitors in this list will be excluded from the experiment."""

    def get_experiments(self, settings: "Main"):
        competitors = { 'tool': Competitors.std.value }
        for c in self.dir.glob('*'):
            if c.name not in self.exclude:
                assert c.name not in competitors, f'tool {c} already registered'
                competitors[c.name] = partial(ExternalSygusRun, name=c.name, path=c.absolute(), args='{filename}')
        return super().get_experiments(settings, competitors)

@dataclass(frozen=True)
class All(Base):
    def get_experiments(self, settings: "Main"):
        return \
            Tools(benchmarks=['sygus_sel', 'deobfusc', 'lobster', 'crypto']).get_benchmarks(settings) + \
            Configs(benchmarks=['sygus_sel']).get_benchmarks(settings) + \
            Opt(benchmarks=['small']).get_benchmarks(settings)



@dataclass(frozen=True)
class Main:
    dir: Path
    """Directory to place the result files."""

    exp: All | Tools | Configs | Opt
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
    tyro.cli(Main).run()