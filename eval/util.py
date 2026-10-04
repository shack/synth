from collections.abc import Sequence
from dataclasses import dataclass, field
from io import StringIO
from pathlib import Path
import sys
from typing import Any, Callable, Mapping
from datetime import timedelta
from functools import cached_property
from contextlib import contextmanager, nullcontext

import hashlib
import json
import subprocess
import time
import tempfile
import shlex
import os
import signal
import threading
import queue
from concurrent.futures import ThreadPoolExecutor, as_completed

import tinysexpr

from sygus import solution_sizes

from synth.util import get_file_path

# Bookkeeping for concurrent runs.
# Every benchmark is executed in its own process (and its own session, see
# Run.run), so a SIGINT delivered to the terminal never reaches the children.
# The driver therefore has to kill them explicitly on Ctrl-C, for which it needs
# to know which children are alive.
_live_lock = threading.Lock()
_live: set[subprocess.Popen] = set()
# Set by the driver when the user interrupts. Runs that observe this flag
# after their child terminated report 'interrupted' and do not persist a
# result file, so they are picked up again by the next invocation.
_cancelled = threading.Event()

_print_lock = threading.Lock()

def _log(line: str):
    """Print one line atomically.

    Used by the driver and by the worker threads, so that lines of
    concurrently starting or finishing runs do not interleave.
    """
    with _print_lock:
        sys.stdout.write(line + '\n')
        sys.stdout.flush()

def _eta(remaining: timedelta, jobs: int) -> timedelta:
    return timedelta(seconds=round((remaining / jobs).total_seconds()))

CPU_SYSFS = Path('/sys/devices/system/cpu')

def _read_sysfs(path: Path) -> str | None:
    try:
        return path.read_text().strip()
    except (OSError, ValueError):
        return None

def _parse_cpu_list(s: str | None) -> frozenset[int] | None:
    """Parse a Linux CPU list like "0-3,8,10-11"."""
    if not s:
        return None
    try:
        cpus = set()
        for part in s.split(','):
            lo, _, hi = part.partition('-')
            cpus.update(range(int(lo), int(hi or lo) + 1))
        return frozenset(cpus)
    except ValueError:
        return None

def _cpu_topology(cpu: int):
    """Return (core, cache, capacity) of the given CPU.

    `core` is the set of hardware threads of the physical core, `cache` the
    set of CPUs sharing the largest cache of the CPU (or None if unknown),
    and `capacity` a number that is larger for faster core types on hybrid
    CPUs (None if all cores are alike or it is unknown).
    """
    d = CPU_SYSFS / f'cpu{cpu}'
    core = (_parse_cpu_list(_read_sysfs(d / 'topology/thread_siblings_list'))
            or _parse_cpu_list(_read_sysfs(d / 'topology/core_cpus_list'))
            or frozenset({cpu}))
    cache, best_level = None, -1
    for idx in sorted((d / 'cache').glob('index*')) if (d / 'cache').is_dir() else []:
        if _read_sysfs(idx / 'type') == 'Instruction':
            continue
        try:
            level = int(_read_sysfs(idx / 'level') or '')
        except ValueError:
            continue
        shared = _parse_cpu_list(_read_sysfs(idx / 'shared_cpu_list'))
        if shared and level > best_level:
            cache, best_level = shared, level
    # Arm big.LITTLE and some x86 systems expose the relative performance
    # of a core directly. Intel hybrid CPUs register separate PMUs for
    # performance (cpu_core) and efficiency (cpu_atom) cores.
    try:
        capacity = int(_read_sysfs(d / 'cpu_capacity') or '')
    except ValueError:
        capacity = None
    if capacity is None:
        atom = _parse_cpu_list(_read_sysfs(CPU_SYSFS.parent.parent / 'cpu_atom/cpus'))
        if atom:
            capacity = 0 if cpu in atom else 1
    return core, cache, capacity

def pinning_supported() -> bool:
    return hasattr(os, 'sched_getaffinity') and hasattr(os, 'sched_setaffinity')

def cpu_quota() -> float | None:
    """The number of CPUs the cgroup of this process may use (as set by,
    e.g., `docker --cpus`), or None if unlimited or unknown."""
    try:
        lines = Path('/proc/self/cgroup').read_text().splitlines()
    except OSError:
        return None
    limits = []
    for line in lines:
        _, controllers, path = line.split(':', 2)
        if controllers == '':
            # cgroup v2: the limit of any ancestor applies.
            d = Path('/sys/fs/cgroup') / path.lstrip('/')
            while True:
                v = (_read_sysfs(d / 'cpu.max') or '').split()
                if len(v) == 2 and v[0] != 'max':
                    limits.append(int(v[0]) / int(v[1]))
                if d == Path('/sys/fs/cgroup'):
                    break
                d = d.parent
        elif 'cpu' in controllers.split(','):
            # cgroup v1 (inside a container, the path may not be visible).
            for d in (Path('/sys/fs/cgroup') / controllers / path.lstrip('/'),
                      Path('/sys/fs/cgroup') / controllers,
                      Path('/sys/fs/cgroup/cpu')):
                q = _read_sysfs(d / 'cpu.cfs_quota_us')
                per = _read_sysfs(d / 'cpu.cfs_period_us')
                if q and per and int(q) > 0:
                    limits.append(int(q) / int(per))
                    break
    return min(limits) if limits else None

SMT_CONTROL = Path('/sys/devices/system/cpu/smt/control')
BOOST_CONTROL = Path('/sys/devices/system/cpu/cpufreq/boost')

@contextmanager
def _sysfs_set(path: Path, what: str, when: str, value: str, hint: str = ''):
    """Write `value` to the sysfs file `path` for the duration of the
    context if it currently reads `when`, and restore it afterwards.

    Needs write access to `path`, i.e. root. Without it, a warning is
    printed and the setting stays as it is.
    """
    try:
        state = path.read_text().strip()
    except OSError:
        state = None
    if state != when:
        # Already set, or not supported by this system: nothing to do.
        yield
        return
    try:
        path.write_text(value)
    except OSError as e:
        _log(f'warning: cannot disable {what} ({e.strerror}); '
             f'run `echo {value} | sudo tee {path}` to disable it manually.' +
             (f' {hint}' if hint else ''))
        yield
        return
    _log(f'disabled {what}')
    try:
        yield
    finally:
        path.write_text(state)
        _log(f'restored {what} setting "{state}"')

def smt_disabled():
    """Disable simultaneous multithreading (SMT) for the duration of the
    context and restore the previous setting afterwards (needs root)."""
    return _sysfs_set(SMT_CONTROL, 'SMT', 'on', 'off',
                      hint='Pinning avoids SMT siblings nevertheless.')

def boost_disabled():
    """Disable CPU frequency boosting (turbo) for the duration of the
    context and restore the previous setting afterwards (needs root).

    With boosting, the clock of a core depends on how many other cores are
    busy, so the measured times depend on the number of concurrent jobs."""
    return _sysfs_set(BOOST_CONTROL, 'frequency boost', '1', '0')

def pick_cpus(jobs: int, siblings: bool = True) -> list[int]:
    """Choose `jobs` CPUs to pin the concurrent runs to.

    On hybrid CPUs, only the fastest core type is used (with a warning if
    there are not enough of them). The CPUs are distributed round-robin over
    the domains of the largest cache, so that as few runs as possible share
    it. Within a domain, distinct physical cores are used before SMT
    siblings, and CPU 0 (which typically serves most interrupts) is used
    last. If `siblings` is false, SMT siblings are not used at all.

    Missing topology information is tolerated: every CPU is then treated as
    a physical core of its own, and all CPUs as sharing one cache.
    """
    avail = sorted(os.sched_getaffinity(0))
    if jobs > len(avail):
        raise ValueError(f'cannot pin {jobs} jobs to {len(avail)} available CPUs')
    topo = { c: _cpu_topology(c) for c in avail }
    # Group by core type, fastest first.
    capacities = sorted({ cap for _, _, cap in topo.values() },
                        key=lambda cap: -1 if cap is None else cap, reverse=True)
    order = []
    for cap in capacities:
        domains: dict[Any, list[int]] = {}
        sibling_cpus: dict[Any, list[int]] = {}
        seen_cores: set = set()
        for c in sorted(avail, key=lambda c: (c == 0, c)):
            core, cache, c_cap = topo[c]
            if c_cap != cap:
                continue
            target = sibling_cpus if core in seen_cores else domains
            target.setdefault(cache, []).append(c)
            seen_cores.add(core)
        for per_dom in (domains, sibling_cpus) if siblings else (domains,):
            lists = list(per_dom.values())
            while any(lists):
                for l in lists:
                    if l:
                        order.append(l.pop(0))
        if cap is not None and cap == capacities[0] and jobs > len(order) \
                and len(capacities) > 1:
            _log(f'warning: only {len(order)} CPUs of the fastest core type available; '
                 f'runs on slower cores are not comparable to the others')
    if jobs > len(order):
        raise ValueError(f'cannot pin {jobs} jobs to {len(order)} physical cores '
                         '(allow SMT to use more)')
    return order[:jobs]

def _kill_live_children():
    with _live_lock:
        for p in list(_live):
            _kill(p)

def _kill(p: subprocess.Popen):
    """Kill the child and (on POSIX) everything it spawned."""
    try:
        if hasattr(os, 'killpg'):
            os.killpg(p.pid, signal.SIGKILL)
        elif os.name == 'nt':
            # No process groups: kill the whole process tree.
            subprocess.run(['taskkill', '/F', '/T', '/PID', str(p.pid)],
                           capture_output=True)
        else:
            p.kill()
    except (ProcessLookupError, PermissionError):
        # Already gone (or, on macOS, a zombie group).
        pass

def _wait(p: subprocess.Popen, timeout: int | None):
    """Wait for the child to terminate, killing it after `timeout` seconds.

    Returns (timed_out, wall time in ns, rusage). The rusage covers the
    child and all of its descendants it waited for; it is None where the
    platform cannot provide it (Windows).
    """
    start = time.perf_counter_ns()
    if not hasattr(os, 'wait4'):
        try:
            p.wait(timeout=timeout)
            return False, time.perf_counter_ns() - start, None
        except subprocess.TimeoutExpired:
            _kill(p)
            p.wait()
            return True, time.perf_counter_ns() - start, None
    # The timer kills the process group on timeout. The lock ensures it
    # does not fire after the child has been reaped (its pid might have
    # been reused by then).
    kill_lock = threading.Lock()
    exited = False
    timed_out = False
    def on_timeout():
        nonlocal timed_out
        with kill_lock:
            if not exited:
                timed_out = True
                _kill(p)
    timer = threading.Timer(timeout, on_timeout) if timeout else None
    try:
        if timer:
            timer.start()
        if hasattr(os, 'waitid'):
            # Wait for termination without reaping, then reap with wait4.
            os.waitid(os.P_PID, p.pid, os.WEXITED | os.WNOWAIT)
            duration = time.perf_counter_ns() - start
            with kill_lock:
                exited = True
            _, status, ru = os.wait4(p.pid, 0)
        else:
            # No waitid (e.g. macOS before Python 3.13): reap directly. The
            # timer may then fire right after reaping, which _kill tolerates.
            _, status, ru = os.wait4(p.pid, 0)
            duration = time.perf_counter_ns() - start
            with kill_lock:
                exited = True
    finally:
        if timer:
            timer.cancel()
    p.returncode = os.waitstatus_to_exitcode(status)
    return timed_out, duration, ru

@dataclass(frozen=True)
class Run:
    iteration: int
    timeout: int | None

    def get_id(self):
        """Uniquely identify this run."""
        cmd = self.get_cmd('')
        return f'{cmd} {self.timeout} {self.iteration:04d}'

    def get_tag(self):
        """A textual description of this run."""
        return f'{self.get_name()}_{self.iteration}_{self.timeout}'

    def read_stats(self, stats_file: Path):
        """Read the stats file generated by ran command."""
        raise NotImplementedError()

    def get_cmd(self, stats_file: Path):
        """Run the benchmark command, writing stats to stats_file."""
        raise NotImplementedError()

    def get_results_filename(self, output_dir: Path):
        filename = f'{self.get_tag()}-' + hashlib.sha1(self.get_id().encode('utf-8')).hexdigest()
        return output_dir / Path(f'{filename}.json')

    def read_result(self, output_dir: Path):
        results_file = self.get_results_filename(output_dir)
        if results_file.exists():
            with open(results_file, 'rt') as f:
                return json.load(f)
        return None

    def run(self, output_dir: Path, cpu: int | None = None):
        """Execute this run in a child process and persist its result.

        Safe to call concurrently from several threads: every invocation
        uses its own temporary stats file and child process. Does not print;
        the caller is responsible for progress output.

        If `cpu` is given, the child (and everything it spawns) is pinned
        to that CPU.
        """
        ns = 1_000_000_000
        result_file = self.get_results_filename(output_dir)
        with tempfile.NamedTemporaryFile(delete=False, delete_on_close=False) as f, \
             tempfile.TemporaryFile('w+t') as out:
            cmd = self.get_cmd(f.name)
            args = shlex.split(cmd)
            stats = {
                'cmd': cmd,
                'tag': self.get_tag(),
            }
            if cpu is not None:
                # On Linux, the affinity of pid 0 is that of the calling
                # thread only. The child forked from this thread inherits it.
                os.sched_setaffinity(0, {cpu})
                stats['cpu'] = cpu
            # start_new_session=True puts the child into its own process
            # group whose id equals p.pid (on POSIX), so we can kill the
            # child together with everything it spawned (e.g. `uv run` ->
            # python -> solver). stdout goes to a file, so that we can reap
            # the child ourselves with wait4 (to obtain its resource usage)
            # without a reader.
            with subprocess.Popen(args,
                                  stdout=out, stdin=subprocess.DEVNULL,
                                  start_new_session=True,
                                  text=True) as p:
                with _live_lock:
                    _live.add(p)
                try:
                    timed_out, duration, ru = _wait(p, self.timeout)
                    if timed_out:
                        stats |= {
                            'status': 'timeout',
                            'wall_time': self.timeout * ns,
                        }
                        if ru:
                            stats['cpu_time'] = self.timeout * ns
                    else:
                        out.seek(0)
                        stats |= {
                            'status': 'success',
                            'wall_time': duration,
                        }
                        if ru:
                            stats |= {
                                'cpu_time': round((ru.ru_utime + ru.ru_stime) * ns),
                                # ru_maxrss is in bytes on macOS, in KiB elsewhere.
                                'max_rss_kb': ru.ru_maxrss // (1024 if sys.platform == 'darwin' else 1),
                            }
                        stats |= {
                            'stats': self.read_stats(Path(f.name)),
                            'stdout': out.read(),
                        }
                except Exception as e:
                    if p.returncode is None:
                        _kill(p)
                    stats |= {
                        'status': 'error',
                        'wall_time': 0,
                        'returncode': p.returncode,
                        'error': repr(e),
                    }
                finally:
                    with _live_lock:
                        _live.discard(p)
        if _cancelled.is_set():
            # The child was (most likely) killed by the driver on Ctrl-C.
            # Do not record a result, so the run is redone next time.
            stats['status'] = 'interrupted'
            return stats
        assert output_dir.exists() and output_dir.is_dir()
        with open(result_file, 'wt') as f:
            json.dump(stats, f, indent=4)
        return stats

def prepare_opts(opts, prefix=None):
    prefix = f'{prefix}.' if prefix else ''
    for k, v in opts.items():
        if isinstance(v, bool):
            yield f'--{prefix}' + ('' if v else 'no-') + k
        else:
            yield f'--{prefix}{k} {v}'

@dataclass(frozen=True)
class SynthRun(Run):
    set: str
    bench: str
    synth: str
    solver: str
    run_opts: dict[str, Any] = field(default_factory=dict)
    set_opts: dict[str, Any] = field(default_factory=dict)
    syn_opts: dict[str, Any] = field(default_factory=dict)
    extra_tag: str = ''

    def read_stats(self, stats_file: Path):
        with open(stats_file, 'rt') as f:
            return json.load(f)

    def get_name(self):
        return 'bench'

    def get_tag(self):
        return f'{super().get_tag()}_{self.set}_{self.bench}_{self.synth}_{self.solver}_{self.extra_tag}'

    def get_cmd(self, stats_file: Path):
        run_opts = ' '.join(prepare_opts(self.run_opts))
        set_opts = ' '.join(prepare_opts(self.set_opts, prefix='set'))
        syn_opts = ' '.join(prepare_opts(self.syn_opts, prefix='synth'))
        args = f'--tests {self.bench} {run_opts} set:{self.set} {set_opts} synth:{self.synth} {syn_opts} synth.solver:config --synth.solver.name {self.solver}'
        return f'uv run benchmark.py run --stats {stats_file} {args}'

@dataclass(frozen=True)
class SygusRun(Run):
    bench: Path
    flags: str = ''
    name: str = 'us'

    def read_stats(self, stats_file: Path):
        with open(stats_file, 'rt') as f:
            return json.load(f)

    def get_name(self):
        return self.name

    def get_tag(self):
        return f'{super().get_tag()}_{self.bench.parts[-1]}'

    def get_cmd(self, stats_file: Path):
        return f'uv run sygus.py synth {self.flags} --stats {stats_file} {self.bench}'

@dataclass(frozen=True)
class ExternalSygusRun(Run):
    bench: Path
    name: str
    path: Path
    args: str
    """Use {filename} to indicate the benchmark file."""

    def read_stats(self, _: Path):
        return ''

    def get_name(self):
        return self.name

    def get_tag(self):
        return f'{super().get_tag()}_{self.bench.parts[-1]}'

    def get_cmd(self, stats_file: Path):
        return str(self.path) + ' ' + self.args.format(filename=self.bench)

class Experiment:
    def __init__(self,
                 name: str,
                 iterations: int,
                 timeout_in_s: int,
                 benchmarks: Sequence,
                 competitors: Mapping[str, Callable]):
        self.exp = {
            str(b): {
                name: [
                    create_run(i, timeout_in_s, b) for i in range(iterations)
                ]
                for name, create_run in competitors.items()
            } for b in benchmarks
        }
        self.name = name

    def get_name(self):
        return self.name

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

    def to_run(self, output_dir: Path, force: bool):
        for run in self.runs():
            if force or not run.get_results_filename(output_dir).exists():
                yield run

    def get_results(self, stats_dir: Path):
        res = self.map(lambda r: r.read_result(stats_dir))
        return res

    def get_aggregated_results(self, stats_dir: Path, aggregate: Callable):
        return {
            bench: {
                competitor: aggregate(trials) for competitor, trials in competitors.items()
            } for bench, competitors in self.get_results(stats_dir).items()
        }

def run_experiments(dir: Path, dry: bool, force: bool, exps: Sequence[Experiment],
                    jobs: int = 1, pin: bool = True, smt: bool = False,
                    boost: bool = False):
    """Execute all outstanding runs of the given experiments.

    `jobs` benchmark processes are executed concurrently. With `jobs=1`
    (the default) runs are executed strictly sequentially, which yields the
    least noisy wall-time measurements.

    If `pin` is set, each concurrent run is pinned to its own CPU (see
    `pick_cpus`). Unless `smt` is set, SMT is disabled while the runs are
    executed (see `smt_disabled`) and runs are never pinned to SMT siblings.
    Unless `boost` is set, frequency boosting is disabled while the runs
    are executed (see `boost_disabled`).
    """
    if jobs < 1:
        raise ValueError(f'jobs must be at least 1, got {jobs}')

    data_dir = dir / Path('data')
    if not dry:
        if not data_dir.exists():
            data_dir.mkdir(parents=True)
        elif not data_dir.is_dir():
            raise NotADirectoryError(f'{data_dir} exists and is not a directory')

    max_time = 0
    to_run = []
    for exp in exps:
        for run in exp.to_run(data_dir, force):
            to_run.append(run)
            max_time += (run.timeout if run.timeout else 0)

    if dry:
        for run in to_run:
            stats_file = run.get_results_filename(data_dir)
            print(run.get_cmd(stats_file))
        return

    n_total = len(to_run)
    if n_total == 0:
        _log('nothing to run: all results are available (use --force to redo them)')
        return
    remaining = timedelta(seconds=max_time)
    _log(f'{n_total} runs to go (<= {_eta(remaining, jobs)} with {jobs} job(s))')
    done = 0
    _cancelled.clear()

    if pin and not pinning_supported():
        _log('warning: pinning runs to CPUs is not supported on this platform')
        pin = False
    quota = cpu_quota()
    if quota is not None and jobs > quota:
        _log(f'warning: {jobs} jobs exceed the CPU quota of {quota:g} CPUs; '
             'the runs will be throttled and the measured times are unreliable')

    # Free CPUs. A worker takes one for the duration of a run.
    cpus = queue.SimpleQueue()

    def start(run: Run):
        # Executed by the worker thread, i.e. when the run actually starts.
        cpu = cpus.get() if pin else None
        try:
            _log(f'started  {run.get_tag()}' + (f' on CPU {cpu}' if pin else ''))
            return run.run(data_dir, cpu)
        finally:
            if pin:
                cpus.put(cpu)

    with (nullcontext() if smt else smt_disabled()), \
         (nullcontext() if boost else boost_disabled()), \
         ThreadPoolExecutor(max_workers=jobs) as ex:
        if pin:
            # Only now, because disabling SMT changes the available CPUs.
            picked = pick_cpus(jobs, siblings=smt)
            _log(f'pinning runs to CPUs {",".join(map(str, picked))}')
            for c in picked:
                cpus.put(c)
        try:
            futs = { ex.submit(start, run): run for run in to_run }
            for fut in as_completed(futs):
                run = futs[fut]
                stats = fut.result()
                done += 1
                remaining -= timedelta(seconds=(run.timeout if run.timeout else 0))
                wall = stats.get('wall_time', 0) / 1e9
                cpu = f'{stats["cpu_time"] / 1e9:9.3f}s' if 'cpu_time' in stats else f'{"n/a":>10}'
                _log(f'[{done}/{n_total}] (<= {_eta(remaining, jobs)} to go) {stats["status"]:8} {wall:9.3f}s wall {cpu} cpu {run.get_tag()}')
        except KeyboardInterrupt:
            # Only the main thread receives SIGINT. Stop handing out queued
            # runs, then kill the children of the runs in flight; their
            # workers observe _cancelled and finish without writing results.
            _cancelled.set()
            ex.shutdown(wait=False, cancel_futures=True)
            _kill_live_children()
            raise

def is_infeasible(trial) -> bool:
    return trial.get('stdout', '').strip() in ('infeasible', '(infeasible)')

def solution_output(trial) -> str | None:
    """The output of a run if it contains a solution, None if the run timed
    out, failed, or answered fail or infeasible."""
    out = trial.get('stdout', '').strip()
    match out:
        case '' | 'fail' | '(fail)' | 'infeasible' | '(infeasible)':
            return None
    return out

def has_answer(trial) -> bool:
    """Whether the run answered with a solution or with infeasible."""
    return solution_output(trial) is not None or is_infeasible(trial)

# The times are only reported for benchmarks that are answered in all trials.
# Otherwise, a solver that quickly gives up would look fast.

def aggregate_wall_time(trials):
    if trials and all('wall_time' in t and has_answer(t) for t in trials):
        get_wall_time = lambda t: t['wall_time'] / 1_000_000_000
        return sum(map(get_wall_time, trials)) / len(trials)

def aggregate_cpu_time(trials):
    if trials and all('cpu_time' in t and has_answer(t) for t in trials):
        get_cpu_time = lambda t: t['cpu_time'] / 1_000_000_000
        return sum(map(get_cpu_time, trials)) / len(trials)

def aggregate_result_size(trials):
    if trials and (out := solution_output(trials[0])):
        try:
            for sexpr in tinysexpr.read(StringIO(out)):
                return sum(sz for _, sz in solution_sizes(sexpr, const_cost=0))
        except tinysexpr.SyntaxError as e:
            tag = trials[0]['tag']
            print(f'error determining size in {tag}: {e}', file=sys.stderr)

def format_by_bench_row_competitor_col(file_like, res):
    first_width = max(len(s) for s in res)
    other_width = 16
    heads = list(next(iter(res.values())).keys())
    print(f'{'bench':{first_width}}', ' '.join(f'{h:>{other_width}}' for h in heads), file=file_like)
    for bench, competitors in res.items():
        row = ' '.join(f'{t:>{other_width}.5f}' if t is not None else f'{'None':>{other_width}}' for t in competitors.values())
        print(f'{bench:{first_width}} {row}', file=file_like)