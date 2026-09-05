#!/usr/bin/env python3
"""Find performance regressions of the checked-out branch relative to a base ref.

The base ref (default: ``main``) is checked out into a temporary git worktree.
``uv run eval.py --dir ... exp:tools --exp.benchmarks ...`` is then run in the
base worktree and in the current working tree (including uncommitted changes),
on the same benchmark directories, one after the other.  Finally the per-benchmark
wall times, solve statuses and solution sizes of both runs are compared.

Only the standard library is used, so the script can be run as

    uv run perfcmp.py BENCH_DIR [BENCH_DIR ...]
    python3 perfcmp.py BENCH_DIR [BENCH_DIR ...]

Results are kept in ``--out`` (default ``results.perfcmp``), one sub-directory
per checkout, so an interrupted run can be resumed: eval.py skips benchmarks
that already have a result file (pass ``--force`` to re-run them).

Exit code is 1 if a regression was found (a benchmark that main solves but the
current branch does not, or one that got slower than the thresholds allow),
0 otherwise, 2 on usage errors.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from statistics import mean

# ----------------------------------------------------------------------------
# helpers

def die(msg: str, code: int = 2):
    print(f'perfcmp: {msg}', file=sys.stderr)
    sys.exit(code)

def git(repo: Path, *args: str, check: bool = True) -> str:
    p = subprocess.run(['git', '-C', str(repo), *args],
                       capture_output=True, text=True, check=False)
    if check and p.returncode != 0:
        die(f'git {" ".join(args)} failed:\n{p.stderr.strip()}')
    return p.stdout.strip()

def banner(msg: str):
    line = '=' * max(8, min(78, len(msg) + 4))
    print(f'\n{line}\n  {msg}\n{line}', flush=True)

# ----------------------------------------------------------------------------
# checkouts

@dataclass(frozen=True)
class Checkout:
    label: str      # 'base' or 'cur'
    name: str       # human readable: ref/branch name
    sha: str
    dirty: bool
    path: Path      # working tree that contains eval.py

    def describe(self) -> str:
        return f'{self.name} @ {self.sha[:8]}' + (' (dirty)' if self.dirty else '')

    def result_dir(self, out: Path) -> Path:
        tag = f'{self.label}-{self.name.replace("/", "_")}-{self.sha[:8]}'
        if self.dirty:
            tag += '-dirty'
        return out / tag

def current_checkout(repo: Path) -> Checkout:
    branch = git(repo, 'rev-parse', '--abbrev-ref', 'HEAD')
    sha = git(repo, 'rev-parse', 'HEAD')
    dirty = bool(git(repo, 'status', '--porcelain', '--untracked-files=no'))
    return Checkout('cur', branch, sha, dirty, repo)

def add_worktree(repo: Path, ref: str, sha: str) -> Checkout:
    tmp = Path(tempfile.mkdtemp(prefix=f'perfcmp-{ref.replace("/", "_")}-'))
    # --detach: works even if `ref` is already checked out in another worktree
    git(repo, 'worktree', 'add', '--detach', str(tmp), sha)
    return Checkout('base', ref, sha, False, tmp)

def remove_worktree(repo: Path, path: Path):
    p = subprocess.run(['git', '-C', str(repo), 'worktree', 'remove', '--force', str(path)],
                       capture_output=True, text=True)
    if p.returncode != 0:
        print(f'perfcmp: git worktree remove failed ({p.stderr.strip()}), removing manually',
              file=sys.stderr)
        shutil.rmtree(path, ignore_errors=True)
        subprocess.run(['git', '-C', str(repo), 'worktree', 'prune'], check=False)

# ----------------------------------------------------------------------------
# running eval.py

def run_eval(co: Checkout, result_dir: Path, benchmarks: list[Path], args):
    banner(f'{co.label}: {co.describe()}  ->  {result_dir}')
    # If perfcmp.py itself runs under `uv run`, VIRTUAL_ENV points to the venv
    # of the current checkout; drop it so uv uses each checkout's own venv.
    env = {k: v for k, v in os.environ.items() if k != 'VIRTUAL_ENV'}
    # Make sure the venv exists before timing anything, otherwise the first
    # `uv run sygus.py` of the experiment pays for creating it.
    subprocess.run(['uv', 'sync'], cwd=co.path, env=env, check=True)
    cmd = ['uv', 'run', 'eval.py', '--dir', str(result_dir)]
    if args.timeout is not None:
        cmd += ['--timeout', str(args.timeout)]
    if args.trials is not None:
        cmd += ['--trials', str(args.trials)]
    if args.force:
        cmd += ['--force']
    if args.dry:
        cmd += ['--dry']
    cmd += ['exp:tools', '--exp.benchmarks', *map(str, benchmarks)]
    print('+', shlex.join(cmd), f'  (cwd: {co.path})', flush=True)
    subprocess.run(cmd, cwd=co.path, env=env, check=True)

# ----------------------------------------------------------------------------
# reading results

@dataclass
class Result:
    status: str             # 'success' | 'timeout' | 'error'
    time: float | None      # mean wall time in seconds over trials (None on error)
    size: int | None        # solution size as computed by eval.py, if known
    trials: int

def read_sizes(result_dir: Path, benchmarks: list[Path]) -> dict[str, int | None]:
    """Parse the `stats/tool_<benchdir>-size.txt` tables written by eval.py."""
    sizes: dict[str, int | None] = {}
    for b in benchmarks:
        f = result_dir / 'stats' / f'tool_{b.name}-size.txt'
        if not f.exists():
            continue
        with open(f) as fh:
            lines = [l.rstrip('\n') for l in fh if l.strip()]
        if not lines:
            continue
        heads = lines[0].split()
        try:
            col = heads.index('tool')     # heads[0] == 'bench'
        except ValueError:
            continue
        for line in lines[1:]:
            parts = line.split()
            if len(parts) <= col:
                continue
            v = parts[col]
            try:
                sizes[parts[0]] = None if v == 'None' else int(float(v))
            except ValueError:
                sizes[parts[0]] = None
    return sizes

def read_results(result_dir: Path, benchmarks: list[Path]) -> dict[str, Result]:
    data = result_dir / 'data'
    if not data.is_dir():
        return {}
    wanted = {str(b) for b in benchmarks}
    per_bench: dict[str, list[dict]] = {}
    for f in sorted(data.glob('*.json')):
        try:
            with open(f) as fh:
                r = json.load(fh)
            bench = shlex.split(r['cmd'])[-1]
        except (json.JSONDecodeError, KeyError, IndexError, ValueError) as e:
            print(f'perfcmp: skipping unreadable result {f}: {e}', file=sys.stderr)
            continue
        # results of other benchmark sets / competitors may live in the same dir
        if str(Path(bench).parent) not in wanted:
            continue
        per_bench.setdefault(bench, []).append(r)

    sizes = read_sizes(result_dir, benchmarks)
    results = {}
    for bench, trials in per_bench.items():
        statuses = {t.get('status', 'error') for t in trials}
        if statuses == {'success'}:
            status = 'success'
        elif 'error' in statuses:
            status = 'error'
        else:
            status = 'timeout'
        times = [t['wall_time'] / 1e9 for t in trials if t.get('status') != 'error' and 'wall_time' in t]
        time = mean(times) if times else None
        results[bench] = Result(status, time, sizes.get(bench), len(trials))
    return results

# ----------------------------------------------------------------------------
# comparison

LOST, SLOWER, SIZE_UP, SAME, SIZE_DOWN, FASTER, GAINED, NA = \
    'LOST', 'SLOWER', 'SIZE+', '', 'SIZE-', 'FASTER', 'GAINED', 'n/a'
REGRESSIONS = (LOST, SLOWER)

@dataclass
class Row:
    bench: str
    base: Result
    cur: Result
    verdict: str
    diff: float | None
    ratio: float | None
    size_verdict: str

    def sort_key(self):
        order = {LOST: 0, SLOWER: 1, SAME: 2, NA: 2, FASTER: 3, GAINED: 4}
        return (order[self.verdict], -(self.ratio if self.ratio is not None else 1.0))

def compare(base: dict[str, Result], cur: dict[str, Result], threshold: float, min_diff: float) -> list[Row]:
    rows = []
    for bench in sorted(set(base) & set(cur)):
        b, c = base[bench], cur[bench]
        diff = ratio = None
        if b.status == 'success' and c.status != 'success':
            verdict = LOST
        elif b.status != 'success' and c.status == 'success':
            verdict = GAINED
        elif b.status != 'success' or c.status != 'success':
            verdict = NA
        else:
            diff = c.time - b.time
            ratio = c.time / max(b.time, 1e-6)
            if diff > min_diff and c.time > b.time * (1 + threshold):
                verdict = SLOWER
            elif -diff > min_diff and b.time > c.time * (1 + threshold):
                verdict = FASTER
            else:
                verdict = SAME
        size_verdict = SAME
        if b.size is not None and c.size is not None and b.size != c.size:
            size_verdict = SIZE_UP if c.size > b.size else SIZE_DOWN
        rows.append(Row(bench, b, c, verdict, diff, ratio, size_verdict))
    rows.sort(key=Row.sort_key)
    return rows

def short_name(bench: str, root: str) -> str:
    try:
        return str(Path(bench).relative_to(root))
    except ValueError:
        return bench

def fmt_time(r: Result) -> str:
    if r.status == 'success':
        return f'{r.time:9.3f}'
    return f'{r.status:>9}'

def fmt_size(r: Result) -> str:
    return '-' if r.size is None else str(r.size)

def report(rows: list[Row], base: dict, cur: dict, base_co: Checkout, cur_co: Checkout,
           benchmarks: list[Path], args, out) -> bool:
    """Print the comparison; return True if a regression was found."""
    root = os.path.commonpath([str(b) for b in benchmarks])
    if len(benchmarks) == 1:
        root = str(benchmarks[0])
    width = max([len(short_name(r.bench, root)) for r in rows] + [len('benchmark')])

    def p(*a, **kw):
        print(*a, **kw)
        print(*a, **kw, file=out)

    p(f'base: {base_co.describe()}    cur: {cur_co.describe()}')
    p(f'benchmarks: {", ".join(str(b) for b in benchmarks)}')
    p(f'thresholds: slower/faster if > {args.threshold*100:.0f}% and > {args.min_diff}s')
    p()
    p(f'{"benchmark":{width}}  {"base[s]":>9}  {"cur[s]":>9}  {"diff[s]":>9}  {"ratio":>6}  {"size b>c":>9}  verdict')
    for r in rows:
        diff = f'{r.diff:+9.3f}' if r.diff is not None else f'{"":>9}'
        ratio = f'{r.ratio:6.2f}' if r.ratio is not None else f'{"":>6}'
        size = f'{fmt_size(r.base):>4}>{fmt_size(r.cur):<4}'
        flags = ' '.join(v for v in (r.verdict if r.verdict != NA else '', r.size_verdict) if v)
        p(f'{short_name(r.bench, root):{width}}  {fmt_time(r.base)}  {fmt_time(r.cur)}  {diff}  {ratio}  {size}  {flags}')

    both = [r for r in rows if r.ratio is not None]
    n = {v: sum(1 for r in rows if r.verdict == v) for v in (LOST, SLOWER, SAME, FASTER, GAINED, NA)}
    ns = {v: sum(1 for r in rows if r.size_verdict == v) for v in (SIZE_UP, SIZE_DOWN)}
    solved_base = sum(1 for r in base.values() if r.status == 'success')
    solved_cur = sum(1 for r in cur.values() if r.status == 'success')
    only_base = sorted(set(base) - set(cur))
    only_cur = sorted(set(cur) - set(base))

    p()
    p('=== summary ===')
    p(f'{"benchmarks compared":40} {len(rows):6}')
    p(f'{"solved by base / cur":40} {solved_base:6} / {solved_cur}')
    p(f'{"LOST   (base solved, cur not)":40} {n[LOST]:6}')
    p(f'{"SLOWER (cur slower than thresholds)":40} {n[SLOWER]:6}')
    p(f'{"about the same":40} {n[SAME]:6}')
    p(f'{"FASTER (cur faster than thresholds)":40} {n[FASTER]:6}')
    p(f'{"GAINED (base unsolved, cur solved)":40} {n[GAINED]:6}')
    p(f'{"unsolved by both":40} {n[NA]:6}')
    p(f'{"solution larger / smaller in cur":40} {ns[SIZE_UP]:6} / {ns[SIZE_DOWN]}')
    if both:
        tb = sum(r.base.time for r in both)
        tc = sum(r.cur.time for r in both)
        geo = math.exp(mean(math.log(max(r.ratio, 1e-6)) for r in both))
        p(f'{"total time solved by both: base / cur":40} {tb:10.3f} / {tc:.3f} s')
        p(f'{"geomean ratio cur/base (solved by both)":40} {geo:10.3f}')
    if only_base:
        p(f'{"only results for base":40} {len(only_base):6}  (e.g. {short_name(only_base[0], root)})')
    if only_cur:
        p(f'{"only results for cur":40} {len(only_cur):6}  (e.g. {short_name(only_cur[0], root)})')

    regressions = [r for r in rows if r.verdict in REGRESSIONS]
    p()
    if regressions:
        p(f'*** {len(regressions)} performance regression(s) found ***')
        for r in regressions:
            p(f'  {r.verdict:6} {short_name(r.bench, root)}: base {fmt_time(r.base).strip()}  cur {fmt_time(r.cur).strip()}')
    else:
        p('no performance regressions found')
    return bool(regressions)

def write_csv(path: Path, rows: list[Row]):
    with open(path, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['benchmark', 'base_status', 'base_time', 'base_size',
                    'cur_status', 'cur_time', 'cur_size', 'diff', 'ratio', 'verdict', 'size_verdict'])
        for r in rows:
            w.writerow([r.bench, r.base.status, r.base.time, r.base.size,
                        r.cur.status, r.cur.time, r.cur.size, r.diff, r.ratio,
                        r.verdict if r.verdict != NA else '', r.size_verdict])

# ----------------------------------------------------------------------------
# main

def parse_args():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('benchmarks', nargs='+', type=Path,
                    help='benchmark directories (each containing *.sl files; not searched recursively)')
    ap.add_argument('--base', default='main', metavar='REF',
                    help='git ref to compare against (default: main)')
    ap.add_argument('--out', type=Path, default=Path('results.perfcmp'), metavar='DIR',
                    help='directory for result files (default: results.perfcmp)')
    ap.add_argument('--timeout', type=int, metavar='S', help='per-benchmark timeout, passed to eval.py')
    ap.add_argument('--trials', type=int, metavar='N', help='trials per benchmark, passed to eval.py')
    ap.add_argument('--force', action='store_true', help='re-run benchmarks that already have results')
    ap.add_argument('--dry', action='store_true', help='only print the commands eval.py would run')
    ap.add_argument('--threshold', type=float, default=0.10, metavar='R',
                    help='relative time change needed to count as slower/faster (default: 0.10)')
    ap.add_argument('--min-diff', type=float, default=0.5, metavar='S',
                    help='absolute time change [s] needed to count as slower/faster (default: 0.5)')
    ap.add_argument('--skip-base', action='store_true', help='do not run the base; reuse results in --out')
    ap.add_argument('--skip-cur', action='store_true', help='do not run the current tree; reuse results in --out')
    ap.add_argument('--keep-worktree', action='store_true', help='keep the temporary worktree of the base')
    return ap.parse_args()

def main():
    args = parse_args()
    repo = Path(git(Path(__file__).resolve().parent, 'rev-parse', '--show-toplevel'))
    if not (repo / 'eval.py').exists():
        die(f'{repo} does not contain eval.py')

    benchmarks = [b.resolve() for b in args.benchmarks]
    for b in benchmarks:
        if not b.is_dir():
            die(f'benchmark directory {b} does not exist')
        if not any(b.glob('*.sl')):
            die(f'benchmark directory {b} contains no *.sl files (subdirectories are not searched)')
    if len({b.name for b in benchmarks}) != len(benchmarks):
        die('benchmark directories must have distinct names (eval.py names experiments after them)')

    cur = current_checkout(repo)
    base_sha = git(repo, 'rev-parse', '--verify', '--quiet', f'{args.base}^{{commit}}', check=False)
    if not base_sha:
        die(f'unknown base ref {args.base!r}')
    if base_sha == cur.sha and not cur.dirty:
        print(f'perfcmp: warning: {args.base} and HEAD are the same commit and the tree is clean;'
              ' you are comparing identical code', file=sys.stderr)

    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)

    worktree: Path | None = None
    try:
        # ---- base -------------------------------------------------------
        base = Checkout('base', args.base, base_sha, False, repo)   # path fixed below
        if not args.skip_base:
            base = add_worktree(repo, args.base, base_sha)
            worktree = base.path
            run_eval(base, base.result_dir(out), benchmarks, args)
        # ---- current ----------------------------------------------------
        if not args.skip_cur:
            run_eval(cur, cur.result_dir(out), benchmarks, args)
    finally:
        if worktree is not None:
            if args.keep_worktree:
                print(f'perfcmp: keeping worktree {worktree}')
            else:
                remove_worktree(repo, worktree)

    if args.dry:
        return 0

    base_res = read_results(base.result_dir(out), benchmarks)
    cur_res = read_results(cur.result_dir(out), benchmarks)
    if not base_res:
        die(f'no base results in {base.result_dir(out)}', 1)
    if not cur_res:
        die(f'no current results in {cur.result_dir(out)}', 1)

    rows = compare(base_res, cur_res, args.threshold, args.min_diff)
    stamp = datetime.now().strftime('%Y%m%d-%H%M%S')
    txt = out / f'comparison-{stamp}.txt'
    with open(txt, 'w') as f:
        banner(f'comparison  (base: {base.result_dir(out).name}, cur: {cur.result_dir(out).name})')
        regressed = report(rows, base_res, cur_res, base, cur, benchmarks, args, f)
    write_csv(out / f'comparison-{stamp}.csv', rows)
    with open(out / f'comparison-{stamp}.json', 'w') as f:
        json.dump({
            'timestamp': stamp,
            'base': {'ref': base.name, 'sha': base.sha, 'results': str(base.result_dir(out))},
            'cur': {'branch': cur.name, 'sha': cur.sha, 'dirty': cur.dirty, 'results': str(cur.result_dir(out))},
            'benchmarks': [str(b) for b in benchmarks],
            'threshold': args.threshold, 'min_diff': args.min_diff,
        }, f, indent=2)
    print(f'\nwritten: {txt}, {txt.with_suffix(".csv")}')
    return 1 if regressed else 0

if __name__ == '__main__':
    try:
        sys.exit(main())
    except subprocess.CalledProcessError as e:
        die(f'command failed with exit code {e.returncode}: {shlex.join(map(str, e.cmd))}', 1)
    except KeyboardInterrupt:
        die('interrupted', 130)
