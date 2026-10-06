"""Tests for the aggregation of run results in eval.util.

Run as a script:

    python test/test_eval.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from eval.util import aggregate_wall_time, aggregate_cpu_time, aggregate_result_size

NS = 1_000_000_000
SOLUTION = '(\n(define-fun f ((x Int)) Int (+ x x))\n)\n'

def run(stdout, secs=2, status='success'):
    """A result as written by Run.run."""
    return { 'status': status, 'tag': 't', 'wall_time': secs * NS, 'cpu_time': secs * NS, 'stdout': stdout }

TIMEOUT = { 'status': 'timeout', 'tag': 't', 'wall_time': 300 * NS, 'cpu_time': 300 * NS }
ERROR = { 'status': 'error', 'tag': 't', 'wall_time': 0, 'returncode': 1, 'error': 'x' }

def check_eq(name, got, expected):
    if got != expected:
        raise AssertionError(f'{name}: expected {expected!r}, got {got!r}')
    print(f'  ok  {name}')

def test_solved():
    check_eq('wall', aggregate_wall_time([run(SOLUTION)]), 2)
    check_eq('cpu', aggregate_cpu_time([run(SOLUTION)]), 2)
    check_eq('size', aggregate_result_size([run(SOLUTION)]) is not None, True)

def test_no_answer():
    # times of runs without an answer are not reported
    for name, trial in [ ('fail', run('fail\n')), ('fail_paren', run('(fail)')),
                         ('empty', run('')), ('timeout', TIMEOUT), ('error', ERROR) ]:
        for agg in (aggregate_wall_time, aggregate_cpu_time, aggregate_result_size):
            check_eq(f'{name}_{agg.__name__}', agg([trial]), None)

def test_infeasible():
    # infeasible is an answer, so it has a time, but no size
    for out in ('infeasible\n', '(infeasible)'):
        check_eq(f'{out.strip()}_wall', aggregate_wall_time([run(out)]), 2)
        check_eq(f'{out.strip()}_cpu', aggregate_cpu_time([run(out)]), 2)
        check_eq(f'{out.strip()}_size', aggregate_result_size([run(out)]), None)

def test_trials():
    check_eq('mean', aggregate_wall_time([run(SOLUTION, 1), run(SOLUTION, 3)]), 2)
    check_eq('with_infeasible', aggregate_wall_time([run(SOLUTION, 1), run('infeasible', 3)]), 2)
    check_eq('one_unsolved', aggregate_wall_time([run(SOLUTION, 1), run('fail', 3)]), None)
    check_eq('one_timeout', aggregate_cpu_time([run(SOLUTION, 1), TIMEOUT]), None)
    check_eq('no_trials', aggregate_wall_time([]), None)

def main():
    tests = [ (n, f) for n, f in sorted(globals().items()) if n.startswith('test_') and callable(f) ]
    for name, f in tests:
        print(name)
        f()
    print(f'{len(tests)} tests passed')

if __name__ == '__main__':
    main()
