"""Tests for util.size.inline_let and util.size.cse.

Run as a script:

    python test/test_size.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from util.size import inline_let, cse


def check_eq(name, got, expected):
    if got != expected:
        raise AssertionError(
            f'{name}: mismatch\n  expected: {expected!r}\n  got:      {got!r}'
        )
    print(f'  ok  {name}')


def check_roundtrip(name, term, vars):
    """cse should be a right-inverse of inline_let: inlining its output
    must recover the original term (which has no let)."""
    encoded = cse(term, vars)
    inlined = inline_let(encoded, vars)
    if inlined != term:
        raise AssertionError(
            f'{name}: round-trip failed\n'
            f'  original: {term!r}\n'
            f'  cse out:  {encoded!r}\n'
            f'  inlined:  {inlined!r}'
        )
    print(f'  ok  {name}')


# ---------------------------------------------------------------------------
# inline_let
# ---------------------------------------------------------------------------

def test_inline_no_let():
    t = ('+', 'x', 'y')
    check_eq('inline_no_let', inline_let(t, {'x', 'y'}), ('+', 'x', 'y'))


def test_inline_simple():
    # let v = x in (+ v v)  -->  (+ x x)
    t = ['let', [['v', 'x']], ('+', 'v', 'v')]
    check_eq('inline_simple', inline_let(t, {'x'}), ('+', 'x', 'x'))


def test_inline_nested():
    # let a = x in let b = (+ a 1) in (* b b)  -->  (* (+ x 1) (+ x 1))
    t = ['let', [['a', 'x']],
            ['let', [['b', ('+', 'a', '1')]],
                ('*', 'b', 'b')]]
    check_eq('inline_nested', inline_let(t, {'x'}),
             ('*', ('+', 'x', '1'), ('+', 'x', '1')))


def test_inline_shadowing():
    # let v = a in let v = b in v  -->  b
    t = ['let', [['v', 'a']],
            ['let', [['v', 'b']], 'v']]
    check_eq('inline_shadowing', inline_let(t, set()), 'b')


def test_inline_parallel_bindings():
    # let a = p, b = q in (+ a b)  -->  (+ p q)
    t = ['let', [['a', 'p'], ['b', 'q']], ('+', 'a', 'b')]
    check_eq('inline_parallel_bindings', inline_let(t, set()), ('+', 'p', 'q'))


def test_inline_parallel_not_sequential():
    # SMT-LIB / SyGuS `let` is *parallel*: rhs of one binding does NOT see
    # the others. Construct a term whose result distinguishes the two:
    #
    #     let a = x in let a = y, b = a in b
    #
    # Parallel:   inner `b = a` sees the *outer* a (= x)  ==> result: x
    # Sequential: inner `b = a` sees the *new*   a (= y)  ==> result: y
    t = ['let', [['a', 'x']],
            ['let', [['a', 'y'], ['b', 'a']], 'b']]
    check_eq('inline_parallel_not_sequential', inline_let(t, {'x', 'y'}), 'x')


# ---------------------------------------------------------------------------
# cse — round-trip property (should always hold if cse is correct)
# ---------------------------------------------------------------------------

def test_rt_bare_variable():
    check_roundtrip('rt_bare_variable', 'x', {'x'})


def test_rt_no_repetition():
    check_roundtrip('rt_no_repetition', ('+', 'x', ('*', 'y', 'z')), {'x', 'y', 'z'})


def test_rt_single_repeat():
    t = ('+', ('*', 'x', 'y'), ('*', 'x', 'y'))
    check_roundtrip('rt_single_repeat', t, {'x', 'y'})


def test_rt_nested_repeat():
    inner = ('-', 'x', 'y')
    mid = ('*', inner, inner)
    t = ('+', mid, mid)
    check_roundtrip('rt_nested_repeat', t, {'x', 'y'})


def test_rt_repeated_variable():
    # A variable repeated many times shouldn't break anything.
    t = ('+', 'x', 'x', 'x')
    check_roundtrip('rt_repeated_variable', t, {'x'})


def test_rt_collision_trigger():
    # *** Bug-triggering case ***
    # No shared subexpressions, but the bookkeeping collision in cse
    # (count vs len(vn)) reuses the same generated name for two different
    # subterms.
    t = ('+', 'a', ('-', 'a', 'b'))
    check_roundtrip('rt_collision_trigger', t, set())


def test_rt_collision_trigger_with_vars():
    # Same shape, but a/b declared as variables. cse currently only renames
    # *non-variable* atoms, so this case may pass while the previous fails.
    t = ('+', 'a', ('-', 'a', 'b'))
    check_roundtrip('rt_collision_trigger_with_vars', t, {'a', 'b'})


def test_rt_many_atoms():
    # Multiple distinct free-atom names exercise the len(vn) counter.
    t = ('f', 'a', 'b', 'c', ('g', 'a', 'd'))
    check_roundtrip('rt_many_atoms', t, set())


def test_rt_int_atoms():
    # Atoms aren't always strings — numeric literals must work too.
    t = ('+', 'x', 1, ('*', 2, 'x'))
    check_roundtrip('rt_int_atoms', t, {'x'})


def test_rt_repeated_int_atom():
    # The same integer constant appearing twice should be CSE'd to one name.
    t = ('+', 7, ('*', 7, 'x'))
    encoded = cse(t, {'x'})
    inlined = inline_let(encoded, {'x'})
    if inlined != t:
        raise AssertionError(
            f'rt_repeated_int_atom: round-trip failed\n'
            f'  original: {t!r}\n  cse out:  {encoded!r}\n  inlined:  {inlined!r}'
        )
    # And the int 7 should only appear once on the rhs of a let binding.
    seven_count = repr(encoded).count(' 7')
    if seven_count != 1:
        raise AssertionError(
            f'rt_repeated_int_atom: expected 7 to be bound once, got {seven_count} occurrences in {encoded!r}'
        )
    print('  ok  rt_repeated_int_atom')


def test_rt_bool_atoms():
    t = ('and', True, ('or', False, 'p'))
    check_roundtrip('rt_bool_atoms', t, {'p'})


# ---------------------------------------------------------------------------
# cse — fresh-name property
# ---------------------------------------------------------------------------

def test_cse_avoids_capturing_existing_names():
    # If the term already contains 'v0' as a free name, cse must not reuse
    # 'v0' for a freshly-introduced binding (capture).
    t = ('+', ('*', 'v0', 'w'), ('*', 'v0', 'w'))
    encoded = cse(t, {'v0', 'w'})
    inlined = inline_let(encoded, {'v0', 'w'})
    if inlined != t:
        raise AssertionError(
            f'cse_avoids_capturing_existing_names: round-trip failed\n'
            f'  original: {t!r}\n'
            f'  cse out:  {encoded!r}\n'
            f'  inlined:  {inlined!r}'
        )
    print('  ok  cse_avoids_capturing_existing_names')


def main():
    tests = [
        test_inline_no_let,
        test_inline_simple,
        test_inline_nested,
        test_inline_shadowing,
        test_inline_parallel_bindings,
        test_inline_parallel_not_sequential,
        test_rt_bare_variable,
        test_rt_no_repetition,
        test_rt_single_repeat,
        test_rt_nested_repeat,
        test_rt_repeated_variable,
        test_rt_collision_trigger,
        test_rt_collision_trigger_with_vars,
        test_rt_many_atoms,
        test_rt_int_atoms,
        test_rt_repeated_int_atom,
        test_rt_bool_atoms,
        test_cse_avoids_capturing_existing_names,
    ]
    failed = []
    for t in tests:
        try:
            t()
        except AssertionError as e:
            print(f'FAIL  {t.__name__}: {e}')
            failed.append(t.__name__)
    if failed:
        print(f'\n{len(failed)} of {len(tests)} test(s) failed: {failed}')
        sys.exit(1)
    else:
        print(f'\nAll {len(tests)} tests passed.')


if __name__ == '__main__':
    main()
