"""Tests for util.convert (SyGuS-IF 2.x <-> 1.0).

Run as a script:

    python test/test_convert.py
"""
import os
import sys
from io import StringIO

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from util.convert import NewToOld, OldToNew

def convert(conv, text):
    out = StringIO()
    conv(StringIO(text), out)
    return ' '.join(out.getvalue().split())

def check_eq(name, got, expected):
    if got != expected:
        raise AssertionError(f'{name}: mismatch\n  expected: {expected!r}\n  got:      {got!r}')
    print(f'  ok  {name}')

NEW = """
(synth-fun f ((x Int)) Int ((Start Int)) ((Start Int (x 0 (- 1) (- 2.5) (- Start) (- Start Start)))))
(constraint (= (f (- 3)) (- x 1)))
"""

def test_negative_literals():
    check_eq('new_to_old', convert(NewToOld(), NEW),
             '(synth-fun f ((x Int)) Int ((Start Int (x 0 -1 -2.5 (- Start) (- Start Start))))) '
             '(constraint (= (f -3) (- x 1)))')
    check_eq('new_to_old_keep', convert(NewToOld(negative_literals=False), NEW),
             '(synth-fun f ((x Int)) Int ((Start Int (x 0 (- 1) (- 2.5) (- Start) (- Start Start))))) '
             '(constraint (= (f (- 3)) (- x 1)))')

BV_NEW = '(synth-fun f ((x (_ BitVec 8))) (_ BitVec 8) ((Start (_ BitVec 8))) ((Start (_ BitVec 8) (x (bvneg Start)))))'
BV_OLD = '(synth-fun f ((x (BitVec 8))) (BitVec 8) ((Start (BitVec 8) (x (bvneg Start)))))'

def test_bit_vectors():
    check_eq('bv_new_to_old', convert(NewToOld(), BV_NEW), BV_OLD)
    check_eq('bv_old_to_new', convert(OldToNew(), BV_OLD), BV_NEW)

NULLARY_OLD = """
(synth-fun fb () Int ((Start Int ((Constant Int)))))
(synth-fun g ((x Int)) Int ((Start Int (x (fb)))))
(define-fun c () Int 3)
(define-fun d ((x Int)) Int (+ x (c)))
(constraint (= (g (fb)) (+ (fb) (d (c)))))
"""

def test_nullary_applications():
    # (f) -> f in terms; the rule list (fb) of g's grammar stays a list
    check_eq('nullary', convert(OldToNew(), NULLARY_OLD),
             '(synth-fun fb () Int ((Start Int)) ((Start Int ((Constant Int))))) '
             '(synth-fun g ((x Int)) Int ((Start Int)) ((Start Int (x (fb))))) '
             '(define-fun c () Int 3) '
             '(define-fun d ((x Int)) Int (+ x c)) '
             '(constraint (= (g fb) (+ fb (d c))))')

def main():
    tests = [ (n, f) for n, f in sorted(globals().items()) if n.startswith('test_') and callable(f) ]
    for name, f in tests:
        print(name)
        f()
    print(f'{len(tests)} tests passed')

if __name__ == '__main__':
    main()
