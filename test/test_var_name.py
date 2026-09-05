"""Tests for `Prg.var_name`, which names the `let`-bound temporaries of an
emitted define-fun.

A temporary used to be called `x<i>` for its index `i` in the program, without
regard for the parameters of the synth-fun.  Since `i` counts from `n_inputs`,
a synth-fun that numbers its parameters from 1 -- `max6 ((x1 Int) ... (x6 Int))`
-- has a parameter whose name is exactly the one the first temporary wants.
The emitted `(let ((x6 ...)) ...)` then shadows that parameter, and every later
reference to it silently reads the temporary instead.  The program the solver
found is correct; only its serialization is wrong.

Run as a script:

    python test/test_var_name.py
"""
import os
import re
import sys
from io import StringIO

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from synth.spec import Prg, Signature
from util.sygus import SyGuS, parse_solution
from util.check import check, follows_grammar

def problem(text):
    return SyGuS('test').read_problem(StringIO(text))

def solution(text):
    return parse_solution(StringIO(text))

def emit(prg, name):
    """Print a program the way sygus.py does."""
    return prg.copy_propagation().dce().sexpr(name)

def derive(prob, sol_text, fun='f'):
    """Turn a solution term into the `Prg` the synthesizer would have found.

       This is the same trick `test_copy_propagation.py` uses: deriving a given
       term over the grammar produces a real program without paying for search,
       and the program then goes through the ordinary emit path."""
    res = follows_grammar(prob.funcs[fun], solution(sol_text)[fun])
    assert res.follows_grammar, res.error
    return res.prgs[0]

def let_names(sexpr):
    """The names bound by the `let`s of an emitted define-fun."""
    return re.findall(r'\(let \(\((\S+) ', sexpr)

def check_no_shadowing(prg, name):
    """No `let` may bind a name that is already a parameter, and no name may be
       bound twice."""
    printed = emit(prg, name)
    bound   = let_names(printed)
    clash   = [ n for n in bound if n in prg.input_names ]
    assert not clash, f'{printed}\n  let-bound {clash} shadows a parameter'
    assert len(set(bound)) == len(bound), f'{printed}\n  duplicate let name'
    return printed

# ---------------------------------------------------------------------------
# The parameters are `y` and `x2`, so `n_inputs` is 2 and the first temporary
# wants the name `x2`.  `Start` is reachable only through `(+ x2 Sub)` and
# `Sub` cannot mention `x2`, so the first instruction is guaranteed to sit
# inside `Sub` and the parameter `x2` is guaranteed to be read after it.

SILENT = """
(set-logic LIA)
(synth-fun f ((y Int) (x2 Int)) Int
  ((Start Int) (Sub Int))
  ((Start Int ((+ x2 Sub)))
   (Sub  Int (y (+ Sub Sub)))))
(declare-var y Int)
(declare-var x2 Int)
(constraint (= (f y x2) (+ x2 (+ y (+ y y)))))
(check-synth)
"""

SILENT_SOL = '(\n(define-fun f ((y Int) (x2 Int)) Int (+ x2 (+ y (+ y y))))\n)\n'

def test_temporary_does_not_shadow_parameter():
    prob = problem(SILENT)
    check_no_shadowing(derive(prob, SILENT_SOL), 'f')

def test_shadowed_parameter_keeps_its_meaning():
    """The emitted term must still be `x2 + 3y`.  Under the shadowing it
       reduced to `5y`, which satisfies neither the grammar nor the
       constraint -- so `check` sees it, but only after the fact."""
    prob = problem(SILENT)
    printed = emit(derive(prob, SILENT_SOL), 'f')
    res = check(prob, solution(f'(\n{printed}\n)'))
    assert res.follows_grammar, f'{printed}\n  {res}'
    assert res.satisfies_constraints, f'{printed}\n  {res}'

# ---------------------------------------------------------------------------
# The same collision with a Bool temporary: the emitted term is not even
# well-sorted, because the `ite` condition and its then-branch end up being
# the same name.

ILL_SORTED = """
(set-logic LIA)
(synth-fun f ((y Int) (x2 Int)) Int
  ((Start Int) (B Bool))
  ((Start Int (y x2 0 (ite B Start Start)))
   (B Bool ((>= Start Start)))))
(declare-var y Int)
(declare-var x2 Int)
(constraint (= (f y x2) (ite (>= y 0) x2 y)))
(check-synth)
"""

ILL_SORTED_SOL = '(\n(define-fun f ((y Int) (x2 Int)) Int (ite (>= y 0) x2 y))\n)\n'

def test_bool_temporary_does_not_shadow_int_parameter():
    prob = problem(ILL_SORTED)
    printed = check_no_shadowing(derive(prob, ILL_SORTED_SOL), 'f')
    res = check(prob, solution(f'(\n{printed}\n)'))
    assert res.follows_grammar and res.satisfies_constraints, f'{printed}\n  {res}'

# ---------------------------------------------------------------------------
# The grammar of resources/sygus/collection/general/max6.sl, the smallest of
# the ten shipped synth-funs that number their parameters from 1.  Deriving
# any solution that reads `x6` after the first instruction exercises the
# collision without paying for the search.

MAX6 = """
(set-logic LIA)
(synth-fun f ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int) (x6 Int)) Int
    ((Start Int) (StartBool Bool))
    ((Start Int (x1 x2 x3 x4 x5 x6 0 1 (+ Start Start) (- Start Start) (ite StartBool Start Start)))
    (StartBool Bool ((and StartBool StartBool) (or StartBool StartBool) (not StartBool) (<= Start Start) (= Start Start) (>= Start Start)))))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(constraint (= (f x1 x2 x3 x4 x5 x6) (ite (>= x1 x2) x6 x2)))
(check-synth)
"""

MAX6_SOL = ('(\n(define-fun f ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int) (x6 Int)) Int'
            ' (ite (>= x1 x2) x6 x2))\n)\n')

def test_shipped_one_based_parameters():
    prob = problem(MAX6)
    prg  = derive(prob, MAX6_SOL)
    assert prg.input_names[-1] == 'x6' and prg.n_inputs == 6
    check_no_shadowing(prg, 'f')

def test_shipped_one_based_parameters_stay_well_sorted():
    """`(ite (>= x1 x2) x6 x2)` became `(ite x6 x6 x2)` -- the Bool temporary
       in the condition displaced the Int parameter in the then-branch."""
    prob = problem(MAX6)
    printed = emit(derive(prob, MAX6_SOL), 'f')
    assert '(ite x6 x6' not in printed, printed
    res = check(prob, solution(f'(\n{printed}\n)'))
    assert res.follows_grammar and res.satisfies_constraints, f'{printed}\n  {res}'

# ---------------------------------------------------------------------------
# The renaming has to keep going when the obvious alternative is taken too.

ESCALATE = """
(set-logic LIA)
(synth-fun f ((x2 Int) (x2_0 Int)) Int
  ((Start Int) (Sub Int))
  ((Start Int ((+ x2 Sub)))
   (Sub  Int (x2_0 (+ Sub Sub)))))
(declare-var x2 Int)
(declare-var x2_0 Int)
(constraint (= (f x2 x2_0) (+ x2 (+ x2_0 (+ x2_0 x2_0)))))
(check-synth)
"""

ESCALATE_SOL = ('(\n(define-fun f ((x2 Int) (x2_0 Int)) Int'
                ' (+ x2 (+ x2_0 (+ x2_0 x2_0))))\n)\n')

def test_renaming_skips_further_taken_names():
    prob = problem(ESCALATE)
    printed = check_no_shadowing(derive(prob, ESCALATE_SOL), 'f')
    res = check(prob, solution(f'(\n{printed}\n)'))
    assert res.follows_grammar and res.satisfies_constraints, f'{printed}\n  {res}'

# ---------------------------------------------------------------------------
# Parameters numbered from 0 can never collide -- a temporary's index is at
# least `n_inputs` -- so those programs must be printed exactly as before.
# This is what keeps the fix a no-op on the rest of the corpus.

ZERO_BASED = """
(set-logic LIA)
(synth-fun f ((x0 Int) (x1 Int)) Int
  ((Start Int) (Sub Int))
  ((Start Int ((+ x0 Sub)))
   (Sub  Int (x1 (+ Sub Sub)))))
(declare-var x0 Int)
(declare-var x1 Int)
(constraint (= (f x0 x1) (+ x0 (+ x1 (+ x1 x1)))))
(check-synth)
"""

ZERO_BASED_SOL = ('(\n(define-fun f ((x0 Int) (x1 Int)) Int'
                  ' (+ x0 (+ x1 (+ x1 x1))))\n)\n')

def test_zero_based_parameters_are_not_renamed():
    prob = problem(ZERO_BASED)
    prg  = derive(prob, ZERO_BASED_SOL)
    printed = check_no_shadowing(prg, 'f')
    # the temporaries keep their plain names; only the output is named `res`
    bound = [ n for n in let_names(printed) if n not in prg.output_names ]
    assert all(re.fullmatch(r'x\d+', n) for n in bound), printed

def test_var_name_is_unchanged_without_a_collision():
    prob = problem(ZERO_BASED)
    prg  = derive(prob, ZERO_BASED_SOL)
    for i in range(prg.n_inputs, prg.n_inputs + len(prg)):
        if i not in prg.output_map:
            assert prg.var_name(i) == f'x{i}', (i, prg.var_name(i))

# ---------------------------------------------------------------------------
# `var_name` also keeps clear of the *output* names, which `Prg.sexpr` binds
# with a `let` of their own.  No front door produces such a clash today -- the
# SyGuS reader always calls the output `res` (util/sygus.py) and
# `synth_func_from_ops` calls them `r<i>` (spec.py), and neither can equal
# `x<i>`.  The signature is therefore built by hand, so that the guarantee is
# pinned rather than left to the accident of how outputs happen to be named.

RENAMED_OUTPUT = """
(set-logic LIA)
(synth-fun f ((y Int) (z Int)) Int
  ((Start Int) (Sub Int))
  ((Start Int ((+ z Sub)))
   (Sub  Int (y (+ Sub Sub)))))
(declare-var y Int)
(declare-var z Int)
(constraint (= (f y z) (+ z (+ y (+ y y)))))
(check-synth)
"""

RENAMED_OUTPUT_SOL = ('(\n(define-fun f ((y Int) (z Int)) Int'
                      ' (+ z (+ y (+ y y))))\n)\n')

def test_temporary_does_not_shadow_output_name():
    prg  = derive(problem(RENAMED_OUTPUT), RENAMED_OUTPUT_SOL)
    # the same program, but with its output called `x2` -- the name the first
    # temporary wants
    sig  = Signature(outputs=[ ('x2', prg.sig.outputs[0][1]) ], inputs=prg.sig.inputs)
    prg  = Prg(sig, prg.insns, prg.outputs, prg.weights)
    assert prg.output_names == [ 'x2' ]
    out     = prg.copy_propagation().dce()
    printed = out.sexpr('f')
    temps   = [ out.var_name(i) for i in range(out.n_inputs, out.n_inputs + len(out))
                  if i not in out.output_map ]
    clash   = [ n for n in temps if n in out.output_names ]
    assert not clash, f'{printed}\n  temporary {clash} shadows an output name'
    bound   = let_names(printed)
    assert len(set(bound)) == len(bound), f'{printed}\n  duplicate let name'

# ---------------------------------------------------------------------------

def main():
    tests = [ (n, f) for n, f in sorted(globals().items())
                if n.startswith('test_') and callable(f) ]
    for name, f in tests:
        print(name)
        f()
        print('  ok')
    print(f'{len(tests)} tests passed')

if __name__ == '__main__':
    main()
