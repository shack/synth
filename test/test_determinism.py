"""Tests that parsing, grammar optimization and the SMT encoding do not
depend on Python's hash randomization (PYTHONHASHSEED).

Sets of strings (non-terminal names, parameters) and of `Production`
(a frozen dataclass whose hash covers strings) iterate in a
seed-dependent order.  When such an order leaks into
`SynthFunc.nonterminals`, `Nonterminal.parameters`/`productions` or the
constraint list handed to z3, the solver returns different models from
run to run and CEGIS behaviour becomes a lottery.  The canonical order
is the textual order of the grammar.

The main test dumps the parsed grammar, the optimized grammar and the
program constraints in subprocesses under several PYTHONHASHSEED values
and requires the dumps to be identical.

Run as a script:

    python test/test_determinism.py
"""
import os
import subprocess
import sys
from io import StringIO

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from z3 import Solver

from synth.synth_n import DEFAULT_OPT, LenCegis, LenConstraints
from util.sygus import SyGuS

# Grammar of resources/sygus/collection/general/unbdd_inv_gen_fig6.sl:
# several non-terminals referencing each other; optimize_grammar inlines
# Sign into Term and folds Const to "any constant".
FIG6 = """(set-logic LIA)
(synth-fun inv ((y Int)) Bool
    ((Start Bool) (AtomicFormula Bool) (Sum Int) (Term Int) (Sign Int) (Var Int) (Const Int))
    ((Start Bool ((and AtomicFormula AtomicFormula) (or AtomicFormula AtomicFormula)))
    (AtomicFormula Bool ((<= Sum Const) (= Sum Const)))
    (Sum Int ((+ Term Term)))
    (Term Int ((* Sign Var)))
    (Sign Int (0 1 (- 1)))
    (Var Int (y))
    (Const Int ((+ Const Const) (- Const Const) 0 1))))
(declare-var y Int)
(constraint (inv y))
(check-synth)
"""

# Start ::= A | B and A ::= ... | C are chain productions: exercises
# util.sygus.merge_non_terminals and two rounds of the chain loop.
CHAIN = """(set-logic LIA)
(synth-fun f ((x Int) (y Int)) Int
  ((Start Int) (A Int) (B Int) (C Int))
  ((Start Int (A B))
   (A Int (x (+ A A) C))
   (B Int (y 1 (- B B)))
   (C Int (2 (* C C)))))
(declare-var x Int)
(constraint (= (f x 0) x))
(check-synth)
"""

GRAMMARS = [ ('inv', FIG6), ('f', CHAIN) ]
N_INSNS = 3
SEEDS = ('0', '1', '2', '3', 'random')

def func(text, name):
    return SyGuS('test').read_problem(StringIO(text)).funcs[name]

def grammar_lines(f):
    yield f'nonterminals {list(f.nonterminals)}'
    for name, nt in f.nonterminals.items():
        consts = None if nt.constants is None else [ str(c) for c in nt.constants ]
        prods = [ p.sexpr for p in nt.productions ]
        yield f'  {name} params={list(nt.parameters)} prods={prods} consts={consts}'

def dump():
    """Text rendering of everything whose order matters for the encoding."""
    out = []
    for name, text in GRAMMARS:
        f = func(text, name)
        out += [ f'== {name} parsed', *grammar_lines(f) ]
        f = f.optimize_grammar()
        out += [ f'== {name} optimized', *grammar_lines(f) ]
        options = LenCegis(size_range=(0, N_INSNS), opt=DEFAULT_OPT)
        c = LenConstraints(options, name, f, N_INSNS)
        s = Solver()
        c.add_program_constraints(s)
        out += [ f'non_terms {list(c.non_terms)}',
                 f'productions {[ (p.sexpr, list(p.operands)) for p in c.pr_enum ]}',
                 f'types {[ str(t) for t in c.types ]}' ]
        out += [ a.sexpr() for a in s.assertions() ]
    return '\n'.join(out) + '\n'

def run_dump(seed):
    p = subprocess.run([ sys.executable, os.path.abspath(__file__), '--dump' ],
                       capture_output=True, text=True, cwd=ROOT,
                       env=dict(os.environ, PYTHONHASHSEED=seed))
    assert p.returncode == 0, (seed, p.stderr)
    return p.stdout

def test_encoding_independent_of_hash_seed():
    dumps = { seed: run_dump(seed) for seed in SEEDS }
    ref_seed = SEEDS[0]
    ref = dumps[ref_seed]
    for seed, d in dumps.items():
        if d == ref:
            continue
        a, b = ref.splitlines(), d.splitlines()
        i = next((k for k, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
        get = lambda l: l[i] if i < len(l) else '<eof>'
        assert False, f'PYTHONHASHSEED={seed} differs from PYTHONHASHSEED={ref_seed} ' \
                      f'at line {i}:\n  {get(a)}\n  {get(b)}'

def test_canonical_orders():
    inv = func(FIG6, 'inv')
    assert inv.nonterminals['AtomicFormula'].referenced_non_terminals() == ('Sum', 'Const')
    # Sign is inlined into Term and therefore dropped
    assert list(inv.optimize_grammar().nonterminals) == \
        [ 'Start', 'AtomicFormula', 'Sum', 'Term', 'Var', 'Const' ]

    f = func(CHAIN, 'f')
    assert list(f.nonterminals) == [ 'Start', 'A', 'B', 'C' ]
    start = f.nonterminals['Start']
    assert start.parameters == ('x', 'y')
    assert [ p.sexpr for p in start.productions ] == \
        [ '(+ {0} {1})', '(- {0} {1})', '(* {0} {1})' ]
    assert [ str(c) for c in start.constants ] == [ '1', '2' ]
    assert [ p.sexpr for p in f.nonterminals['A'].productions ] == \
        [ '(+ {0} {1})', '(* {0} {1})' ]
    assert list(f.optimize_grammar().nonterminals) == [ 'Start', 'A', 'B', 'C' ]

def main():
    tests = [ (n, f) for n, f in sorted(globals().items())
                if n.startswith('test_') and callable(f) ]
    for name, f in tests:
        print(name)
        f()
        print('  ok')
    print(f'{len(tests)} tests passed')

if __name__ == '__main__':
    if sys.argv[1:] == [ '--dump' ]:
        sys.stdout.write(dump())
    else:
        main()
