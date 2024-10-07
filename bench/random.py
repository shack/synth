import random
import itertools

from dataclasses import dataclass

from synth.oplib import Bl
from synth.spec import Func

from bench.util import Bench

from z3 import *

def _create_random_formula(inputs, size, ops):
    assert size > 0
    def create(size):
        nonlocal inputs, ops
        assert size > 0
        if size == 1:
            return random.choice(inputs)
        elif size == 2:
            op = random.choice([op for op, n in ops if n == 1])
            return op(create(1))
        else:
            size -= 1
            op, arity = random.choice(ops)
            assert arity <= 2
            if arity == 1:
                return op(create(size))
            else:
                assert arity == 2
                szl = random.choice(range(size - 1)) + 1
                szr = size - szl
                return op(create(szl), create(szr))
    return create(size)

def _create_random_dnf(inputs, clause_probability=50):
    """Creates a random DNF formula.

    Attributes:
    inputs: List of Z3 variables that determine the number of variables in the formula.
    clause_probability: Probability of a clause being added to the formula.
    seed: Seed for the random number generator.

    This function iterates over *all* clauses, and picks based on the
    clause_probability if a clause is added to the formula.
    Therefore, the function's running time is exponential in the number of variables.
    """
    # sample function results
    clauses = []
    for vals in itertools.product(*[range(2)] * len(inputs)):
        if random.choice(range(100)) < clause_probability:
            clauses += [ And([ inp if pos else Not(inp) for inp, pos in zip(inputs, vals) ]) ]
    return Or(clauses)

@dataclass
class Random:
    """Boolean formulas that are randomly generated."""

    seed: int = 0x5aab199e
    """Seed for the random number generator."""

    def __post_init__(self):
        random.seed(self.seed)

    def random_test(self, name, n_vars, create_formula):
        ops  = [ Bl.and2, Bl.or2, Bl.xor2, Bl.not1 ]
        spec = Func('rand', create_formula([ Bool(f'x{i}') for i in range(n_vars) ]))
        return Bench(name, spec, ops, consts={}, theory='QF_BV')

    def test_rand(self, size=40, n_vars=4):
        ops = [ (And, 2), (Or, 2), (Xor, 2), (Not, 1) ]
        f   = lambda x: _create_random_formula(x, size, ops)
        return self.random_test('rand_formula', n_vars, f)

    def test_rand_dnf(self, n_vars=4):
        f = lambda x: _create_random_dnf(x)
        return self.random_test('rand_dnf', n_vars, f)