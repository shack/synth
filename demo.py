from synth.spec import Constraint, Problem, SynthFunc
from synth.synth_n import LenCegis
from synth.oplib import Bv
from z3 import *

# set bit width to 8
width   = 8
# define two bit vector variables for the argument and result of the function
r, x    = BitVecs('r x', width)

# an expression that is true if and only if x is a power of 2 or x is 0
is_pow2 = Or([x == 0] + [BitVecVal(1 << i, width) == x for i in range(width)])

# define the specification of the function to synthesize by means
# of a synthesis constraint. Note that the specification is
# non-deterministic because multiple values of r satisfy the specification
# in case the value of x is not a power of 2.
# The function_applications parameter lists all applications of the
# function to be synthesized. This is done by specifying the output
# variables (here: r) and the corresponding input expressions (here: x).
# Note that the synthesis constraint may refer to multiple functions
# and each of the functions may be applied multiple times in the constraint.
constraint = Constraint(
    phi=If(is_pow2, r == 0, r != 0),
    params=[x],
    function_applications={
        'is_pow2': [ ([r], [x]) ]
    }
)

# create the synthesis function specification.
# A synthesis function is specified by its input and output variables
# (pairs of name and sort).
# Additionally, we specify the library of operators to synthesize from.
# The ops map maps each operator to its maximum number of occurrences in the
# synthesized program. None means that the operator can appear to arbitrary often.
func = SynthFunc(
    outputs=[ (str(r), r.sort()) ],
    inputs=[ (str(x), x.sort()) ],
    ops={ op: None for op in Bv(width).ops }
)

# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraint=constraint, funcs={ 'is_pow2': func })

# Synthesize a program and print it if it exists
prgs, stats = LenCegis().synth_prgs(problem)
if prgs:
    print(prgs['is_pow2'].to_string(sep='\n'))
else:
   print('No program found')
