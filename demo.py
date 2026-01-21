from synth.spec import Constraint, Problem, SynthFunc, Spec, Task, synth_func_from_ops
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
        ('is_pow2', (x,)): (r,)
    }
)

# Create the synthesis function specification.
# This function takes a list of operators and creates a SyGuS grammar
# based on the operator types.
# Note that there is an explicit API to create more complex grammars explicitly.
func = synth_func_from_ops([ x.sort() ], [ r.sort() ], Bv(width).ops)
print(func)

# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraints=[constraint], funcs={ 'is_pow2': func })

# Synthesize a program and print it if it exists
prgs, stats = LenCegis().synth_prgs(problem)
if prgs:
    print(prgs['is_pow2'].to_string(sep='\n'))
else:
   print('No program found')

# For functional specifications and simple grammars, we can also use the
# convenient Task interface:
spec = Spec('is_pow2', If(is_pow2, r == 0, r != 0), inputs=[x], outputs=[r])
problem = Task(spec, Bv(width).ops)

# Synthesize a program and print it if it exists
prgs, stats = LenCegis().synth_prgs(problem)
if prgs:
    print(prgs['is_pow2'].to_string(sep='\n'))
else:
   print('No program found')