from synth.spec import Constraint, Problem, SynthFunc, Func
from synth.synth_n import LenCegis
from synth.oplib import Bv
from sygus import logics
from synth.util import Debug
from z3 import *



width   = 128
print("Building bit-vector op library for width", width)
oplib = Bv(width)
print("Built bit-vector op library.")



# define two bit vector variables for the argument and result of the function
r, x    = BitVecs('r x', width)

# an expression that is true if and only if x is a power of 2 or x is 0
sum = r == x & (x-1)

print("Defining constraint...")

constraint = Constraint(
    phi=sum,
    params=[x],
    function_applications={
        'sum': [ ([r], [x]) ]
    }
)

print("Defining synthesis function...")

func = SynthFunc(
    outputs=[ (str(r), r.sort()) ],
    inputs=[ (str(x), x.sort()) ],
    ops={ op: None for op in Bv(width).ops },
    const_map={ BitVecVal(i, width): None for i in range(1, 2) }
)


print("Defining synthesis problem...")

# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraint=constraint, funcs={ 'sum': func })
print(problem)
print()