from synth.spec import Constraint, Problem, SynthFunc
from synth.synth_n import LenCegis
from sygus import logics
from synth.oplib import Bv, R
from synth.util import Debug
from synth.spec import Func
from z3 import *

width = 5
# output of helper g
rg, rgm1, n    = Reals('rg rgm1 n')


def get_spec(n):
    return If(n < 0, 0, ((n * (n + 1)) / 2)) 
# output of sum(n-1)
# rfnminus1 = Int('rfnminus1')

# result is right
correct = rg == If (n > 0, n + rgm1, 0)

# rfnminus1 is input to g
# recursive = rg == get_spec(n - 1, rfnminus1)

constraint = Constraint(
    # constraint on input -> could be violated by samples
    phi=Implies(And(n >= 0, n < 6), correct),
    params=[n],
    function_applications={
        # Kind of a "dependent value" situation, as rfnminus1 depends on the value of n
        'g':   [ ([rg], [n]), ([rgm1], [n - 1]) ],
    }
)

# create the synthesis function specification.
# A synthesis function is specified by its input and output variables
# (pairs of name and sort).
# Additionally, we specify the library of operators to synthesize from.
# The ops map maps each operator to its maximum number of occurrences in the
# synthesized program. None means that the operator can appear to arbitrary often.
# func_sum = SynthFunc(
#     outputs=[ (str(rf), rf.sort()) ],
#     inputs=[ (str(n), n.sort()) ],
#     ops={ op: None for op in (logics['LIA'](0)) }
# )

x, y, z = Reals('x y z')

func_g = SynthFunc(
    outputs=[ (str(rg), rg.sort()) ],
    inputs=[ (str(n), n.sort()) ],
    ops={ op: None for op in (R.ops + [Func('ite', If(z != 0, x, y))])  },
    const_map={ RealVal(i): None for i in range(0, 3) }
)


# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraint=constraint, funcs={'g': func_g})

print(problem)

# Synthesize a program and print it if it exists
prgs, stats = LenCegis(debug=Debug(what="len|cex|synth_prg|synth_constr")).synth_prgs(problem)
print(stats)
if prgs:
    #print(prgs['sum'].to_string(sep='\n'))
    #print("---")
    print(prgs['g'].to_string(sep='\n'))

else:
   print('No program found')
