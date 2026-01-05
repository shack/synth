from synth.spec import Constraint, Problem, SynthFunc
from synth.synth_n import LenCegis
from synth.oplib import Bv
from sygus import logics
from synth.util import Debug
from z3 import *

# set bit width to 8
width   = 16
# define two bit vector variables for the argument and result of the function
r, x    = BitVecs('r x', width)

sum = r == x & (x-1)


smaller_width = 8
abs_r = BitVec('abs_r', smaller_width)
smaller_sum = Extract(7, 0, r) == abs_r

constraint = Constraint(
    phi=And(sum, smaller_sum),
    params=[x],
    function_applications={
        'sum': [ ([abs_r], [Extract(7, 0, x)]) ]
    }
)

func = SynthFunc(
    outputs=[ (str(abs_r), abs_r.sort()) ],
    inputs=[ (str(x), abs_r.sort()) ],
    ops={ op: None for op in Bv(smaller_width).ops }
)

# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraint=constraint, funcs={ 'sum': func })

# Synthesize a program and print it if it exists
prgs, stats = LenCegis(debug=Debug(what="len|cex|synth_prg"), verbose=True).synth_prgs(problem)
if prgs:
    print(prgs['sum'].to_string(sep='\n'))
else:
   print('No program found')
