from synth.spec import Constraint, Problem, SynthFunc
from synth.synth_n import LenCegis
from sygus import logics
from synth.oplib import Bv
from synth.util import Debug
from synth.spec import Func
from z3 import *

width = 8
# output of helper g
rg, n, k    = BitVecs('rg n k', width)

def get_spec(n):
    return If(n < 0, 0, ((n * (n + 1)) / 2))

# output of sum(n-1)
rfnminus1 = BitVec('rfnminus1', width)

constraint = Constraint(
    phi=And(rg == get_spec(n)),
    params=[n],
    function_applications={
        'g':   [ ([rg], [n]) ]
    }
)

# op definition for recf
rec_in = BitVec('rec_in', width)
recf = Func('recf', get_spec(rec_in), precond=rec_in < n, )

func_g = SynthFunc(
    outputs=[ (str(rg), rg.sort()) ],
    inputs=[ (str(n), n.sort()) ],
    ops=# { op: None for op in Bv(width).simple_ops} |
    { recf: None }
)

# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraint=constraint, funcs={'g': func_g })

# Synthesize a program and print it if it exists
prgs, stats = LenCegis(debug=Debug(what="len|cex|synth_prg|synth_constr")).synth_prgs(problem)
print(stats)
if prgs:
    #print(prgs['sum'].to_string(sep='\n'))
    #print("---")
    print(prgs['g'].to_string(sep='\n'))
else:
   print('No program found')