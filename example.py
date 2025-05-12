from synth.spec import Func, Spec, Task
from synth.synth_n import LenCegis
from synth.oplib import Bv
from synth.util import Debug
from z3 import *

# set bit width to 8
width   = 8
# define two bit vector variables for the argument and result of the function
q, r, x, y = BitVecs('q r x y', width)

# spec    = Spec('test', Exists([q] , And([q == ~x & y, q != r])), [r], [x, y])
spec    = Spec('test', r == x + y, [r], [x, y])

# create a sythesis task from the specification
# and the library of all bit vector operations.
# each operation can appear arbitrary often in the synthesized program
# which is indicarted by the dictiotnary value `None`.
task    = Task(spec, {op: None for op in Bv(width).simple_ops }, max_const=None)

# Synthesize a program and print it if it exists
synth = LenCegis(debug=Debug(level=1), no_const_expr=True, no_semantic_eq=True, size_range=(1, 6))
for prg, stats in synth.synth_all(task):
    print(prg)