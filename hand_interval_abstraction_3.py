
from synth.spec import Constraint, Problem, Production, Nonterminal, SynthFunc, Func, synth_func_from_ops
from synth.synth_n import LenCegis
from synth.oplib import Bv, Interval, I, InfInterval
from sygus import logics
from synth.util import Debug
from z3 import *



x, y, z = Ints('x y z')
correct = z == x - y

constraint = Constraint(
    phi=correct,
    params=[x, y],
    function_applications={
        ('sum', (x, y)): (z,)
    }
)

func = synth_func_from_ops(
    out_types=[ z.sort() ],
    in_types=[ x.sort(), y.sort() ],
    ops={ op: None for op in I.ops },
    const_map={ IntVal(i): None for i in range(0, 3) }
)

# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraints=[constraint], funcs={ 'sum': func })
print(problem)
print()


abs_func = synth_func_from_ops(
    out_types=[ InfInterval.IntPairWithInfty ],
    in_types=[ BoolSort(), IntSort(), BoolSort(), IntSort(), BoolSort(), IntSort(), BoolSort(), IntSort() ], # is_inf_low, low, is_inf_high, high for x and y
    ops={ op: None for op in InfInterval.ops },
    const_map={ InfInterval.mkIntPairWithInfty(BoolVal(False), IntVal(i), BoolVal(False), IntVal(i)): None for i in range(0, 3) } #\
        #| { InfInterval.mkIntPairWithInfty(BoolVal(True), IntVal(0), BoolVal(False), IntVal(0)): None, InfInterval.mkIntPairWithInfty(BoolVal(False), IntVal(0), BoolVal(True), IntVal(0)): None }\
        #| { InfInterval.mkIntPairWithInfty(BoolVal(True), IntVal(0), BoolVal(True), IntVal(0)): None }
    #max_const=1
)

print(abs_func)

def abstract_contains_concrete(abstract_expr, concrete_expr):
    low = InfInterval.get_val_low(abstract_expr)
    high = InfInterval.get_val_high(abstract_expr)
    is_inf_low = InfInterval.is_inf_low(abstract_expr)
    is_inf_high = InfInterval.is_inf_high(abstract_expr)
    return And(
        Or(is_inf_low, concrete_expr >= low),
        Or(is_inf_high, concrete_expr <= high)
    )

abs_x, abs_y, abs_z = Consts('abs_x abs_y abs_z', InfInterval.IntPairWithInfty)

correct_abs = Implies(
    And(abstract_contains_concrete(abs_x, x), abstract_contains_concrete(abs_y, y), correct),
    abstract_contains_concrete(abs_z, z)
)

abs_constraint = Constraint(
    phi=correct_abs,
    params=[abs_x, abs_y, x, y, z],
    function_applications={
        ('sum', (InfInterval.is_inf_low(abs_x), InfInterval.get_val_low(abs_x), InfInterval.is_inf_high(abs_x), InfInterval.get_val_high(abs_x), InfInterval.is_inf_low(abs_y), InfInterval.get_val_low(abs_y), InfInterval.is_inf_high(abs_y), InfInterval.get_val_high(abs_y))): (abs_z,)
    }
)


abs_problem = Problem(constraints=[abs_constraint], funcs={ 'sum': abs_func })
print(abs_problem)


# Synthesize a program and print it if it exists
prgs, stats = LenCegis(debug=Debug(what="len|cex|prg|success"), keep_samples=False, size_range=(5, 6), opt_cse=False).synth_prgs(abs_problem)
if prgs:
    print(prgs['sum'].to_string(sep='\n'))
else:
    print('No program found')
    print(stats)
