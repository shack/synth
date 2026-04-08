from synth.oplib import Bv, Interval, I, InfInterval
from synth.spec import Constraint, Problem, Production, Nonterminal, SynthFunc, Func, synth_func_from_ops
from synth.synth_n import LenCegis
from synth.util import Debug
from z3 import *


class IntervalAbstraction:
    def __init__(self):
        pass

    def abstract_contains_concrete(self, abstract_expr, concrete_expr):
        low = InfInterval.get_val_low(abstract_expr)
        high = InfInterval.get_val_high(abstract_expr)
        is_inf_low = InfInterval.is_inf_low(abstract_expr)
        is_inf_high = InfInterval.is_inf_high(abstract_expr)
        return And(
            Or(is_inf_low, concrete_expr >= low),
            Or(is_inf_high, concrete_expr <= high)
        )
    
    def abstract_variable(self, name):
        return Const(name, InfInterval.IntPairWithInfty)
    
    def input_to_input_expressions(self, abs_input):
        return [ InfInterval.is_inf_low(abs_input), InfInterval.get_val_low(abs_input), InfInterval.get_val_high(abs_input), InfInterval.is_inf_high(abs_input) ], [ BoolSort(), IntSort(), IntSort(), BoolSort() ]
    
    def output_to_output_expressions(self, abs_output):
        return [ abs_output ], [ InfInterval.IntPairWithInfty ]

class BvAbstraction:
    def __init__(self, width):
        self.width = width

    def abstract_contains_concrete(self, abstract_expr, concrete_expr):
        return abstract_expr == Extract(self.width - 1, 0, concrete_expr)
    
    def abstract_variable(self, name):
        return BitVec(name, self.width)
    
    def input_to_input_expressions(self, abs_input):
        return [ abs_input ], [ BitVecSort(self.width) ]
    
    def output_to_output_expressions(self, abs_output):
        return [ abs_output ], [ BitVecSort(self.width) ]

# Use this to build Constraint and Spec
def Abstract(concrete_constraint, inputs, outputs, abstraction):
    abs_inputs = [ abstraction.abstract_variable(f'abs_{inp}') for inp in inputs ]
    abs_outputs = [ abstraction.abstract_variable(f'abs_{outp}') for outp in outputs ]

    abstract_correct = Implies(
        And(*[ abstraction.abstract_contains_concrete(abs_inp, inp) for abs_inp, inp in zip(abs_inputs, inputs) ], concrete_constraint),
        And(*[ abstraction.abstract_contains_concrete(abs_outp, outp) for abs_outp, outp in zip(abs_outputs, outputs) ])
    )

    input_exprs = []
    input_types = []
    for abs_inp in abs_inputs:
        inp_exprs, inp_types = abstraction.input_to_input_expressions(abs_inp)
        assert len(inp_exprs) == len(inp_types)
        input_exprs.extend(inp_exprs)
        input_types.extend(inp_types)
    
    output_exprs = []
    output_types = []
    for abs_outp in abs_outputs:
        outp_exprs, outp_types = abstraction.output_to_output_expressions(abs_outp)
        assert len(outp_exprs) == len(outp_types)
        output_exprs.extend(outp_exprs)
        output_types.extend(outp_types)
    
    func_appl = (tuple(input_exprs), tuple(output_exprs))

    params = inputs + outputs + abs_inputs

    return input_types, output_types, func_appl, params, abstract_correct


def abstract_problem(concrete_constraint, inputs, outputs, abstraction, ops, const_map, name):
    input_types, output_types, (ins, outs), params, abstract_correct = Abstract(concrete_constraint, inputs, outputs, abstraction)

    func = synth_func_from_ops(
        out_types=output_types,
        in_types=input_types,
        ops=ops,
        const_map=const_map
    )

    constraint = Constraint(
        phi=abstract_correct,
        params=params,
        function_applications={
            (name, ins): outs
        }
    )

    problem = Problem(constraints=[constraint], funcs={ name: func })
    return problem




def test_interval_abstraction():
    x, y, z = Ints('x y z')
    concrete_constraint = z == x + y
    inputs = [x, y]
    outputs = [z]
    abstraction = IntervalAbstraction()

    problem = abstract_problem(concrete_constraint, inputs, outputs, abstraction, { op: None for op in InfInterval.ops }, { InfInterval.mkIntPairWithInfty(BoolVal(False), IntVal(i), BoolVal(False), IntVal(i)): None for i in range(0, 3) }, 'sum')
    print(problem)

    # Synthesize a program and print it if it exists
    prgs, stats = LenCegis(debug=Debug(what="len|cex|prg|success"), keep_samples=False, opt_cse=False, size_range=(5,6)).synth_prgs(problem)
    if prgs:
        print(prgs['neg'].to_string(sep='\n'))
    else:
        print('No program found')
        print(stats)


def test_bv_abstraction():
    original_width   = 1024
    # define two bit vector variables for the argument and result of the function
    r, x    = BitVecs('r x', original_width)

    concrete_constraint = r == (x & (x-1))
    inputs = [x]
    outputs = [r]

    scaled_down_width = 8
    abstraction = BvAbstraction(scaled_down_width)

    problem = abstract_problem(concrete_constraint, inputs, outputs, abstraction, { op: None for op in Bv(scaled_down_width).simple_ops }, {}, 'neg')
    print(problem)

    # Synthesize a program and print it if it exists
    prgs, stats = LenCegis(debug=Debug(what="len|cex|prg|success"), keep_samples=False, opt_cse=False).synth_prgs(problem)
    if prgs:
        print(prgs['neg'].to_string(sep='\n'))
    else:
        print('No program found')
        print(stats)

if __name__ == "__main__":
    test_interval_abstraction()
    test_bv_abstraction()




