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
    
    def smaller(self, a, b):
        a_low = InfInterval.get_val_low(a)
        a_high = InfInterval.get_val_high(a)
        a_inf_low = InfInterval.is_inf_low(a)
        a_inf_high = InfInterval.is_inf_high(a)

        b_low = InfInterval.get_val_low(b)
        b_high = InfInterval.get_val_high(b)
        b_inf_low = InfInterval.is_inf_low(b)
        b_inf_high = InfInterval.is_inf_high(b)

        # returns true iff interval a is a true subset of interval b
        return And(
            Or(a_inf_low, b_inf_low, a_low > b_low),
            Or(a_inf_high, b_inf_high, a_high < b_high),
            Not(And(a_inf_low == b_inf_low, a_inf_high == b_inf_high, a_low == b_low, a_high == b_high))
        )
    
    def smaller_equals(self, a, b):
        a_low = InfInterval.get_val_low(a)
        a_high = InfInterval.get_val_high(a)
        a_inf_low = InfInterval.is_inf_low(a)
        a_inf_high = InfInterval.is_inf_high(a)

        b_low = InfInterval.get_val_low(b)
        b_high = InfInterval.get_val_high(b)
        b_inf_low = InfInterval.is_inf_low(b)
        b_inf_high = InfInterval.is_inf_high(b)

        # returns true iff interval a is a subset of interval b
        return And(
            Or(a_inf_low, b_inf_low, a_low >= b_low),
            Or(a_inf_high, b_inf_high, a_high <= b_high)
        )

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

def abstract_and_refine(concrete_constraint, inputs, outputs, abstraction, ops, const_map, name, prev_prg):
    input_types, output_types, (ins, outs), params, abstract_correct = Abstract(concrete_constraint, inputs, outputs, abstraction)

    func = synth_func_from_ops(
        out_types=output_types,
        in_types=input_types,
        ops=ops,
        const_map=const_map
    )

    # at least the same as the old prg on the abstract level
    at_least_equal_outs = [ abstraction.abstract_variable(f'abs_{name}_out_{i}') for i in range(len(outputs)) ]
    at_least_correct = And(
        And(*prev_prg.eval_clauses(ins, at_least_equal_outs)), 
        And(*[ abstraction.smaller_equals(new_out, old_out) for new_out, old_out in zip(outs, at_least_equal_outs) ])
    )

    # refining input

    refined_ins = [ abstraction.abstract_variable(f'refined_abs_{name}_in_{i}') for i in range(len(inputs)) ]
    refined_ins_exprs = []
    for refined_in in refined_ins:
        inp_exprs, _ = abstraction.input_to_input_expressions(refined_in)
        refined_ins_exprs.extend(inp_exprs)
    refined_outs = [ abstraction.abstract_variable(f'refined_abs_{name}_out_{i}') for i in range(len(outputs)) ]

    # only allow a constant output
    refine_func = synth_func_from_ops(
        out_types=input_types,
        in_types=[],
        ops=[],
        const_map=None
    )

    # old prg executed with refined inputs and outputs 
    refined_old_outs = [ abstraction.abstract_variable(f'abs_{name}_out_old_{i}') for i in range(len(outputs)) ]
    refine_fun_correct = And(
        *[
            And(*prev_prg.eval_clauses(refined_ins_exprs, refined_old_outs)),
            Or(*[ abstraction.smaller(old_out, new_out) for old_out, new_out in zip(refined_old_outs, refined_outs) ])
        ]
        
    )


    constraint = Constraint(
        phi=And(abstract_correct, at_least_correct, refine_fun_correct),
        params=params,
        function_applications={
            (name, ins): outs,
            (name, tuple(refined_ins)): tuple(refined_outs),
            (f'refine_{name}', tuple()): tuple(refined_outs)
        }
    )

    problem = Problem(constraints=[constraint], funcs={ name: func, f'refine_{name}': refine_func })
    return problem





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


def test_interval_abstraction_refine():
    x, z = Ints('x z')
    correct = z == -x
    inputs = [x]
    outputs = [z]
    abstraction = IntervalAbstraction()

    # first find an abstract program
    problem = abstract_problem(correct, inputs, outputs, abstraction, { op: None for op in InfInterval.ops }, { InfInterval.mkIntPairWithInfty(BoolVal(False), IntVal(i), BoolVal(False), IntVal(i)): None for i in range(0, 3) } | { InfInterval.mkIntPairWithInfty(BoolVal(True), IntVal(0), BoolVal(True), IntVal(0)): None }, 'neg')

    prgs, stats = LenCegis(debug=Debug(what="len|cex|prg|success"), keep_samples=False, opt_cse=False, size_range=(1,6)).synth_prgs(problem)
    if prgs:
        print(prgs['neg'].to_string(sep='\n'))

        old_prg = prgs['neg']
        while True:
            refine_problem = abstract_and_refine(correct, inputs, outputs, abstraction, { op: None for op in InfInterval.ops }, { InfInterval.mkIntPairWithInfty(BoolVal(False), IntVal(i), BoolVal(False), IntVal(i)): None for i in range(0, 3) } | { InfInterval.mkIntPairWithInfty(BoolVal(True), IntVal(0), BoolVal(True), IntVal(0)): None }, 'neg', old_prg)
            prgs, stats = LenCegis(debug=Debug(what="len|cex|prg|success"), keep_samples=False, opt_cse=False, size_range=(1,6)).synth_prgs(refine_problem)
            if prgs:
                print(prgs['neg'].to_string(sep='\n'))
                old_prg = prgs['neg']
            else:
                print('No more refined program found')
                break

    else:        
        print('No program found')

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
    test_interval_abstraction_refine()




