
from synth.spec import Constraint, Problem, SynthFunc, Func
from synth.synth_n import LenCegis
from synth.oplib import Bv
from sygus import logics
from synth.util import Debug
from z3 import *



class Abstraction:
    def __init__(self):
        pass
    
    # Abstraction function
    def concrete_to_abstract(self, expr):
        # returns a z3 expression in the abstract domain, that approximates the concrete expr
        pass

    # Concretization function
    def abstract_contains_concrete(self, abstract_expr, concrete_expr):
        # returns a z3 boolean expression that is true if is concrete_expr is a value represented by abstract_expr

        # TODO: could one just check whether concrete_to_abstract(concrete_expr) == abstract_expr?
        pass

    def concrete_abstract_operators(self) -> list[tuple[Func, Func]]:
        # returns a list of pairs between concrete operators and abstract operators
        # left pair element is concrete operator, right element is abstract operator
        pass

    def get_abstract_sort(self, concrete_sort):
        # returns the abstract sort corresponding to the concrete sort
        # could return the same sort if the abstraction does not touch a certain sort
        pass
    
    def abstract_constant_mapping(self, const_map: dict[ExprRef, int | None] | None = None) -> dict[ExprRef, int | None] | None:
        # given a mapping of concrete constants, returns the mapping of abstract constants that should be used
        # generally ignore constant limits for abstractions
        return None

    def abstract_max_constant_count(self, concrete_max_const: int | None) -> int | None:
        # given a maximum constant count for the concrete problem, returns the maximum constant count for the abstract problem
        # generally keep the same limit for abstractions
        return concrete_max_const


class BvDownscalingAbstraction(Abstraction):
    def __init__(self, from_size: int, to_size: int):
        assert from_size > to_size
        self.from_size = from_size
        self.to_size = to_size
        super().__init__()

    def concrete_to_abstract(self, expr):
        return Extract(self.to_size - 1, 0, expr)

    def abstract_contains_concrete(self, abstract_expr, concrete_expr):
        extracted = Extract(self.to_size - 1, 0, concrete_expr)
        return extracted == abstract_expr

    def concrete_abstract_operators(self) -> list[tuple[Func, Func]]:
        from_ops = Bv(self.from_size)
        to_ops = Bv(self.to_size)

        return list(zip(from_ops.ops, to_ops.ops))
    
    def get_abstract_sort(self, concrete_sort):
        if is_bv_sort(concrete_sort) and concrete_sort.size() == self.from_size:
            return BitVecSort(self.to_size)
        else:
            return concrete_sort





# Problem definition with abstraction
# TODO: maybe pass theory / logic to use for the abstract problem?
def AbstractedProblem(base_problem: Problem, abstraction: Abstraction) -> Problem:

    # abstract func definitions
    operator_mapping = abstraction.concrete_abstract_operators()
    # helper mapping to find abstract operator by concrete operator name
    concrete_to_abstract_op = { conc_op.name: abs_op for conc_op, abs_op in operator_mapping }

    abstract_funcs = {}
    for func_name, func in base_problem.funcs.items():
        abstract_inputs = [ (name, abstraction.get_abstract_sort(sort)) for name, sort in func.inputs ]
        abstract_outputs = [ (name, abstraction.get_abstract_sort(sort)) for name, sort in func.outputs ]
        abstract_funcs[func_name] = SynthFunc(
            outputs=abstract_outputs,
            inputs=abstract_inputs,
            ops={ concrete_to_abstract_op[op.name]: count for op, count in func.ops.items() },
            max_const=abstraction.abstract_max_constant_count(func.max_const),
            const_map=abstraction.abstract_constant_mapping(func.const_map)
        )
    
    # abstract constraint 
    # params stay the same, as we ensure the program is correct under the concrete inputs
    abstract_params = base_problem.constraint.params
    # for each function application, extend phi to ensure correctness under abstraction
    # and set the abstract function applications
    abstract_function_applications = {}
    abstract_phi = base_problem.constraint.phi

    for func_name, applications in base_problem.constraint.function_applications.items():
        for output_vars, input_exprs in applications:
            # create variables containing abstracted output
            abstract_output_vars = [ Const('abs_' + str(var), abstraction.get_abstract_sort(var.sort())) for var in output_vars ]
            abstract_input_exprs = [ abstraction.concrete_to_abstract(expr) for expr in input_exprs ]
            
            abstract_function_applications.setdefault(func_name, []).append( (abstract_output_vars, abstract_input_exprs) )
            
            # add constraints to relate abstract output to concrete output
            for abs_var, conc_var in zip(abstract_output_vars, output_vars):
                abstract_phi = And(
                    abstract_phi,
                    abstraction.abstract_contains_concrete(
                        abs_var,
                        conc_var
                    )
                )
    
    abstract_constraint = Constraint(
        phi=abstract_phi,
        params=abstract_params,
        function_applications=abstract_function_applications
    )

    return Problem(
        constraint=abstract_constraint,
        funcs=abstract_funcs,
        name= base_problem.name + "_abstracted" if base_problem.name is not None else None,
        # TODO: theory
    )



width   = 16
# define two bit vector variables for the argument and result of the function
r, x    = BitVecs('r x', width)

# an expression that is true if and only if x is a power of 2 or x is 0
sum = r == x & (x-1)

constraint = Constraint(
    phi=sum,
    params=[x],
    function_applications={
        'sum': [ ([r], [x]) ]
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
    ops={ op: None for op in Bv(width).ops },
    const_map={ BitVecVal(i, width): None for i in range(1, 2) }
)

# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraint=constraint, funcs={ 'sum': func })
print(problem)
print()
abstracted_problem = AbstractedProblem(problem, BvDownscalingAbstraction(from_size=16, to_size=8))
print(abstracted_problem)

# Synthesize a program and print it if it exists
prgs, stats = LenCegis(debug=Debug(what="len|cex")).synth_prgs(abstracted_problem)
if prgs:
    print(prgs['sum'].to_string(sep='\n'))
else:
   print('No program found')

