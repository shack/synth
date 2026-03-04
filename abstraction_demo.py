
from synth.spec import Constraint, Problem, Production, Nonterminal, SynthFunc, Func, synth_func_from_ops
from synth.synth_n import LenCegis
from synth.oplib import Bv, Interval
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

    def get_non_terminals(self, func: SynthFunc) -> dict[str, Nonterminal]:
        # returns the operators of the function in the abstract domain
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


class EquivalentOperatorsAbstraction(Abstraction):
    def concrete_abstract_operators(self) -> list[tuple[Func, Func]]:
        # returns a list of pairs between concrete operators and abstract operators
        # left pair element is concrete operator, right element is abstract operator
        pass
    
    def get_non_terminals(self, func: SynthFunc) -> dict[str, Nonterminal]:
        # abstract func definitions
        operator_mapping = self.concrete_abstract_operators()
        # helper mapping to find abstract operator by concrete operator name
        concrete_to_abstract_op = { conc_op.name: abs_op for conc_op, abs_op in operator_mapping }
        # replace operators in nts
        abstract_nts = {}
        for name, nt in func.nonterminals.items():
            prods_litst = []
            for prod in nt.productions:
                if prod.op.name in concrete_to_abstract_op:
                    # print(f"Mapping concrete operator {prod.op.name} to abstract operator {concrete_to_abstract_op[prod.op.name].name} in production {prod}")
                    prods_litst.append(Production(
                        op=concrete_to_abstract_op[prod.op.name],
                        operands=prod.operands,
                        operand_is_nt=prod.operand_is_nt,
                        sexpr=prod.sexpr,
                        attributes=prod.attributes
                    ))
                else:
                    print(f"Warn: No mapping for concrete operator {prod.op.name} in production {prod}, keeping it unchanged")
                    prods_litst.append(prod)

            prods = tuple(prods_litst)
            
            abstract_nts[name] = Nonterminal(
                name=name,
                sort=self.get_abstract_sort(nt.sort),
                constants=None, # TODO: handle properly 
                parameters=nt.parameters,
                productions=prods,
            )
        
        return abstract_nts



class BvDownscalingAbstraction(EquivalentOperatorsAbstraction):
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

class IntervalAbstraction(Abstraction):
    def __init__(self):
        super().__init__()
    
    def concrete_to_abstract(self, expr):
        # make an interval representing only the one value
        return Interval.mkIntPair(expr, expr)
    
    def abstract_contains_concrete(self, abstract_expr, concrete_expr):
        low = Interval.low(abstract_expr)
        high = Interval.high(abstract_expr)
        return And(concrete_expr >= low, concrete_expr <= high)
    
    def get_func_ops(self, func: SynthFunc) -> dict[str, Nonterminal]:
        return { op: None for op in Interval.ops }

    def get_abstract_sort(self, concrete_sort):
        if concrete_sort.is_int():
            print("Returning interval sort")
            return Interval.IntPair
        else:
            return concrete_sort
    
    def abstract_constant_mapping(self, const_map):
        return {}


class FpFromRealAbstraction(Abstraction):
    def __init__(self, epsilon: float):
        self.epsilon = epsilon
        super().__init__()
    



# Problem definition with abstraction
# TODO: maybe pass theory / logic to use for the abstract problem?
def AbstractedProblem(base_problem: Problem, abstraction: Abstraction) -> Problem:

    print("Building abstracted problem...")

    abstract_funcs = {}
    for func_name, func in base_problem.funcs.items():
        print(f"Abstracting function {func_name}...")
        
        abstract_in_types = [ (n, abstraction.get_abstract_sort(sort)) for n, sort in func.inputs ]
        abstract_out_types = [ (n, abstraction.get_abstract_sort(sort)) for n, sort in func.outputs ]
        
        abstract_nts = abstraction.get_non_terminals(func)
        
        abstract_funcs[func_name] = SynthFunc(
            inputs=abstract_in_types,
            outputs=abstract_out_types,
            max_const=abstraction.abstract_max_constant_count(func.max_const),
            result_nonterminals=func.result_nonterminals, # assume the grammar itself does not need a change
            weights=func.weights, # assume the abstraction does not change the weights
            nonterminals=abstract_nts
        )
    
    # abstract constraints
    abstract_constraints = []
    for constraint in base_problem.constraints:
        # params stay the same, as we ensure the program is correct under the concrete inputs
        abstract_params = constraint.params
        # for each function application, extend phi to ensure correctness under abstraction
        # and set the abstract function applications
        abstract_function_applications = {}
        abstract_phi = constraint.phi

        # all previous output vars would now be free variables -> must be quantified
        concrete_output_vars = []

        for (func_name, input_exprs), output_vars in constraint.function_applications.items():
            print(f"Abstracting function application of {func_name} with outputs {output_vars} and inputs {input_exprs}...")

            # create variables containing abstracted output
            abstract_output_vars = [ Const('abs_' + str(var), abstraction.get_abstract_sort(var.sort())) for var in output_vars ]
            abstract_input_exprs = [ abstraction.concrete_to_abstract(expr) for expr in input_exprs ]
            
            abstract_function_applications[(func_name, tuple(abstract_input_exprs))] = tuple(abstract_output_vars)
            
            concrete_output_vars.extend(output_vars)
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
            phi=Exists(concrete_output_vars, abstract_phi),
            params=abstract_params,
            function_applications=abstract_function_applications
        )
        abstract_constraints.append(abstract_constraint)

    return Problem(
        constraints=abstract_constraints,
        funcs=abstract_funcs,
        name= base_problem.name + "_abstracted" if base_problem.name is not None else None,
        # TODO: theory
    )



class BvUpscalingSample:
    def run(self):
        width   = 1024
        # define two bit vector variables for the argument and result of the function
        r, x    = BitVecs('r x', width)

        # an expression that is true if and only if x is a power of 2 or x is 0
        sum = r == x & (x-1)

        constraint = Constraint(
            phi=sum,
            params=[x],
            function_applications={
                # (name, ins): (outs)
                ('sum', (x,)): (r,)
            }
        )

        func = synth_func_from_ops(
            out_types=[ r.sort() ],
            in_types=[ x.sort() ],
            ops={ op: None for op in [Bv(width).and_, Bv(width).sub_] },
            const_map={ BitVecVal(i, width): None for i in range(1, 2) }
        )

        # The synthesis problem consists of the constraint and the functions to synthesise.
        problem = Problem(constraints=[constraint], funcs={ 'sum': func })
        print(problem)
        print()
        abstracted_problem = AbstractedProblem(problem, BvDownscalingAbstraction(from_size=width, to_size=8))
        print(abstracted_problem)

        # Synthesize a program and print it if it exists
        prgs, stats = LenCegis(debug=Debug(what="len|cex|prg")).synth_prgs(abstracted_problem)
        if prgs:
            print(prgs['sum'].to_string(sep='\n'))
        else:
            print('No program found')


class FpFromRealSample:
    def run(self):
        r, x = Reals('r x') # output, input variables of the real definition
        correct = r == Sqrt(x + 1) - Sqrt(x)

        constraint = Constraint(
            phi=correct,
            params=[x],
            function_applications={
                'sqrt_fp': [ ([r], [x]) ]
            }
        )

        func = synth_func_from_ops(
            outputs=[ (str(r), r.sort()) ],
            inputs=[ (str(x), x.sort()) ],
            ops={ op: None for op in R.ops },
            const_map={ RealVal(i): None for i in range(0, 3) }
        )


class IntervalAnalysisSample:
    def run(self):
        x, y, z = Ints('x y z')
        correct = z == x + y

        constraint = Constraint(
            phi=correct,
            params=[x],
            function_applications={
                'sum': [ ([z], [x]) ]
            }
        )

        func = synth_func_from_ops(
            out_types=[ z.sort() ],
            in_types=[ x.sort() ],
            ops={ op: None for op in Interval.ops },
            const_map={ IntVal(i): None for i in range(0, 3) }
        )

        # The synthesis problem consists of the constraint and the functions to synthesise.
        problem = Problem(constraints=[constraint], funcs={ 'sum': func })
        print(problem)
        print()
        abstracted_problem = AbstractedProblem(problem, IntervalAbstraction())
        print(abstracted_problem)
        # Synthesize a program and print it if it exists
        prgs, stats = LenCegis(debug=Debug(what="len|cex|prg")).synth_prgs(abstracted_problem)
        if prgs:
            print(prgs['sum'].to_string(sep='\n'))
        else:
            print('No program found')

if __name__ == "__main__":
    BvUpscalingSample().run()
