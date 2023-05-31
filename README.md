# Synthesis of Loop-free Programs

This is a synthesis algorithm that combines a [counterexample-guided synthesis algorithm](https://susmitjha.github.io/papers/pldi11.pdf) with the program-length based approach found in recent work on [SAT-based exact synthesis](https://infoscience.epfl.ch/record/271569/files/WH-IEEE-SAT-Based.pdf) for circuits.
It is implemented using the [Z3](https://github.com/Z3Prover/z3) SMT solver.

This algorithm synthesizes loop-free programs from a library of operators given the specification of the program.
The specification is given by a list of SMT formulas, one for each output of the program.
An operator is a function with $n$ inputs and one output whose semantics is specified by an SMT formula.
The algorithm will find the shortest *provably correct* program composed of the operators in the library if such a program exists or will report failure if no such program exists.

The algorithm is generic with respect to the SMT theories used by operators and functions to synthesize.
In contrast to Gulwani et al.s work, this algorithm does not require a specify a specific number of instances of each operator but can instantiate each operator as often as it sees fit.

For example, if you provide an operator library that only consists of a NAND operation with the specification $o=\neg (i_1\land i_2)$, and ask for synthesizing a program that fulfils the specification $o=i_1\land i_2$, the algorithm will synthesize the program
```
v2 = nand(v0, v1)
v3 = nand(v2, v2)
return(v3)
```
where `v0` and `v1` are the input variables.

## Prerequisites

You need Z3 and the [z3-solver](https://pypi.org/project/z3-solver/) package for Python installed.

## How to Use

The package provides the function
```Python
def synth(funcs: list[Op], ops: list[Op], to_len, from_len = 0, input_names=[], debug=False):
```
which does the actual synthesis.

- The first argument `funcs` is the list of functions to synthesize.
- `ops` is the library of operators it can use.
- `to_len` specifies the maximum length of the program.
- `from_len` is optional and can be set to specify a minimum program length
- `input_names` is optional and can be used to give names to the inputs of the program.
- `debug` is an `int` specifying the debug output level.

The function returns a pair of the synthesized program (or `None`) and statistics information about the synthesis process.

The following example shows how to produce the program mentioned above:
```Python
from synth import synth
# Just a helper for a list of two boolean parameters
Bool2 = [ Bool, Bool ]

# A template has z
# - name
# - return type
# - list of parameter types
# - Z3 formula that describes its semantics
nand2 = Op('nand2', Bool2, Bool, lambda ins: Not(And(ins)))

# The specification for the program to synthesize
# is also given by a template.
spec  = Template('and', Bool2, Bool, And)

# Synthesize the program and print it if it exists
prg, stats = synth([ spec ], [ nand2 ], 10)
if prg:
    print(prg)