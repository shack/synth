# Synthesis of Loop-free Programs

This is an implementation of the counterexample-guided synthesis algorithm
of [Gulwani et al.](https://susmitjha.github.io/papers/pldi11.pdf) using the [Z3](https://github.com/Z3Prover/z3) SMT solver. 

This algorithm synthesizes loop-free programs from a library of templates, given the specification of the program as an SMT formula.
A template is an operation with $n$ inputs and one output whose semantics is specified by an SMT formula.
The algorithm will find a *provably correct* program composed of the templates in the library if such a program exists or will report failure if no such program exists. 

For example, if you provide a library that consists of two NAND operations, each with the specification $o=\neg (i_1\land i_2)$, and ask for synthesizing a program that fulfils the specification $o=i_1\land i_2$, the algorithm will synthesize the program
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
synth(lib, specs)
```
which will do the actual synthesis.
The first argument is the library of templates and the second is a list of specifications for the outputs of the program.
The algorithm supports programs with a list of output variables.
Each output variable has a specification in the list.

The following example shows how to produce the program mentioned above:
```Python
# Just a helper for a list of two boolean parameters
Bool2 = [ Bool, Bool ]

# A template has z
# - name
# - return type
# - list of parameter types
# - Z3 formula that describes its semantics
nand2 = Template('nand2', Bool, Bool2, lambda ins: Not(And(ins)))

# The specification for the program to synthesize 
# is also given by a template.
spec  = Template('and', Bool, Bool2, And)

# Create a library with two NANDs.
lib = create_lib([
    (nand2, 2),
])

# Synthesize the program and print it if it exists
if prg := synth(lib, [ spec ]):
    print(prg.str_multiline())