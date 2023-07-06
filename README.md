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
def synth(spec: Spec, ops: list[Func], to_len, from_len=0, input_names=[], debug=False):
```
which does the actual synthesis.

- The first argument `spec` is the specification of the program to synthesize.
- `ops` is the library of operators it can use.
- `to_len` specifies the maximum length of the program.
- `from_len` is optional and can be set to specify a minimum program length
- `debug` is an `int` specifying the debug output level.

The function returns a pair of the synthesized program (or `None`) and statistics information about the synthesis process.

The following example shows how to produce the program mentioned above:
```Python
from synth import synth

r, x, y := Bools('r x y')

# An operator consists of a name and a formula specifying its semantics
nand2 = Func('nand2', Not(And([x, y])), [x, y])

# The specification for the program to synthesize is an object of class Spec
# A Spec is given by a name, a formula of type boolean that relates inputs to outputs
# and two lists that give that specify the output and input variables.
spec  = Spec('and', r == And([x, y]), [r], [x, y])

# Synthesize a program of at most 10 instructions and print it if it exists
prg, stats = synth(spec, [ nand2 ], 10)
if prg:
    print(prg)
```

### Notes

- It might seem strange that we use variables `x` and `y` in the specification
  of the function to synthesize and of an operator. However, the concrete
  variable names in the specification and operator formulas don't matter
  because the formulas are instantiated in the synthesizer and the variables
  are substituted with ones that the synthesizer picks.
- A `Func` is just a special `Spec` for functional relations with one output variable.
  ```
  Func(name, phi, ins)
  ```
  is shorthand for
  ```
  Spec(name, r == phi, [ r ], ins)
  ```
  where `r` does not appear in `ins`

## Espresso PLA Synthesis

`synth_pla` reads in an [Espresso](https://ptolemy.berkeley.edu/projects/embedded/pubs/downloads/espresso/index.htm) PLA description of the form
```
.i 3
.o 1
100 1
110 1
001 1
011 1
.e
```
and synthesizes the shortest program that implements that truth table using the operators and, or, xor, not, and3, or3.

For an example, type
```
./synth_pla.py pla/mux.in
```