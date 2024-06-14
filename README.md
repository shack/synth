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
def synth(spec: Spec, ops: list[Func], iter_range, n_samples=1, **args):
```
which does the actual synthesis.

- The first argument `spec` is the specification of the program to synthesize.
- `ops` is the library of operators it can use.
- `range` is the range of program sizes to try.
- `n_samples` number of initial I/O samples to draw.
- `args` are additional options given to the core synthesis routine `synth_n` (see code).

The function returns a pair of the synthesized program (or `None`) and statistics information about the synthesis process.

The following example shows how to synthesize a 1-bit full adder:
```Python
from cegis import Func, Spec
from synth_n import synth
from z3 import *

r, x, y := Bools('r x y')

# An operator consists of a name, a formula specifying its semantics,
# and the list of input operands
nand2 = Func('nand2', Not(And([x, y])), [x, y])

# The specification for the program to synthesize is an object of class Spec
# A Spec is given by a name, a list of input/output relations,
# and two lists that give that specify the output and input variables.
spec  = Spec('and', r == And([x, y]), [r], [x, y])

# Synthesize a program of at most 9 instructions and print it if it exists
prg, stats = synth(spec, [ nand2 ], range(10))
if prg:
    print(prg)
else:
   print('No program of length 10 found')
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
  where `r` does not appear in `ins` and `ins` are the free variables in `phi`.

## Synthesis of Boolean Functions

`boolfunc` synthesizes boolean functions. It has three modes of operation:
1. Pass function values as hex numbers via the command line:
   ```
   ./boolfunc.py 0b00010010 1234 0xabcd1234
   ```
   synthesizes 3-input function 0x12, 4-input function 0x1234, and 5-input function 0xabcd1234
2. Read in function values from a file
   ```
   ./boolfunc.py -f funcs.txt
   ```
   where `funcs.txt` contains function values of each function per line, i.e.
   ```
   0b00010010
   1234
   0xabcd1234
   ```
3. Read in an [Espresso](https://raw.githubusercontent.com/JackHack96/logic-synthesis/espresso/doc/espresso5.pdf) PLA description of the form
   ```
   .i 3
   .o 2
   000 00
   001 01
   010 01
   011 10
   100 01
   101 10
   110 10
   111 11
   .e
   ```
   Don't care entries (`-`) in input and output are supported (see `pla/dontcare.pla`).
   Use with parameter `-a`, for example: `./synth_bf.py -a pla/add.pla`

See `./boolfunc.py -h` for more options.

## Hacker's Delight Benchmarks

`hackdel.py` provides benchmarks 1-24 from the [Brahma paper](https://susmitjha.github.io/papers/pldi11.pdf).