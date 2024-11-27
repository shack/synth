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

You need the following packages:

[z3-solver](https://pypi.org/project/z3-solver/),
[tyro](https://pypi.org/project/tyro/),
[tinysexpr](https://github.com/shack/tinysexpr)

## How to Use

The package provides different synthesis algorithms in its `synth` subdirectory.
Each synthesis algorithm comes with a class that holds parameters to the synthesis and has a function
```Python
def synth(self, task: Task)
```
where `Task` is a class that holds the specification and a library of operators to synthesize from; among other things.
`synth` returns a pair of the synthesized program (or `None`) and statistics information about the synthesis process.

The following example shows how to synthesize the NAND example above.
```Python
from synth.spec import Func, Spec, Task
from synth.synth_n import LenCegis
from z3 import *

r, x, y = Bools('r x y')

# An operator consists of a name and a formula specifying
# function from the inputs to the output that specifies its semantics.
# The input variables are all free variables in that formula.
nand2 = Func('nand2', Not(And([x, y])))

# The specification for the program to synthesize is an object of class Spec
# A Spec is given by a name, a list of input/output relations,
# and two lists that give that specify the output and input variables.
spec  = Spec('and', r == And([x, y]), [r], [x, y])

# Create a synthesis task
# Here, the library only consists of a nand2 which has no upper bound
# on how often it is allowed to be used in the program (indicated by None).
task = Task(spec, { nand2: None })

# Synthesize a program and print it if it exists
prg, stats = LenCegis().synth(task)
if prg is not None:
    print(prg)
else:
   print('No program found')
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
1. Pass function values as numbers via the command line:
   ```
   python boolfunc.py op:func --op.func 0b00010010
   python boolfunc.py op:func --op.func 1234
   python boolfunc.py op:func --op.func 0xabcd1234
   ```
   synthesizes 3-input function 0x12, 4-input function 0x1234, and 5-input function 0xabcd1234
2. Read in function values from a file
   ```
   python boolfunc.py op:file --op.file funcs.txt
   ```
   where `funcs.txt` contains function values of each function per line, i.e.
   ```
   0b00010010
   1234
   0xabcd1234
   ```
3. Read in an [Espresso](https://raw.githubusercontent.com/JackHack96/logic-synthesis/espresso/doc/espresso5.pdf) PLA description of the form
   ```
   .i 4
   .o 2
   # names of inputs from left to right (optional)
   .ilb running enabled hlt reset intr
   # names of outputs from left to right (optional)
   .ob new_running new_enabled
   # dashes indicate don't cares
   0-000 00
   1-000 11
   ---01 11
   ---1- 10
   --100 00
   .e
   ```
   Don't care entries (`-`) in input and output are supported (see `pla/dontcare.pla`).
   ```
   python boolfunc.py op:pla --op.file filename.pla
   ```

You can specify the library of operators (with an optional maximum count) and a maximum count of constants (True, False) like this:
```
python boolfunc.py --ops nand2:2,nor2,and2:4 --consts 3 ...
```
which would look for solutions with at most 3 constants, 2 2-operand nands, 4 2-operand ands, and an arbitrary amount of 2-operand nors.

See `python boolfunc.py --help` for more options.

## Hacker's Delight Benchmarks

`bench/hackdel.py` provides benchmarks 1-24 from the [Brahma paper](https://susmitjha.github.io/papers/pldi11.pdf).
You can run them using
```
python benchmark.py run set:hackdel synth:len-cegis
```
