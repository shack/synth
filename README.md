# Synthesis of Loop-free Programs

This is a synthesis algorithm that combines a [constrained-based counterexample-guided synthesis algorithm](https://susmitjha.github.io/papers/pldi11.pdf) with the program-length based approach found in recent work on [SAT-based exact synthesis](https://infoscience.epfl.ch/record/271569/files/WH-IEEE-SAT-Based.pdf) for circuits.
A similar technique is also known as [linear encoding](https://github.com/lorisdanto/cse291-program-synthesis-loris).
It is implemented using the [Z3](https://github.com/Z3Prover/z3) SMT Python bindings but can use any [SMTLIB](https://www.smtlib.org)-compatible solver for synthesis.

The key features of this tool are:
- [SyGuS](https://sygus-org.github.io/assets/pdf/SyGuS-IF_2.1.pdf) frontend (`sygus.py`) and Python API (see below)
- Multi-instance, multi-function synthesis constraints:
  The algorithm can synthesise multiple functions which each can be instantiated arbitrarily often in the synthesis constraint.
  This allows for hyper-property specifications, e.g. a function being constant.
  Note that functional correctness is a special case in which the function to be synthesised appears only once.
- Synthesises DAGs (default) and trees
- Synthesises constants
- Finds the shortest program by construction
- Optimisation mode in which another optimisation objective can be specified and lexicographic optimum of that goal and program length (or vice versa) is found
- Supports bit vector downscaling (solve the synthesis problem with smaller bit widths and try to generalise to larger ones)
- Supports any [SMT-LIB](https://www.smt-lib.org) sort

## Prerequisites

You need the following packages:

[z3-solver](https://pypi.org/project/z3-solver/),
[tyro](https://pypi.org/project/tyro/),
[tinysexpr](https://github.com/shack/tinysexpr)

See `pyproject.toml`.

## How to Use

This package is best used with [uv](https://github.com/astral-sh/uv).

### SyGuS

```
uv run sygus.py synth <sygus file>
```

The first parameter selects the synthesizer.
There are other options available (replace than option with `--help` to see them).

### Python API

The package provides different synthesis algorithms in its `synth` subdirectory.
Each synthesis algorithm comes with a class that holds parameters to the synthesis and has a function
```Python
def synth_prgs(self, problem: Problem)
```
where `Problem` is a class that holds the synthesis constraint and the specification of several functions to be synthesised.
`synth_prg` returns a pair of the synthesized program (or `None`) and statistics information about the synthesis process.

The following example shows how to synthesize a function that checks if a bit vector is a power of two:
```Python
from synth.spec import Constraint, Problem, SynthFunc, Spec, Task
from synth.synth_n import LenCegis
from synth.oplib import Bv, nonterminal_from_ops
from z3 import *

# set bit width to 8
width   = 8
# define two bit vector variables for the argument and result of the function
r, x    = BitVecs('r x', width)

# an expression that is true if and only if x is a power of 2 or x is 0
is_pow2 = Or([x == 0] + [BitVecVal(1 << i, width) == x for i in range(width)])

# define the specification of the function to synthesize by means
# of a synthesis constraint. Note that the specification is
# non-deterministic because multiple values of r satisfy the specification
# in case the value of x is not a power of 2.
# The function_applications parameter lists all applications of the
# function to be synthesized. This is done by specifying the output
# variables (here: r) and the corresponding input expressions (here: x).
# Note that the synthesis constraint may refer to multiple functions
# and each of the functions may be applied multiple times in the constraint.
constraint = Constraint(
    phi=If(is_pow2, r == 0, r != 0),
    params=[x],
    function_applications={
        ('is_pow2', (x,)): (r,)
    }
)

# Create the synthesis function specification.
# This function takes a list of operators and creates a SyGuS grammar
# based on the operator types.
# Note that there is an explicit API to create more complex grammars.
func = synth_func_from_ops([ x.sort() ], [ r.sort() ], Bv(width).ops)

# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraints=[constraint], funcs={ 'is_pow2': func })

# Synthesize a program and print it if it exists
prgs, stats = LenCegis().synth_prgs(problem)
if prgs:
    print(prgs['is_pow2'].to_string(sep='\n'))
else:
   print('No program found')
```
There is also a more lightweight interface using the function `Task` if you are interested simple functional correctness specifications:
```python

# For functional specifications and simple grammars, we can also use the
# convenient Task interface:
spec = Spec('is_pow2', If(is_pow2, r == 0, r != 0), inputs=[x], outputs=[r])
problem = Task(spec, Bv(width).ops)

# Synthesize a program and print it if it exists
prgs, stats = LenCegis().synth_prgs(problem)
if prgs:
    print(prgs['is_pow2'].to_string(sep='\n'))
else:
   print('No program found')
```

## Synthesis of Boolean Functions

`boolfunc` synthesizes boolean functions. It has three modes of operation:
1. Pass function values as numbers via the command line:
   ```
   uv run boolfunc.py op:func 0b00010010
   uv run boolfunc.py op:func 1234
   uv run boolfunc.py op:func 0xabcd1234
   ```
   synthesizes 3-input function 0x12, 4-input function 0x1234, and 5-input function 0xabcd1234
2. Read in function values from a file
   ```
   uv run boolfunc.py op:file funcs.txt
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
   uv run boolfunc.py op:pla filename.pla
   ```

You can specify the library of operators (with an optional maximum count) and a maximum count of constants (True, False) like this:
```
uv run boolfunc.py --ops nand2:2,nor2,and2:4 --consts 3 ...
```
which would look for solutions with at most 3 constants, 2 2-operand nands, 4 2-operand ands, and an arbitrary amount of 2-operand nors.

See `uv run boolfunc.py --help` for more options.

## Hacker's Delight Benchmarks

`bench/hackdel_light.py` provides benchmarks 1-18 and `bench/hackdel_heavy.py` provides benchmarks 19-24 from the [Brahma paper](https://susmitjha.github.io/papers/pldi11.pdf).
You can run them using
```
uv run benchmark.py run set:hackdel-light synth:len-cegis
```

## Connecting External Solvers

This package is built on top of the [z3 Python bindings](https://z3prover.github.io/api/html/namespacez3py.html).
However, you can use any SMT solver that offers a [SMTLIB2](https://smt-lib.org/) interface for synthesis.
To this end, provide a file `solvers.json` in the following form:
```
{
   "my_solver": {
      "path": "<path to the binary of the solver>",
      "args": [ "{filename}" ]
   },
   ... more solvers ...
}
```
where the args field is a list of command line args to the solver in which `{filename}` will be expanded to the input filename.
You can then use the solver with adding the flags:
```
synth.solver:config --synth.solver.name my_solver
```
