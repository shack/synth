# Synthesis of Loop-free Programs

This is a synthesis algorithm that combines a [counterexample-guided synthesis algorithm](https://susmitjha.github.io/papers/pldi11.pdf) with the program-length based approach found in recent work on [SAT-based exact synthesis](https://infoscience.epfl.ch/record/271569/files/WH-IEEE-SAT-Based.pdf) for circuits.
A similar technique is also known as [linear encoding](https://github.com/lorisdanto/cse291-program-synthesis-loris).
It is implemented using the [Z3](https://github.com/Z3Prover/z3) SMT Python bindings but can use any [SMTLIB](https://www.smtlib.org)-compatible solver for synthesis.

The key features of this tool are:
- [SyGuS](https://sygus-org.github.io/assets/pdf/SyGuS-IF_2.1.pdf) frontend (`python sygus.py`) and Python API (see below)
- Multi-instance, multi-function synthesis constraints:
  The algorithm can synthesise multiple functions which each can be instantiate arbitrarily often in the synthesis constraint.
  This allows for hyper-property specifications, e.g. a function being constant.
  Note that functional correctness is a special case in which the function to be synthesised appears only once.
- Synthesises DAGs (default) and trees
- Finds the shortest program
- Optimisation mode in which another optimisation objective can be specified and lexicographic optimum of that goal and program length (or vice versa) is found
- Supports bit vector downscaling (solve the synthesis problem with smaller bit widths and try to generalise to larger ones)
- Supports any SMTLIB sort (however, parsing models from external (non-Z3) solvers only works for bit vectors, ints, reals, bools for now)
- Contains [Brahma](https://susmitjha.github.io/papers/pldi11.pdf) implementation for comparison

## Prerequisites

You need the following packages:

[z3-solver](https://pypi.org/project/z3-solver/),
[tyro](https://pypi.org/project/tyro/),
[tinysexpr](https://github.com/shack/tinysexpr)

See `pyproject.toml`.

## How to Use

### SyGuS

```
python sygus.py synth:len-cegis <sygus file>
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
from synth.spec import Constraint, Problem, SynthFunc
from synth.synth_n import LenCegis
from synth.oplib import Bv
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
        'is_pow2': [ ([r], [x]) ]
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
    ops={ op: None for op in Bv(width).ops }
)

# The synthesis problem consists of the constraint and the functions to synthesise.
problem = Problem(constraint=constraint, funcs={ 'is_pow2': func })

# Synthesize a program and print it if it exists
prgs, stats = LenCegis().synth_prgs(problem)
if prgs:
    print(prgs['is_pow2'].to_string(sep='\n'))
else:
   print('No program found')
```

## Differences to SyGuS

- We ignore grammar specifications.
  The compatibility of operators is solely derived from the signature of the operator based on the used/produced the SMTLIB sorts.
  This means that we might produce solutions that violate the specified grammar but are, of course, still semantically correct.
  In practice, this is not a big restriction because in most settings, the grammar non-terminals are merely used to specify sorts.
- Using the Python API you have more fine-grained control in restricting how often each operator and constant can be used.
- In principle, we can synthesise arbitrary constants even though SuGuS requires to list all the constants that are allowed in the synth-fun.

## Synthesis of Boolean Functions

`boolfunc` synthesizes boolean functions. It has three modes of operation:
1. Pass function values as numbers via the command line:
   ```
   python boolfunc.py op:func 0b00010010
   python boolfunc.py op:func 1234
   python boolfunc.py op:func 0xabcd1234
   ```
   synthesizes 3-input function 0x12, 4-input function 0x1234, and 5-input function 0xabcd1234
2. Read in function values from a file
   ```
   python boolfunc.py op:file funcs.txt
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
   python boolfunc.py op:pla filename.pla
   ```

You can specify the library of operators (with an optional maximum count) and a maximum count of constants (True, False) like this:
```
python boolfunc.py --ops nand2:2,nor2,and2:4 --consts 3 ...
```
which would look for solutions with at most 3 constants, 2 2-operand nands, 4 2-operand ands, and an arbitrary amount of 2-operand nors.

See `python boolfunc.py --help` for more options.

## Hacker's Delight Benchmarks

`bench/hackdel_light.py` provides benchmarks 1-18 and `bench/hackdel_heavy.py` provides benchmarks 19-24 from the [Brahma paper](https://susmitjha.github.io/papers/pldi11.pdf).
You can run them using
```
python benchmark.py run set:hackdel-light synth:len-cegis
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
