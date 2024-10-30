import subprocess
import tempfile

from dataclasses import dataclass

from z3 import *

from synth import util

# wrapper around a object map for the parsed model
# this is used to pass the model to the synthesizer
# (necessary, as Model->Program parser needs evaluation methods)
# warning: do not use the setter of the model attribute
class _ParsedModelWrapper:
    def __init__(self, model):
        self.model = model

    def __getitem__(self, key):
        return self.model[str(key)]

    def evaluate(self, expr, model_completion=True):
        return self.model[str(expr)]

def _parse_smt2_output(ctx, model_string: str):
    # create always True and False bool z3 value constants
    b = Bool('p')
    z3_true = simplify(b == b)
    z3_false = simplify(Not(z3_true))

    model = {}
    # since linebreaks may be arbitrary, just remove them
    model_string = model_string.replace("\n", "").strip()

    # while we are not at the closing parenthesis of the model
    while not model_string.strip() == ")":
        if not model_string.startswith('(define-fun'):
            # cut off first character, hopefully just spaces; or "(model"
            model_string = model_string[1:]
            continue

        # cut off the define-fun
        model_string = model_string[len('(define-fun'):].strip()

        # get the name of the variable
        var_name, model_string = model_string.split(" ", 1)

        model_string = model_string.strip()

        # we expect empty function types
        if not model_string.startswith("()"):
            print("Expected empty function type")
            return None

        model_string = model_string[len("()"):].strip()

        # parse type and value
        if model_string.startswith("(_ BitVec"):
            # cut off the type
            model_string = model_string[len("(_ BitVec"):].strip()

            # get the bit width
            bit_width, model_string = model_string.split(")", 1)
            bit_width = int(bit_width)

            # cut off the space
            model_string = model_string.strip()

            # get the value
            value, model_string = model_string.split(")", 1)
            value = value.strip()

            # value has prefix #b -> binary value
            if value.startswith("#b"):
                value = value[len("#b"):]

                # convert to z3 value
                model[var_name] = BitVecVal(int(value, 2), bit_width, ctx=ctx)
            elif value.startswith("#x"):
                value = value[len("#x"):]

                # convert to z3 value
                model[var_name] = BitVecVal(int(value, 16), bit_width, ctx=ctx)
            else:
                print("Unknown bitvector value: " + value)
                exit(1)


        elif model_string.startswith("Bool"):
            # cut off the type
            model_string = model_string[len("Bool"):].strip()

            # get the value
            value, model_string = model_string.split(")", 1)
            value = value.strip()

            # convert to z3 value
            model[var_name] = z3_true if value == "true" else z3_false
        elif model_string.startswith("Int"):
            # cut off the type
            model_string = model_string[len("Int"):].strip()

            # get the value
            print(model_string)
            value, model_string = model_string.split(")", 1)
            value = value.strip()

            # convert to z3 value
            model[var_name] = IntVal(int(value), ctx=ctx)
        else:
            print("Unknown type in model: " + model_string)
            exit(1)

        # store value in model with pipes, as needed sometimes(?)
        model[f'|{var_name}|'] = model[var_name]

    return _ParsedModelWrapper(model)

@dataclass(frozen=True)
class _External(util.HasDebug):
    keep_file: bool = False
    """Keep temporary file for external solver for debugging purposes."""

    def solve(self, goal, theory):
        ctx = goal.ctx
        theory = theory if theory else 'ALL'
        s = Solver(ctx=ctx)
        t = Tactic('card2bv', ctx=ctx)
        for a in goal:
            # this would be great, if it did not leak internal z3 operators to the smt2 output
            for b in t(simplify(a)):
              s.add(b)
            # s.add(a)
        smt2_string = s.to_smt2()

        # replace internal z3 operators with smt2 operators
        smt2_string = smt2_string.replace("bvudiv_i", "bvudiv")
        smt2_string = smt2_string.replace("bvurem_i", "bvurem")
        smt2_string = smt2_string.replace("bvsdiv_i", "bvsdiv")
        smt2_string = smt2_string.replace("bvsrem_i", "bvsrem")
        # # replace empty and statements
        # smt2_string = smt2_string.replace("and)", "(and true))")
        bench = f'(set-option :produce-models true)\n(set-logic {theory})\n' + smt2_string + "\n(get-model)"
        with tempfile.NamedTemporaryFile(delete_on_close=not self.keep_file, mode='w+t') as f:
            print(bench, file=f)
            cmd = self._get_cmd(f.name)
            self.debug(2, bench)
            self.debug(1, 'running', cmd)
            with util.timer() as elapsed:
                p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                time = elapsed()

            f.close()
            output = p.stdout.decode('utf-8')
            self.debug(3, output)
            self.debug(2, p.stderr.decode('utf-8'))

            if output.startswith('sat'):
                smt_model = output.split("\n",1)[1]
                model = _parse_smt2_output(ctx, smt_model)
                return time, model
        return time, None

@dataclass(frozen=True)
class InternalZ3:
    tactic: str = ''
    """A tactic to construct the SMT solver (e.g. psmt for a parallel solver)"""

    parallel: bool = False
    """Enable Z3 parallel mode."""

    verbose: int = 0
    """Set Z3 verbosity level."""

    def __post_init__(self):
        if self.parallel or self.tactic == 'psmt':
            set_option("parallel.enable", True);
        if self.verbose > 0:
            set_option("verbose", self.verbose);
            set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

    def solve(self, goal, theory):
        ctx = goal.ctx
        if theory:
            s = SolverFor(theory, ctx=ctx)
        elif self.tactic:
            s = Tactic(self.tactic, ctx=ctx).solver()
        else:
            s = Solver(ctx=ctx)
        s.add(goal)
        with util.timer() as elapsed:
            res = s.check()
            time = elapsed()
        return time, s.model() if res == sat else None

@dataclass(frozen=True)
class ExternalZ3(_External):
    def _get_cmd(self, filename):
        return f'{os.getenv("Z3_PATH", default="z3")} {filename}'

@dataclass(frozen=True)
class Yices(_External):
    def _get_cmd(self, filename):
        return f'{os.getenv("YICES_PATH", default="yices-smt2")} {filename} --smt2-model-format'

@dataclass(frozen=True)
class Bitwuzla(_External):
    def _get_cmd(self, filename):
        return f'{os.getenv("BITWUZLA_PATH", default="bitwuzla")} -m {filename}'

@dataclass(frozen=True)
class Cvc5(_External):
    def _get_cmd(self, filename):
        return f'{os.getenv("CVC5_PATH", default="cvc5")} {filename}'

_SOLVERS = InternalZ3 | ExternalZ3 | Yices | Bitwuzla | Cvc5

@dataclass(frozen=True)
class HasSolver:
    solver: _SOLVERS = InternalZ3()
    """Solver to use for synthesis."""