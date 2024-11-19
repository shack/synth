import subprocess
import tempfile
import shutil

import tinysexpr

from typing import Optional
from dataclasses import dataclass
from pathlib import Path
from io import StringIO

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
    model = {}
    sexp = tinysexpr.read(StringIO(model_string))
    # some solvers don't say "model" at the beginning
    if sexp[0] == 'model':
        sexp = sexp[1:]
    for d, var, _, sort, val in sexp:
        assert d == 'define-fun'
        match sort:
            case 'Bool':
                model[var] = BoolVal(val == "true", ctx=ctx)
            case 'Int':
                match val:
                    case ['-', i]:
                        i = -int(i)
                    case i:
                        i = int(i)
                model[var] = IntVal(i, ctx=ctx)
            case [_,'BitVec', width]:
                assert len(val) >= 2, f'bitvector value too short: {val}'
                match val[:2]:
                    case '#b': base = 2
                    case '#x': base = 16
                    case _: assert False, f'unknown bitvector value: {val}'
                val = int(val[2:], base)
                model[var] = BitVecVal(val, int(width), ctx=ctx)
        # store value in model with pipes, as needed sometimes(?)
        model[f'|{var}|'] = model[var]
    return _ParsedModelWrapper(model)

@dataclass(frozen=True)
class _External(util.HasDebug):
    keep_file: bool = False
    """Keep temporary file for external solver for debugging purposes."""

    path: Optional[Path] = None
    """Path to the external solver executable."""

    def _env_var(self):
        return f'{self.binary.upper()}_PATH'

    def _resolve_binary(self):
        if self.path and self.path.is_file():
            return str(self.path)
        elif (e := self._env_var()) in os.environ:
            return os.environ[e]
        elif res := shutil.which(self.binary):
            return res
        else:
            raise FileNotFoundError(f'Could not find {self.binary} in PATH or environment variable {self._env_var()}')

    def _get_cmdline_params(self, filename):
        return f'{filename}'

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
        with tempfile.NamedTemporaryFile(delete_on_close=False, delete=not self.keep_file, mode='w+t') as f:
            print(bench, file=f)
            binary = self._resolve_binary()
            params = self._get_cmdline_params(f.name)
            cmd = f'{binary} {params}'
            self.debug(2, bench)
            self.debug(1, 'running', cmd)
            f.close()
            with util.timer() as elapsed:
                p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                time = elapsed()

            output = p.stdout.decode('utf-8')
            self.debug(3, output)
            self.debug(2, p.stderr.decode('utf-8'))

            if output.startswith('sat'):
                smt_model = output.split("\n",1)[1]
                model = _parse_smt2_output(ctx, smt_model)
                return time, model
        return time, None

@dataclass(frozen=True)
class ExternalZ3(_External):
    binary = 'z3'

@dataclass(frozen=True)
class Yices(_External):
    binary: str = 'yices-smt2'

    def _env_var(self):
        return 'YICES_PATH'

    def _get_cmdline_params(self, filename):
        return f'{filename} --smt2-model-format'

@dataclass(frozen=True)
class Bitwuzla(_External):
    binary: str = 'bitwuzla'

    def _get_cmdline_params(self, filename):
        return f'-m {filename}'

@dataclass(frozen=True)
class Cvc5(_External):
    binary: str = 'cvc5'

@dataclass(frozen=True)
class InternalZ3:
    tactic: str = ''
    """A tactic to construct the SMT solver (e.g. psmt for a parallel solver)"""

    parallel: bool = False
    """Enable Z3 parallel mode."""

    verbose: int = 0
    """Set Z3 verbosity level."""

    timeout: int = 0
    """Timeout for the solver in seconds."""

    def __post_init__(self):
        if self.parallel or self.tactic == 'psmt':
            set_option("parallel.enable", True);
        if self.verbose > 0:
            set_option("verbose", self.verbose);
            set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

    def solve(self, goal, theory):
        set_option("sat.random_seed", 0)
        set_option("smt.random_seed", 0)
        ctx = goal.ctx
        if theory:
            s = SolverFor(theory, ctx=ctx)
        elif self.tactic:
            s = Tactic(self.tactic, ctx=ctx).solver()
        else:
            s = Solver(ctx=ctx)
        if self.timeout:
            s.set("timeout", self.timeout * 1000)
        s.add(goal)
        with util.timer() as elapsed:
            res = s.check()
            time = elapsed()
        return time, s.model() if res == sat else None

_SOLVERS = InternalZ3 | ExternalZ3 | Yices | Bitwuzla | Cvc5

@dataclass(frozen=True)
class HasSolver:
    solver: _SOLVERS = InternalZ3()
    """Solver to use for synthesis."""