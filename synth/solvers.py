import subprocess
import tempfile
import shutil
import types
import json

import tinysexpr

from dataclasses import dataclass, field
from pathlib import Path
from io import StringIO

from z3 import *

from synth import util

class ExternalSolverAdapter:
    def __init__(self, external, theory):
        self.external = external
        self.theory = theory

        self.constraints = []
        self.stack = []

    def add(self, constraint):
        if type(constraint) == list:
            for c in constraint:
                self.constraints.append(c)
        else:
            self.constraints.append(constraint)

    def __repr__(self):
        return repr(self.constraints)

    def __str__(self):
        return str(self.constraints)

    def assertions(self):
        return self.constraints

    def push(self):
        self.stack.append(len(self.constraints))

    def pop(self):
        i = self.stack.pop()
        assert i <= len(self.constraints), f'pop {i} > {len(self.constraints)}'
        self.constraints = self.constraints[:i]

    def solve(self, timeout=None):
        return self.external.solve(self.theory, self.constraints, timeout)


# wrapper around a object map for the parsed model
# this is used to pass the model to the synthesizer
# (necessary, as Model->Program parser needs evaluation methods)
# warning: do not use the setter of the model attribute
class _ParsedModelWrapper:
    def __init__(self, model):
        self.model = model

    def __getitem__(self, key):
        return self.model[str(key)] if str(key) in self.model else None

    def __repr__(self):
        return repr(self.model)

    def decls(self):
        return self.model.keys()

    def evaluate(self, expr, model_completion=True):
        return self.model[str(expr)]

def _parse_smt2_output(model_string: str):
    model = {}
    sexp = tinysexpr.read(StringIO(model_string))
    # some solvers don't say "model" at the beginning
    if sexp[0] == 'model':
        sexp = sexp[1:]
    for d, var, _, sort, val in sexp:
        assert d == 'define-fun'
        match sort:
            case 'Bool':
                model[var] = BoolVal(val == "true")
            case 'Int':
                match val:
                    case ['-', i]:
                        i = -int(i)
                    case i:
                        i = int(i)
                model[var] = IntVal(i)
            case [_,'BitVec', width]:
                assert len(val) >= 2, f'bitvector value too short: {val}'
                match val[:2]:
                    case '#b': base = 2
                    case '#x': base = 16
                    case _: assert False, f'unknown bitvector value: {val}'
                val = int(val[2:], base)
                model[var] = BitVecVal(val, int(width))
        # store value in model with pipes, as needed sometimes(?)
        model[f'|{var}|'] = model[var]
    return _ParsedModelWrapper(model)

@dataclass(frozen=True)
class _External(util.HasDebug):
    keep_file: bool = field(kw_only=True, default=False)
    """Keep temporary file for external solver for debugging purposes."""

    def has_minimize(self):
        return False

    def _get_cmd(self, filename):
        return f'{self.path} ' + ' '.join(a.format(filename=filename) for a in self.args)

    def create(self, theory):
        return ExternalSolverAdapter(self, theory)

    def solve(self, theory, constraints, timeout):
        theory = theory if theory else 'ALL'
        s = Solver()
        t = Tactic('card2bv')
        for a in constraints:
            for b in t(simplify(a)):
              s.add(b)
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
            cmd = self._get_cmd(f.name)
            self.debug('ext_solver', bench)
            self.debug('ext_solver', 'running', cmd)
            f.close()
            with util.timer() as elapsed:
                try:
                    p = subprocess.run(cmd, shell=True, timeout=timeout,
                                       capture_output=True, text=True)
                    time = elapsed()
                    output = p.stdout
                    self.debug('ext_solver_io', output)
                    self.debug('ext_solver_io', p.stderr)

                    if output.startswith('sat'):
                        smt_model = output.split("\n",1)[1]
                        model = _parse_smt2_output(smt_model)
                        return time, model
                    else:
                        return time, None
                except subprocess.TimeoutExpired:
                    return timeout, None

def _consolidate_solver_path(path: Path):
    path = Path(os.path.expanduser(os.path.expandvars(path)))
    if path.exists() and path.is_file():
        return path
    elif res := shutil.which(path):
        return Path(res)
    else:
        raise FileNotFoundError(f'External solver {path} not found and not in path')

@dataclass(frozen=True)
class Binary(_External):
    path: Path
    """Path of the external solver binary (environment variables are expanded)."""

    args: list[str] | None = field(default_factory=lambda: ['{filename}'])
    """Arguments to pass to the external solver binary (use {filename} for the file argument)."""

    def __post_init__(self):
        self.path = _consolidate_solver_path(self.path)

def get_consolidated_solver_config(filename='solvers.json'):
    res = {}
    with open(filename) as f:
        cfg = json.load(f)
        for name, c in cfg.items():
            try:
                res[name] = {
                    'path': _consolidate_solver_path(c['path']),
                    'args': c.get('args', ['{filename}'])
                }
            except FileNotFoundError as e:
                pass
    return res

@dataclass(frozen=True)
class Config(_External):
    name: str
    """Name of the solver in the config file."""

    file: Path = Path('solvers.json')
    """Path of the external solver config file (default: solvers.json)."""

    def __post_init__(self):
        cfg = get_consolidated_solver_config(self.file)
        assert self.name in cfg, f'Solver {self.name} not available in {self.file} (maybe path is invalid?)'
        cfg = cfg[self.name]
        self.path = _consolidate_solver_path(cfg['path'])
        self.args = cfg.get('args', ['{filename}'])

@dataclass(frozen=True)
class Z3:
    parallel: bool = False
    """Enable Z3 parallel mode."""

    verbose: int = 0
    """Set Z3 verbosity level."""

    def has_minimize(self):
        return False

    def __post_init__(self):
        if self.parallel:
            set_option("parallel.enable", True);
        if self.verbose > 0:
            set_option("verbose", self.verbose);

    def _solve(solver, timeout=None):
        if timeout:
            solver.set("timeout", timeout * 1000)
        with util.timer() as elapsed:
            res = solver.check()
            time = elapsed()
        model = solver.model() if res == sat else None
        return time, model

    def _create_solver(self, theory):
        return SolverFor(theory) if theory else Solver()

    def create(self, theory):
        set_option("sat.random_seed", 0)
        set_option("smt.random_seed", 0)
        s = self._create_solver(theory)
        # TODO: Experiment with that. Without this, AtMost and AtLease
        # constraints are translated down to boolean formulas.
        # s.set("sat.cardinality.solver", True)
        s.solve = types.MethodType(Z3._solve, s)
        return s

@dataclass(frozen=True)
class Z3Opt(Z3):
    def has_minimize(self):
        return True

    def _create_solver(self, theory):
        return Optimize()

SOLVERS = Z3 | Z3Opt | Config | Binary

@dataclass(frozen=True)
class HasSolver:
    solver: SOLVERS = field(kw_only=True, default_factory=Z3)
    """Solver to use for synthesis."""