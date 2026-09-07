from z3 import *

from synth.util import timer, Debug, no_debug
from synth.spec import Constraint

class Cegis:
    """CEGIS loop whose state is bound to one solver.

    `synth` may be called repeatedly on the same object.  Between two calls
    the caller can add constraints to the solver, e.g. to exclude a program
    that was found.  The counterexamples of earlier calls stay in the solver
    and are not encoded again; every instance gets a fresh id.
    """
    def __init__(self, solver, clauses: list[Constraint], synths: dict[str, Any],
                 initial_samples=(), d: Debug=no_debug, verbose=False):
        assert len(clauses) > 0
        self.solver  = solver
        self.clauses = clauses
        self.synths  = synths
        self.d       = d
        self.verbose = verbose
        self.samples = []
        # index of the clause that produced the last counterexample;
        # verification of the next program starts with the clause after it
        self._curr   = 0
        for s in initial_samples:
            self.add_sample(s, 0)

    def add_sample(self, sample, idx):
        instance_id = f'{len(self.samples)}'
        if self.d.has('cex'):
            cex = ' '.join(map(lambda s: s.sexpr(), sample))
            print(f'(cex {instance_id} {idx} ({cex}))')
        # Z3 seems to optimize each assertion separately,
        # so fuse all assertions into one.
        tmp = list()
        self.clauses[idx].add_instance_constraints(instance_id, self.synths, sample, tmp)
        self.solver.add(And(tmp))
        self.samples.append(sample)

    def _solve(self):
        d, solver = self.d, self.solver
        stat = {}
        if self.verbose:
            stat['synth_constr'] = str(solver)
        synth_time, model = solver.solve()
        if d.has('synth_constr'):
            print('synth_constr:', solver)
        if d.has('synth_model'):
            print('synth_model:', model)
        d('time', f'(synth-time {synth_time / 1e9:.3f})')
        stat['synth_time'] = synth_time
        if model is not None:
            if self.verbose:
                stat['model'] = str(model)
            prgs = { name: synth.create_prg(model) for name, synth in self.synths.items() }
            stat['success'] = True
            stat['prgs'] = { name: prg.sexpr(name) for name, prg in prgs.items() }
            d('prg', f'(prg\n{'\n'.join(prg.sexpr(name, sep='\n\t') for name, prg in prgs.items())})')
            return prgs, stat
        else:
            stat['success'] = False
            d('success', f'(fail)')
            return None, stat

    def synth(self):
        """Runs the loop until a program passes verification or no program
           is left.  Returns (prgs, stats); prgs is None in the latter case."""
        stats = []
        with timer() as elapsed:
            while True:
                prgs, stat = self._solve()
                stat['n_samples'] = len(self.samples)
                stats.append(stat)
                if prgs is None:
                    break
                for i in range(len(self.clauses)):
                    j = (self._curr + 1 + i) % len(self.clauses)
                    counterexample, stat['verif'] = self.clauses[j].verify(prgs, d=self.d, verbose=self.verbose)
                    if counterexample is not None:
                        # we got a counterexample, so add it to the samples
                        self._curr = j
                        self.add_sample(counterexample, j)
                        break
                else:
                    break
            return prgs, { 'time': elapsed(), 'stats': stats }

def cegis(solver, clauses: list[Constraint], synths: dict[str, Any],
          initial_samples=[], d: Debug=no_debug, verbose=False):
    """One-shot CEGIS on a fresh solver.  Returns (prgs, stats, samples)."""
    c = Cegis(solver, clauses, synths, initial_samples, d, verbose)
    prgs, stats = c.synth()
    return prgs, stats, c.samples
