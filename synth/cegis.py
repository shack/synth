from z3 import *

from synth.util import Debug, timer, eval_model, no_debug
from synth.spec import Spec

class CegisBaseSynth:
    def __init__(self, spec: Spec, debug: Debug = no_debug):
        self.spec = spec
        self.n_samples = 0
        self.samples = []
        self.d = debug

        # I tried to create a solver here, add the spec constraint
        # and precondition and use push/pop to add the program but that
        # was way slower and led to huge verification times for some programs...

    def _verify(self, prg):
        # push a new verification solver state
        # and add equalities that evaluate the program
        self.verif = Solver()
        self.verif.add(self.spec.precond)
        self.verif.add(Not(self.spec.phi))
        for c in prg.eval_clauses():
            self.verif.add(c)

        stat = {}
        if self.options.detailed_stats:
            stat['verif_constraint'] = str(self.verif)
        with timer() as elapsed:
            res = self.verif.check()
            verif_time = elapsed()
        stat['verif_time'] = verif_time
        self.d(2, f'verif time {verif_time / 1e9:.3f}')

        if res == sat:
            # there is a counterexample, reiterate
            m = self.verif.model()
            counterexample = eval_model(m, self.spec.inputs)
            if self.options.detailed_stats:
                stat['verif_model'] = str(m)
                stat['counterexample'] = [ str(v) for v in counterexample ]
            return counterexample, stat
        else:
            # we found no counterexample, the program is therefore correct
            self.d(1, 'no counter example found')
            stat['counterexample'] = []
            return [], stat

    def _add_sample(self, sample):
        self.samples.append(sample)
        # add a new instance of the specification for each sample
        self.d(1, 'sample', self.n_samples, sample)
        self.add_constr_instance(self.n_samples)
        if self.spec.is_deterministic and self.spec.is_total:
            # if the specification is deterministic and total we can
            # just use the specification to sample output values and
            # include them in the counterexample constraints.
            out_vals = self.spec.eval(sample)
            self.add_constr_io_sample(self.n_samples, sample, out_vals)
        else:
            # if the spec is not deterministic or total, we have to
            # express the output of the specification implicitly by
            # the formula of the specification.
            self.add_constr_io_spec(self.n_samples, sample)
        self.add_constr_opt_instance(self.n_samples)
        self.n_samples += 1

    def _synth(self):
        stat = {}
        self.solver.push()
        self.add_cross_instance_constr(self.n_samples - 1)
        if self.options.detailed_stats:
            stat['synth_constraint'] = str(self.solver)
        synth_time, model = self.solver.solve()
        self.solver.pop()
        self.d(2, f'synth time: {synth_time / 1e9:.3f}')
        stat['synth_time'] = synth_time
        if not model is None:
            if self.options.detailed_stats:
                stat['model'] = str(model)
            prg = self.create_prg(model)
            stat['success'] = True
            stat['prg'] = str(prg)
            self.d(3, 'program:', stat['prg'])
            return prg, stat
        else:
            stat['success'] = False
            self.d(1, f'synthesis failed')
            return None, stat

    def synth_prg(self):
        """Synthesise one program."""
        stats = []
        with timer() as elapsed:
            while True:
                # call the synthesizer with more counter-examples
                prg, stat = self._synth()
                stats.append(stat)

                if prg is None:
                    self.d(1, f'synthesis failed')
                else:
                    # check if the program is correct
                    counterexample, stat['verif'] = self._verify(prg)
                    if counterexample:
                        # we got a counterexample, so add it to the samples
                        self._add_sample(counterexample)
                        continue
                return prg, { 'time': elapsed(), 'stats': stats }