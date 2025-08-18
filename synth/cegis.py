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

        self.d(3, 'verif', self.verif)
        with timer() as elapsed:
            res = self.verif.check()
            verif_time = elapsed()
        self.d(2, f'verif time {verif_time / 1e9:.3f}')

        if res == sat:
            # there is a counterexample, reiterate
            m = self.verif.model()
            counterexample = eval_model(m, self.spec.inputs)
            self.d(4, 'verification model', m)
            self.d(4, 'verif sample', counterexample)
            return counterexample, verif_time
        else:
            # we found no counterexample, the program is therefore correct
            self.d(1, 'no counter example found')
            return [], verif_time

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
        if self.options.dump_constr:
            s = Solver()
            s.add(self.synth)
            with open(f'synth_{self.spec.name}_{self.n_insns}_{self.n_samples}.smt2', 'wt') as f:
                print(s.to_smt2(), file=f)
        stat = {}
        self.d(3, 'synth', self.n_samples, self.synth)
        self.synth.push()
        self.add_cross_instance_constr(self.n_samples - 1)
        if self.d.level >= 4:
            stat['constraint'] = str(self.synth)
        self.d(2, 'synth constraints:', self.synth)
        synth_time, model = self.synth.solve()
        self.synth.pop()
        self.d(2, f'synth time: {synth_time / 1e9:.3f}')
        stat['synth_time'] = synth_time
        if not model is None:
            if self.d.level >= 4:
                stat['model'] = str(model)
            self.d(4, 'model: ', model)
            if self.options.dump_model:
                with open(f'model_{self.spec.name}_{self.n_insns}_{self.n_samples}.txt', 'wt') as f:
                    for d in model.decls():
                        print(d, model[d], file=f)
            prg = self.create_prg(model)
            stat['success'] = True
            stat['prg'] = str(prg).replace('\n', '; ')
            self.d(2, 'program:', stat['prg'])
            return prg, stat
        else:
            stat['success'] = False
            self.d(2, f'synthesis failed')
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
                    counterexample, stat['verif_time'] = self._verify(prg)
                    if counterexample:
                        # we got a counterexample, so add it to the samples
                        self._add_sample(counterexample)
                        continue
                return prg, { 'time': elapsed(), 'stats': stats }