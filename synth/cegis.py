from z3 import *

from synth.util import timer, Debug, no_debug
from synth.spec import Constraint

def cegis(solver, constr: Constraint, synths: dict[str, Any],
          initial_samples=[], d: Debug=no_debug, verbose=False):
    samples = []

    def add_sample(sample):
        d('cex', 'sample', len(samples), sample)
        constr.add_instance_constraints(f'{len(samples)}', synths, sample, solver)
        samples.append(sample)

    def synth():
        stat = {}
        if verbose:
            stat['synth_constr'] = str(solver)
        synth_time, model = solver.solve()
        if verbose:
            d('synth_constr', 'synth constr:', solver)
            d('synth_model', 'synth model:', model)
        d('time', f'synth time: {synth_time / 1e9:.3f}')
        stat['synth_time'] = synth_time
        if model:
            if verbose:
                stat['model'] = str(model)
            prgs = { name: synth.create_prg(model) for name, synth in synths.items() }
            stat['success'] = True
            stat['prgs'] = { name: str(prg) for name, prg in prgs.items() }
            d('synth_prg', 'program:', stat['prgs'])
            return prgs, stat
        else:
            stat['success'] = False
            d('success', f'synthesis failed')
            return None, stat

    if initial_samples:
        for s in initial_samples:
            add_sample(s)
    else:
        s = constr.counterexample_eval.sample_n(1)
        add_sample(s[0])

    stats = []
    with timer() as elapsed:
        while True:
            # call the synthesizer with more counter-examples
            prgs, stat = synth()
            stat['n_samples'] = len(samples)
            stats.append(stat)

            if not prgs is None:
                # check if the program is correct
                counterexample, stat['verif'] = constr.verify(prgs, d=d, verbose=verbose)
                if counterexample:
                    # we got a counterexample, so add it to the samples
                    add_sample(counterexample)
                    continue
            return prgs, { 'time': elapsed(), 'stats': stats }, samples