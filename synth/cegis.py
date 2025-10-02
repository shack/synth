from typing import Dict, Any

from z3 import *

from synth.util import timer
from synth.spec import Constraint

def cegis(solver, constr: Constraint, synths: Dict[str, Any], options, initial_samples):
    d = options.debug
    samples = []

    def add_sample(sample):
        d(1, 'sample', len(samples), sample)
        samples.append(sample)
        constr.add_instance_constraints(f'{len(samples) - 1}', synths, sample, solver)

    def synth():
        stat = {}
        if options.detailed_stats:
            stat['synth_constraint'] = str(solver)
        synth_time, model = solver.solve()
        # print(solver)
        d(2, f'synth time: {synth_time / 1e9:.3f}')
        stat['synth_time'] = synth_time
        if model:
            if options.detailed_stats:
                stat['model'] = str(model)
            prgs = { name: synth.create_prg(model) for name, synth in synths.items() }
            stat['success'] = True
            stat['prgs'] = { name: str(prg) for name, prg in prgs.items() }
            d(3, 'program:', stat['prgs'])
            return prgs, stat
        else:
            stat['success'] = False
            d(1, f'synthesis failed')
            return None, stat

    for s in initial_samples:
        add_sample(s)
    stats = []
    with timer() as elapsed:
        while True:
            # call the synthesizer with more counter-examples
            prgs, stat = synth()
            stat['n_samples'] = len(samples)
            stats.append(stat)

            if not prgs is None:
                # check if the program is correct
                counterexample, stat['verif'] = constr.verify(prgs, options.detailed_stats)
                if counterexample:
                    # we got a counterexample, so add it to the samples
                    add_sample(counterexample)
                    continue
            return prgs, { 'time': elapsed(), 'stats': stats }, samples