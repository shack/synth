from collections import deque
from z3 import *

from synth.util import timer, Debug, no_debug
from synth.spec import Constraint

def cegis(solver,
          clauses: list[Constraint],
          synths: dict[str, Any],
          initial_samples=[],
          d: Debug=no_debug, verbose=False):
    samples = []
    assert len(clauses) > 0

    def add_sample(sample, idx):
        instance_id = f'{len(samples)}'
        if d.has('cex'):
            cex = ' '.join(map(lambda s: s.sexpr(), sample))
            print(f'(cex {instance_id} {idx} ({cex}))')
        clauses[idx].add_instance_constraints(instance_id, synths, sample, solver)
        samples.append(sample)

    def synth():
        stat = {}
        if verbose:
            stat['synth_constr'] = str(solver)
        synth_time, model = solver.solve()
        if d.has('synth_constr'):
            print('synth_constr:', solver)
        if d.has('synth_model'):
            print('synth_model:', model)
        d('time', f'(synth-time {synth_time / 1e9:.3f})')
        stat['synth_time'] = synth_time
        if model:
            if verbose:
                stat['model'] = str(model)
            prgs = { name: synth.create_prg(model) for name, synth in synths.items() }
            stat['success'] = True
            stat['prgs'] = { name: prg.sexpr(name) for name, prg in prgs.items() }
            d('prg', f'(prg\n{'\n'.join(prg.sexpr(name, sep='\n\t') for name, prg in prgs.items())})')
            return prgs, stat
        else:
            stat['success'] = False
            d('success', f'(fail)')
            return None, stat

    if initial_samples:
        for s in initial_samples:
            add_sample(s, 0)

    stats = []

    with timer() as elapsed:
        done = False
        curr = 0
        while not done:
            # call the synthesizer with more counter-examples
            prgs, stat = synth()
            stat['n_samples'] = len(samples)
            stats.append(stat)

            done = True
            if prgs is not None:
                for i in range(0, len(clauses)):
                    j = (curr + 1 + i) % len(clauses)
                    counterexample, stat['verif'] = clauses[j].verify(prgs, d=d, verbose=verbose)
                    if counterexample is not None:
                        # we got a counterexample, so add it to the samples
                        curr = j
                        add_sample(counterexample, curr)
                        done = False
                        break

        return prgs, { 'time': elapsed(), 'stats': stats }, samples