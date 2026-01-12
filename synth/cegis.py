from z3 import *

from synth.util import timer, Debug, no_debug
from synth.spec import Constraint

def cegis(solver,
          clauses: list[BoolRef],
          synths: dict[str, Any],
          initial_samples=[],
          d: Debug=no_debug, verbose=False):
    samples = []

    def add_sample(sample):
        if d.has('cex'):
            cex = ' '.join(map(lambda s: s.sexpr(), sample))
            print(f'(cex {len(samples)} ({cex}))')
        current.add_instance_constraints(f'{len(samples)}', synths, sample, solver)
        samples.append(sample)

    def synth():
        stat = {}
        if verbose:
            stat['synth_constr'] = str(solver)
        synth_time, model = solver.solve()
        if verbose:
            d('synth_constr', 'synth constr:', solver)
            d('synth_model', 'synth model:', model)
        d('time', f'(synth-time {synth_time / 1e9:.3f})')
        stat['synth_time'] = synth_time
        if model:
            if verbose:
                stat['model'] = str(model)
            prgs = { name: synth.create_prg(model) for name, synth in synths.items() }
            stat['success'] = True
            stat['prgs'] = { name: str(prg) for name, prg in prgs.items() }
            d('prg', f'(prg\n{'\n'.join(prg.sexpr(name, sep='\n\t') for name, prg in prgs.items())})')
            return prgs, stat
        else:
            stat['success'] = False
            d('success', f'(fail)')
            return None, stat

    assert len(clauses) > 0
    current = clauses.pop(0)

    if initial_samples:
        for s in initial_samples:
            add_sample(s)
    else:
        s = current.counterexample_eval.sample_n(1)
        add_sample(s[0])

    stats = []

    with timer() as elapsed:
        done = False
        while not done:
            # call the synthesizer with more counter-examples
            prgs, stat = synth()
            stat['n_samples'] = len(samples)
            stats.append(stat)

            done = True
            if prgs is not None:
                # check if the program is correct
                counterexample, stat['verif'] = current.verify(prgs, d=d, verbose=verbose)
                if counterexample:
                    # we got a counterexample, so add it to the samples
                    add_sample(counterexample)
                    clauses.append(current)
                    current = clauses.pop(0)
                    done = False
                else:
                    for c in clauses:
                        counterexample, _ = c.verify(prgs, d=d, verbose=verbose)
                        if counterexample:
                            clauses.remove(c)
                            clauses.append(current)
                            current = c
                            add_sample(counterexample)
                            done = False
                            break

        return prgs, { 'time': elapsed(), 'stats': stats }, samples