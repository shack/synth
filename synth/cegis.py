from z3 import *

from synth.util import timer, eval_model, no_debug
from synth.spec import Spec

def cegis(spec: Spec, synth, init_samples=[], debug=no_debug):
    d = debug

    samples = init_samples if init_samples else spec.eval.sample_n(1)
    assert len(samples) > 0, 'need at least 1 initial sample'

    # set up the verification constraint
    verif = Solver(ctx=spec.ctx)
    verif.add(spec.precond)
    verif.add(Not(spec.phi))

    i = 0
    stats = []
    while True:
        stat = {}
        stats += [ stat ]
        old_i = i

        for sample in samples:
            if len(sample_str := str(sample)) < 50:
                sample_out = sample_str
            else:
                sample_out = sample_str[:50] + '...'
            d(1, 'sample', i, sample_out)
            i += 1
        samples_str = f'{i - old_i}' if i - old_i > 1 else old_i

        # call the synthesizer with more counter-examples
        prg, synth_stat = synth.synth_with_new_samples(samples)
        stat.update(synth_stat)

        if not prg is None:
            # we got a program, so check if it is correct
            stat['prg'] = str(prg).replace('\n', '; ')
            d(2, 'program:', stat['prg'])

            # push a new verification solver state
            # and add equalities that evaluate the program
            verif.push()
            for c in prg.eval_clauses():
                verif.add(c)

            d(3, 'verif', samples_str, verif)
            with timer() as elapsed:
                res = verif.check()
                verif_time = elapsed()
            stat['verif_time'] = verif_time
            d(2, f'verif time {verif_time / 1e9:.3f}')

            if res == sat:
                # there is a counterexample, reiterate
                m = verif.model()
                samples = [ eval_model(m, spec.inputs) ]
                d(4, 'verification model', m)
                d(4, 'verif sample', samples[0])
                verif.pop()
            else:
                verif.pop()
                # we found no counterexample, the program is therefore correct
                d(1, 'no counter example found')
                return prg, stats
        else:
            d(1, f'synthesis failed')
            return None, stats