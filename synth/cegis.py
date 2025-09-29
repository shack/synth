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

        param_subst = list(zip(constr.params, sample))
        out_subst = []

        for name, synth in synths.items():
            for k, (out_vars, args) in enumerate(constr.functions[name]):
                instance_id = f'{len(samples) - 1}_{k}'
                synth.add_constr_instance(instance_id)

                inst_outs, inst_ins = synth.vars_out_in(instance_id)
                inst_args = [ substitute(i, param_subst) for i in args ]

                for var, val in zip(inst_ins, inst_args):
                    solver.add(var == val)

                out_subst += list(zip(out_vars, inst_outs))

        phi = substitute(constr.phi, param_subst)
        phi = substitute(phi, out_subst)
        solver.add(simplify(phi))

    def synth():
        stat = {}
        if options.detailed_stats:
            stat['synth_constraint'] = str(solver)
        synth_time, model = solver.solve()
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