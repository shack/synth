from synth.cegis import Spec

import synth_constants_cegis_stage

def synth(spec: Spec, ops, iter_range, n_samples=1, **args):
    synth.synth_constants_cegis_stage.use_cegis = False
    return synth.synth_constants_cegis_stage.synth(spec, ops, iter_range, n_samples, **args)