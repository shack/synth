from cegis import Spec
import synth_constants_cegis_stage

def synth(spec: Spec, ops, iter_range, n_samples=1, downsize=False, **args):
    synth_constants_cegis_stage.use_cegis = True
    synth_constants_cegis_stage.synth(spec, ops, iter_range, n_samples, downsize, **args)