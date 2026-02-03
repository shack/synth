from synth import synth_n, objective

# register all the synthesizers here
BASE_SYNTHS = synth_n.LenCegis \
            | synth_n.LenFA \
            | objective.OptSolver \
            | objective.OptSearch
