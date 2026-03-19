from synth import synth_n, tree, objective

# register all the synthesizers here
BASE_SYNTHS = synth_n.LenCegis \
            | synth_n.LenFA \
            | tree.TreeCegis \
            | tree.KBO \
            | objective.OptSolver \
            | objective.OptSearch
