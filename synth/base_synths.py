from synth import synth_n, objective, brahma

# register all the synthesizers here
BASE_SYNTHS = synth_n.LenCegis \
            | synth_n.LenFA \
            | brahma.BrahmaExact \
            | brahma.BrahmaIterate \
            | brahma.BrahmaPaper \
            | brahma.BrahmaMaxLen \
            | objective.OptSolver \
            | objective.OptSearch
