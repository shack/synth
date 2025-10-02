from z3 import set_option
from synth import synth_n, brahma

# register all the synthesizers here
SYNTHS  = synth_n.LenCegis \
        | synth_n.LenFA \
        | brahma.BrahmaExact \
        | brahma.BrahmaIterate \
        | brahma.BrahmaPaper \
        | brahma.BrahmaMaxLen
        # | synth_n.OptSolver \
        # | synth_n.OptSearch \
        # | synth_n.Downscale

set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)
