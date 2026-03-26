from z3 import set_option

from synth import downscaling
from synth.base_synths import BASE_SYNTHS

set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

SYNTHS = BASE_SYNTHS | downscaling.Downscale
