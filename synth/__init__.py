from synth import synth_n, brahma

# register all the synthesizers here
SYNTHS  = synth_n.LenCegis \
        | synth_n.LenFA \
        | brahma.BrahmaExact \
        | brahma.BrahmaIterate \
        | brahma.BrahmaPaper \
        | synth_n.OptCegis \
        | synth_n.DownscaleSynth
