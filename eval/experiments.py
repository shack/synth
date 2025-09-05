from eval.util import SynthRun, Cvc5SygusRun, ComparisonExperiment

hackdel_light = ('hackdel-light', [ f'p{i:02d}' for i in range(1, 19) ])
hackdel_heavy = ('hackdel-heavy', [ f'p{i:02d}' for i in [ 19, 20, 21, 22, 24 ] ])

run_difficult = {
    'op-freq': False,
    'difficulty': 100,
    'const-mode': 'FREE',
}
run_easy = {
    'op-freq': True,
    'difficulty': 0,
    'const-mode': 'COUNT',
}

# hackdel-light (10min timeout, —difficulty 100, —no-op-freq, —set.bit-width 8): len-cegis, brahma-iterate, brahma-paper, brahma-exact
class SynthComparison(ComparisonExperiment):
    def __init__(self, iterations, timeout=10*60, set=hackdel_light):
        set, benches = set

        synths = [
            'len-cegis',
            'brahma-iterate',
            'brahma-paper',
        ]

        self.exp = {
            b: {
                s: [
                    SynthRun(set=set, bench=b, synth=s, solver='z3',
                             iteration=i, timeout=timeout, run_opts=run_difficult)
                    for i in range(iterations)
                ] for s in synths
            } for b in benches
        }

# hackdel-light (timeout ?): downscale from 16, 32, 64 mit const cegis
class Downscale(ComparisonExperiment):
    def __init__(self, iterations, timeout=10*60, set=hackdel_light):
        set, benches = set

        bit_widths = [16, 32, 64]

        self.exp = {
            b: {
                w: [
                    SynthRun(set=set, bench=b, synth='downscale', solver='z3',
                             iteration=i, timeout=timeout,
                             run_opts=run_difficult, set_opts={'bit-width': w})
                    for i in range(iterations)
                ] for w in bit_widths
            } for b in benches
        }

# hackdel-light (timout 10min): len-cegis. different solvers (Yices, etc.) 8-bit
class Solvers(ComparisonExperiment):
    def __init__(self, iterations, timeout=10*60, set=hackdel_light):
        set, benches = set
        solvers = ['z3', 'cvc5', 'yices', 'bitwuzla']

        self.exp = {
            b: {
                s: [
                    SynthRun(set=set, bench=b, synth='len-cegis', solver=s,
                             iteration=i, timeout=timeout,
                             run_opts=run_difficult,
                             )
                    for i in range(iterations)
                ] for s in solvers
            } for b in benches
        }

# SyGuS (10min timeout): len-cegis, CVC5, brahma-iterate, brahma-paper
class SyGuS(ComparisonExperiment):
    def __init__(self, iterations: int, difficulty: int, timeout=10*60):
        assert difficulty in [0, 1, 5]
        sygus_benches = [1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 17, 19, 20]
        benches = [ f'p{i:02d}_d{difficulty}' for i in sygus_benches ]
        self.exp = {
            b: {
                {
                    'len-cegis': [
                        SynthRun(set=set, bench=b, synth='len-cegis', solver='external-z3',
                                iteration=i, timeout=timeout)
                        for i in range(iterations)
                    ],
                    'cvc5': [
                        Cvc5SygusRun(iteration=i, timeout=timeout)
                        for i in range(iterations)
                    ],
                }
            } for b in benches
        }

def experiments(n_runs, light_timeout=10*60):
    return [
        SynthComparison(n_runs, timeout=light_timeout, set=hackdel_light),
        # Downscale      (n_runs, timeout=light_timeout, set=hackdel_light),
        # Solvers        (n_runs, timeout=light_timeout, set=hackdel_light),
        # SyGuS          (n_runs, timeout=light_timeout, difficulty=0),
        # SyGuS          (n_runs, timeout=light_timeout, difficulty=1),
        # SyGuS          (n_runs, timeout=light_timeout, difficulty=5),
    ]

"""
# hackdel-light opt: len/opcost/depth, 8-bit, z3opt vs linsearch
# hackdel-heavy (timeout 6h, 8bit): len-cegis, brahma-exact

# ruler-bool, ruler-bv, herbie (timeout 10min, —difficulty 100, —no-op-freq, 8bit), len-cegis vs brahma-iterate (bei letzterem kommt vermutlich nix vernünftiges).
class Ruler(ComparisonExperiment):
    def __init__(self, iterations=3, timeout=10*60):
        sets = [
            'ruler-bool',
            'ruler-bv',
            'herbie',
        ]

        self.exp = {
            set: {
                'len-cegis': [
                    SynthRun(timeout=timeout, iteration=i, set=set, bench='".*"',
                             run_opts=run_difficult,
                             synth='len-cegis')
                    for i in range(iterations)
                ]
            } for set in sets
        }

# hackdel-heavy (timeout 6h, difficulty 100, —no-op-freq, 8bit): len-cegis, brahma-paper
class Heavy(ComparisonExperiment):
    def __init__(self, iterations, difficulty, timeout=10*60, set=hackdel_heavy):
        set, benches = set

        synths = [
            'len-cegis',
            'brahma-exact',
        ]

        self.exp = {
            b: {
                s: [
                    SynthRun(set=set, bench=b, synth=s, iteration=i,
                             timeout=timeout, run_opts=difficulty)
                    for i in range(iterations)
                ] for s in synths
            } for b in benches
        }
"""
