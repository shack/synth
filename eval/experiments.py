import itertools
import glob

from eval.util import Cvc5SygusRun, DownscaleRun, SygusRun, SynthRun, Cvc5SygusBitVecRun, ComparisonExperiment

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
                    DownscaleRun(set=set, bench=b, synth='downscale', solver='z3',
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

class OptFlags(ComparisonExperiment):
    def __init__(self, iterations: int, timeout=10*60, set=hackdel_light):
        set, benches = set

        flags = {
            'd': 'opt-no-dead-code',
            'e': 'opt-cse',
            'c': 'opt-const',
            'o': 'opt-commutative',
            'r': 'opt-insn-order',
        }

        # for c in itertools.product(['--', '--no-'], repeat=len(opts)):
        self.exp = {
            b: {
                c: [
                    SynthRun(bench=b, set=set, synth='len-cegis', solver='z3',
                             iteration=i, timeout=timeout,
                             tag=''.join(k if v else '-' for k, v in zip(flags.keys(), c)),
                             run_opts=run_difficult,
                             syn_opts=({
                                 o: v for o, v in zip(flags.values(), c)
                             }))
                    for i in range(iterations)
                ] for c in itertools.product([True, False], repeat=len(flags))
            } for b in benches
        }


# SyGuS (10min timeout): len-cegis, CVC5, brahma-iterate, brahma-paper
class SyGuSBitVec(ComparisonExperiment):
    def __init__(self, iterations: int, difficulty: int, timeout=10*60):
        assert difficulty in [0, 1, 5]
        benches = [1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 17, 19, 20]
        self.exp = {
            b: {
                'len-cegis': [
                    SynthRun(set='hackdel-sygus', bench=f'p{b:02d}_d{difficulty}',
                             synth='len-cegis', solver='z3',
                             iteration=i, timeout=timeout)
                    for i in range(iterations)
                ],
                'cvc5': [
                    Cvc5SygusBitVecRun(base_dir='resources/sygus', bench=b,
                                       difficulty=difficulty,
                                       iteration=i, timeout=timeout)
                    for i in range(iterations)
                ],
            } for b in benches
        }

class SyGuS(ComparisonExperiment):
    def __init__(self, iterations: int, timeout=10*60):
        benches = glob.glob(f'resources/sygus/*.sl')
        self.exp = {
            b: {
                'len-cegis': [
                    SygusRun(bench=b, iteration=i, timeout=timeout)
                    for i in range(iterations)
                ],
                'cvc5': [
                    Cvc5SygusRun(bench=b, iteration=i, timeout=timeout)
                    for i in range(iterations)
                ],
            } for b in benches
        }

# ruler-bool, ruler-bv, herbie (timeout 10min, —difficulty 100, —no-op-freq, 8bit), len-cegis vs brahma-iterate
class RulerDifficult(ComparisonExperiment):
    def __init__(self, iterations=3, timeout=10*60):
        sets = {
            'ruler-bool': 'resources/rulesets/ruler/bool-3vars-3iters.json',
            'ruler-bit-vec': 'resources/rulesets/ruler/bv4-3vars-3iters.json',
            'herbie': 'resources/rulesets/ruler/herbie.txt',
        }

        difficult = run_difficult | { 'exclude': r'".*\*.*"' }
        bench = r'".*"'

        self.exp = {
            set: {
                'len-cegis': [
                    SynthRun(timeout=timeout,
                             iteration=i,
                             set=set,
                             bench=bench,
                             synth='len-cegis',
                             solver='z3',
                             run_opts=difficult,
                             set_opts={ 'file': file })
                    for i in range(iterations)
                ],
                'brahma-max-len': [
                    SynthRun(timeout=timeout,
                             iteration=i,
                             set=set,
                             bench=bench,
                             synth='brahma-max-len',
                             solver='z3',
                             run_opts=difficult,
                             syn_opts={ 'max-len': 3 },
                             set_opts={ 'file': file })
                    for i in range(iterations)
                ],
                'brahma-iterate': [
                    SynthRun(timeout=timeout,
                             iteration=i,
                             set=set,
                             bench=bench,
                             synth='brahma-iterate',
                             solver='z3',
                             run_opts=difficult,
                             set_opts={ 'file': file })
                    for i in range(iterations)
                ]
            } for set, file in sets.items()
        }

class RulerExact(ComparisonExperiment):
    def __init__(self, iterations=3, timeout=10*60):
        sets = {
            'ruler-bool': 'resources/rulesets/ruler/bool-3vars-3iters.json',
            'ruler-bit-vec': 'resources/rulesets/ruler/bv4-3vars-3iters.json',
            'herbie': 'resources/rulesets/ruler/herbie.txt',
        }

        run_opts = run_easy | { 'exclude': r'".*\*.*"', 'const-mode': 'FREE' }
        bench = r'".*"'

        self.exp = {
            set: {
                'len-cegis': [
                    SynthRun(timeout=timeout,
                             iteration=i,
                             set=set,
                             bench=bench,
                             synth='len-cegis',
                             solver='z3',
                             run_opts=run_opts,
                             set_opts={ 'file': file },
                             syn_opts={ 'exact': True })
                    for i in range(iterations)
                ],
                'brahma-exact': [
                    SynthRun(timeout=timeout,
                             iteration=i,
                             set=set,
                             bench=bench,
                             synth='brahma-exact',
                             solver='z3',
                             run_opts=run_opts,
                             set_opts={ 'file': file })
                    for i in range(iterations)
                ],
            } for set, file in sets.items()
        }

# hackdel-heavy (timeout 6h, 8bit): len-cegis, brahma-exact
class Heavy(ComparisonExperiment):
    def __init__(self, iterations, difficult: bool, timeout, set=hackdel_heavy):
        set, benches = set

        synths = {
            'len-cegis': { 'exact': not difficult },
            'brahma-paper': {}
        }

        self.exp = {
            b: {
                s: [
                    SynthRun(set=set,
                             bench=b,
                             synth=s,
                             solver='z3',
                             iteration=i,
                             timeout=timeout,
                             run_opts=run_difficult if difficult else run_easy,
                             syn_opts=opts)
                    for i in range(iterations)
                ] for s, opts in synths.items()
            } for b in benches
        }

def experiments(n_runs, light_timeout=10*60):
    return [
        SynthComparison(n_runs, timeout=light_timeout, set=hackdel_light),
        Downscale      (n_runs, timeout=light_timeout, set=hackdel_light),
        Solvers        (n_runs, timeout=light_timeout, set=hackdel_light),
        SyGuSBitVec    (n_runs, timeout=light_timeout, difficulty=0),
        SyGuSBitVec    (n_runs, timeout=light_timeout, difficulty=1),
        SyGuSBitVec    (n_runs, timeout=light_timeout, difficulty=5),
        OptFlags       (n_runs, timeout=30*60),
        RulerDifficult (n_runs, timeout=30*60),
        RulerExact     (n_runs, timeout=30*60),
        Heavy          (1, timeout=6*60*60, difficult=True),
        Heavy          (1, timeout=6*60*60, difficult=False),
        SyGuS          (n_runs, timeout=1*60),
        SyGuS          (n_runs, timeout=10*60),
    ]