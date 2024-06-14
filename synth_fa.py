from functools import lru_cache
from collections import defaultdict

from synth_n import SynthN

from z3 import *

from cegis import Spec, Func, Prg, OpFreq, no_debug, timer
from util import bv_sort

class SynthFA(SynthN):
    def __init__(self, spec: Spec, ops: list[Func], n_insns, **args):
        args['reset_solver'] = True
        self.exist_vars = set()
        super().__init__(spec, ops, n_insns, **args)

    @lru_cache
    def get_var(self, ty, name, instance=None):
        res = super().get_var(ty, name, instance)
        if not instance is None:
            self.exist_vars.add(res)
        return res

    def do_synth(self):
        ins  = [ self.var_input_res(i, 'fa') for i in range(self.n_inputs) ]
        self.exist_vars.difference_update(ins)
        self.add_constr_instance('fa')
        self.add_constr_io_spec('fa', ins)
        s = Solver(ctx=self.ctx)
        s.add(ForAll(ins, Exists(list(self.exist_vars), And([a for a in self.synth]))))

        if self.output_prefix:
            filename = f'{self.output_prefix}_synth.smt2'
            with open(filename, 'w') as f:
                print(s.to_smt2(), file=f)

        stat = {}
        self.d(3, 'synth', s)
        with timer() as elapsed:
            res = s.check()
            synth_time = elapsed()
            stat['synth_stat'] = s.statistics()
            self.d(5, stat['synth_stat'])
            self.d(2, f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = s.model()
            prg = self.create_prg(m)
            self.d(4, 'model: ', m)
            return prg, stat
        else:
            return None, stat

def synth(spec: Spec, ops, iter_range, n_samples=1, **args):
    """Synthesize a program that computes the given function.

    Attributes:
    spec: Specification of the function to be synthesized.
    ops: Collection (set/list) of operations that can be used in the program.
    iter_range: Range of program lengths that are tried.
    n_samples: Number of initial I/O samples to give to the synthesizer.
    args: arguments passed to the synthesizer

    Returns:
    A tuple (prg, stats) where prg is the synthesized program (or None
    if no program has been found) and stats is a list of statistics for each
    iteration of the synthesis loop.
    """

    all_stats = []
    for n_insns in iter_range:
        with timer() as elapsed:
            prg, stats = SynthFA(spec, ops, n_insns, **args).do_synth()
            all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
            if not prg is None:
                return prg, all_stats
    return None, all_stats