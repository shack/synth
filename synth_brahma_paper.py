from z3 import is_bv_sort

from util import no_debug, timer
from cegis import Spec, OpFreq
from oplib import Bv
from synth_brahma import synth_exact

def synth(spec: Spec, ops, size_range, n_samples=1, **args):
    for o in ops:
        assert all(is_bv_sort(i.sort()) for i in o.outputs + o.inputs), \
            'only bit vector operations are supported'
    w = next(iter(ops)).inputs[0].sort().size()
    d = args.get('debug', no_debug)
    bv = Bv(w)
    initial_ops = [
        bv.neg_, bv.not_, bv.and_, bv.or_, bv.xor_,
        bv.add_, bv.sub_, bv.shl_, bv.lshr_, bv.ashr_,
        bv.uge_, bv.ult_,
    ]
    all_stats = []
    use_ops = initial_ops
    for o, n in ops.items():
        if n < OpFreq.MAX:
            cnt = n - 1 if o in initial_ops else n
            for _ in range(cnt):
                use_ops.append(o)
    library = ', '.join(str(o) for o in use_ops)
    d(1, f'library (#{len(use_ops)}):', library)
    with timer() as elapsed:
        prg, stats = synth_exact(spec, use_ops, n_samples, **args)
        all_stats = {
            'library': library,
            'iterations': stats,
            'time': elapsed(),
        }
        return prg, [all_stats]