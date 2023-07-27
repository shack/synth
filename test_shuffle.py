#! /usr/bin/env python3

from synth import *

b = Array('b', IntSort(), IntSort())

def extract(len):
    res = Array('res', IntSort(), IntSort())
    a   = Array('a', IntSort(), IntSort())
    idx = Int('idx')
    for i in range(len):
        res = Store(res, i, Select(a, idx + i))
    return res

def insert(len):
    res = Array('res', IntSort(), IntSort())
    a   = Array('a', IntSort(), IntSort())
    idx = Int('idx')
    for i in range(len):
        res = Store(res, idx + i, Select(a, i))
    return res

def mm256_unpacklo_ps(a, b):
    return [ (a, 0), (b, 0), (a, 1), (b, 1),
             (a, 4), (b, 4), (a, 5), (b, 5) ]

def mm256_unpackhi_ps(a, b):
    return [ (a, 2), (b, 2), (a, 3), (b, 3),
             (a, 6), (b, 6), (a, 7), (b, 7) ]

def mm256_shuffle_ps_1010(a, b):
    return [ (a, 0), (a, 1), (b, 0), (b, 1),
             (a, 4), (a, 5), (b, 4), (b, 5) ]

def mm256_shuffle_ps_3232(a, b):
    return [ (a, 2), (a, 3), (b, 2), (b, 3),
             (a, 6), (a, 7), (b, 6), (b, 7) ]

def mm256_permute2f123_ps_20(a, b):
    return [ (b, 0), (b, 1), (b, 2), (b, 3),
             (a, 0), (a, 1), (a, 2), (a, 3) ]

def mm256_permute2f123_ps_31(a, b):
    return [ (b, 4), (b, 5), (b, 6), (b, 7),
             (a, 4), (a, 5), (a, 6), (a, 7) ]

def gen_shuffle_spec(move):
    res = Array('res', IntSort(), IntSort())
    a   = Array('a', IntSort(), IntSort())
    b   = Array('b', IntSort(), IntSort())
    for i, c in enumerate(move(a, b)):
        res = Store(res, i, Select(*c))
    return res

shuffle_insns = [
    mm256_unpacklo_ps,
    mm256_unpackhi_ps,
    mm256_shuffle_ps_1010,
    mm256_shuffle_ps_3232,
    mm256_permute2f123_ps_20,
    mm256_permute2f123_ps_31,
]

ops  = [ Func(f.__name__, gen_shuffle_spec(f)) for f in shuffle_insns ]
ops += [
    Func('insert', insert(8)),
    Func('extract', extract(8))
]

def transpose(mat, n_rows, n_cols):
    res = Array('out', IntSort(), IntSort())
    for r in range(n_rows):
        for c in range(n_cols):
            res = Store(res, c * n_rows + r, Select(mat, r * n_cols + c))
    return res

if __name__ == '__main__':
    mat = Array('in',  IntSort(), IntSort())
    res = Array('out', IntSort(), IntSort())
    spec = Spec('transpose', res == transpose(mat, 8, 8), [ res ], [ mat ])
    print(spec)
    prg, stats = synth(spec, ops, 20, debug=1)
    print(prg)


