#! /ust/bin/env python3

from synth import *

def Arr(name):
    return Array(name, IntSort(), IntSort())

def extract(arr, idx, len):
    res = Arr('res')
    for i in range(len):
        res = Store(res, i, Select(arr, idx + i))
    return res

def insert(to_arr, from_arr, idx, len):
    for i in range(len):
        to_arr = Store(to_arr, idx + i, Select(from_arr, i))
    return to_arr

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

def gen_shuffle_spec(a, b, move):
    res = K(IntSort(), 0)
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

ops = [
    Op(f.__name__, [ Arr, Arr ], Arr, lambda x: gen_shuffle_spec(x[0], x[1], f)) \
        for f in shuffle_insns
]

ops += [
    Op('insert',  [ Arr, Arr, Int, ], Arr, lambda x: insert(x[0], x[1], x[2], 8)),
    Op('extract', [ Arr, Int ], Arr, lambda x: extract(x[0], x[1], 8)),
    Const(Int),
    Const(Int),
    Const(Int),
    Const(Int),
]

def transpose(mat, n_rows, n_cols):
    res = K(IntSort(), 0)
    for r in range(n_rows):
        for c in range(n_cols):
            res = Store(res, c * n_rows + r, Select(mat, r * n_cols + c))
    return res

spec = Op('transpose', [ Arr ], Arr, lambda x: transpose(x[0], 6, 2))
print(spec)
prg, stats = synth([ spec ], ops, 20, debug=1)
print(prg)


