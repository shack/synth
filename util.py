from z3 import *

def bv_sort(max_value, ctx=None):
    return BitVecSort(len(bin(max_value)) - 2, ctx=ctx)