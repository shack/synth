from z3 import *
from cegis import Func

class Bl:
    w, x, y, z = Bools('w x y z')
    s0, s1 = Bools('s0 s1')
    i2 = [x, y]
    i3 = i2 + [z]
    i4 = [w] + i3
    not1  = Func('not',     Not(x))          #7404
    nand2 = Func('nand2',   Not(And(i2)))    #7400
    nor2  = Func('nor2',    Not(Or(i2)))     #7402
    and2  = Func('and2',    And(i2))         #7408
    or2   = Func('or2',     Or(i2))          #7432
    xor2  = Func('xor2',    Xor(x, y))       #7486

    and3  = Func('and3',    And(i3))         #7408
    or3   = Func('or3',     Or(i3))          #7432

    nand3 = Func('nand3',   Not(And(i3)))    #7410
    nor3  = Func('nor3',    Not(Or(i3)))     #7427
    and3  = Func('and3',    And(i3))         #7411

    nand4 = Func('nand4',   Not(And(i4)))    #7420
    and4  = Func('and4',    And(i4))         #7421
    nor4  = Func('nor4',    Not(Or(i4)))     #7429

    mux2  = Func('mux2',    Or(And(s0, x), And(Not(s0), y)))
    mux4  = Func('mux4',    Or([And(Not(s0), Not(s1), w), And([s0, Not(s1), x]), And([Not(s0), s1, y]), And([s0, s1, z])]))
    maj3  = Func('maj3',    Or(And(x, y), And(x, z), And(y, z)))
    eq2   = Func('eq2',     x == y)

class Bv:
    def __init__(self, width):
        self.width = width
        self.ty    = BitVecSort(width)

        x, y = BitVecs('x y', width)
        shift_precond = ULE(y, width - 1)
        div_precond = y != 0
        z = BitVecVal(0, width)
        o = BitVecVal(1, width)

        self.ops = [
            Func('neg',  -x),
            Func('not',  ~x),
            Func('and',  x & y),
            Func('or' ,  x | y),
            Func('xor',  x ^ y),
            Func('add',  x + y),
            Func('sub',  x - y),
            Func('mul',  x * y),
            Func('div',  x / y),
            Func('udiv', UDiv(x, y), precond=div_precond),
            Func('smod', x % y,      precond=div_precond),
            Func('urem', URem(x, y), precond=div_precond),
            Func('srem', SRem(x, y), precond=div_precond),
            Func('shl',  (x << y),   precond=shift_precond),
            Func('lshr', LShR(x, y), precond=shift_precond),
            Func('ashr', x >> y,     precond=shift_precond),
            Func('uge',  If(UGE(x, y), o, z)),
            Func('ult',  If(ULT(x, y), o, z)),
            Func('sge',  If(x >= y, o, z)),
            Func('slt',  If(x < y, o, z)),
        ]

        for op in self.ops:
            setattr(self, f'{op.name}_', op)