from z3 import *

from synth.spec import Func, Nonterminal, Production

class Bl:
    ty = BoolSort()
    w, x, y, z = Bools('w x y z')
    s0, s1 = Bools('s0 s1')
    i2 = [x, y]
    i3 = i2 + [z]
    i4 = [w] + i3
    ops = [
        Func('not1',    Not(x)),
        Func('nand2',   Not(And(i2))),
        Func('nor2',    Not(Or(i2))),
        Func('and2',    And(i2)),
        Func('or2',     Or(i2)),
        Func('xor2',    Xor(x, y)),

        Func('and3',    And(i3)),
        Func('or3',     Or(i3)),
        Func('nand3',   Not(And(i3))),
        Func('nor3',    Not(Or(i3))),

        Func('nand4',   Not(And(i4))),
        Func('and4',    And(i4)),
        Func('nor4',    Not(Or(i4))),

        Func('mux2',    Or(And(s0, x), And(Not(s0), y)), inputs=[s0, x, y]),
        Func('mux4',    Or([And(Not(s0), Not(s1), w), And([s0, Not(s1), x]), And([Not(s0), s1, y]), And([s0, s1, z])]), inputs=[s0, s1, w, x, y, z]),
        Func('maj3',    Or(And(x, y), And(x, z), And(y, z))),
        Func('eq2',     x == y),
    ]

for op in Bl.ops:
    setattr(Bl, f'{op.name}', op)

class Bv:
    def __init__(self, width):
        self.width = width
        self.ty    = BitVecSort(width)

        x, y = BitVecs('x y', width)
        z = BitVecVal(0, width)
        o = BitVecVal(1, width)
        shift_precond = ULE(y, width)
        div_precond = y != z

        self.simple_ops = [
            Func('neg',  -x),
            Func('not',  ~x),
            Func('and',  x & y),
            Func('or' ,  x | y),
            Func('xor',  x ^ y),
            Func('add',  x + y),
            Func('sub',  x - y),
        ]

        self.shift_ops = [
            Func('shl',  (x << y),   precond=shift_precond),
            Func('lshr', LShR(x, y), precond=shift_precond),
            Func('ashr', x >> y,     precond=shift_precond),
        ]

        self.cmp_ops = [
            Func('uge',  If(UGE(x, y), o, z)),
            Func('ult',  If(ULT(x, y), o, z)),
            Func('sge',  If(x >= y, o, z)),
            Func('slt',  If(x < y, o, z)),
        ]

        self.mul_div = [
            Func('mul',  x * y),
            Func('div',  x / y,      precond=div_precond),
            Func('udiv', UDiv(x, y), precond=div_precond),
            Func('smod', x % y,      precond=div_precond),
            Func('urem', URem(x, y), precond=div_precond),
            Func('srem', SRem(x, y), precond=div_precond),
        ]
        self.ops = self.simple_ops + self.shift_ops + self.cmp_ops + self.mul_div

        for op in self.ops:
            setattr(self, f'{op.name}_', op)

class I:
    ty = IntSort()
    x, y = Ints('x y')
    div_precond = y != 0

    simple_ops = [
        Func('neg', -x),
        Func('add', x + y),
        Func('sub', x - y),
    ]

    cmp_ops = [
        Func('abs', If(x >= 0, x, -x))
    ]

    mul_div = [
        Func('mul', x * y),
        Func('div', x / y, precond=div_precond),
        Func('mod', x % y, precond=div_precond),
    ]

    ops = simple_ops + cmp_ops + mul_div

for op in I.ops:
    setattr(I, f'{op.name}', op)


class R:
    ty = RealSort()
    x, y = Reals('x y')
    div_precond = y != 0

    simple_ops = [
        Func('neg', -x),
        Func('add', x + y),
        Func('sub', x - y),
    ]

    cmp_ops = [
        Func('fabs', If(x >= 0, x, -x))
    ]

    mul_div = [
        Func('mul', x * y),
        Func('div', x / y, precond=div_precond),
    ]

    ops = simple_ops + cmp_ops + mul_div

for op in R.ops:
    setattr(R, f'{op.name}', op)

def nonterminal_from_ops(name: str, parameters: tuple[str], ops: Sequence[Func]) -> Nonterminal:
    sorts = set([ f.out_type for f in ops ]) | set([ ty for f in ops for ty in f.in_types])
    assert len(sorts) == 1
    sort = next(iter(sorts))
    prods = tuple(Production(operands=(name,) * len(f.inputs), op=f) for f in ops)
    return Nonterminal(name=name, sort=sort, parameters=parameters, productions=prods, constants=None)