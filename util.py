from z3 import *

class EnumBase:
    def __init__(self, items, cons):
        assert len(items) == len(cons)
        self.cons = cons
        self.item_to_cons = { i: con for i, con in zip(items, cons) }
        self.cons_to_item = { con: i for i, con in zip(items, cons) }

    def __len__(self):
        return len(self.cons)

class EnumSortEnum(EnumBase):
    def __init__(self, name, items, ctx):
        # TODO: Seems to be broken with contexts
        # self.sort, cons = EnumSort(name, [ str(i) for i in items ], ctx=ctx)
        s = Datatype(name, ctx=ctx)
        for i in items:
            s.declare(str(i))
        self.sort = s.create()
        cons = [ getattr(self.sort, str(i)) for i in items ]
        super().__init__(items, cons)

    def get_from_model_val(self, val):
        return self.cons_to_item[val]

    def add_range_constr(self, solver, var):
        pass

def bv_sort(n, ctx):
    return BitVecSort(len(bin(n)) - 2, ctx=ctx)

class BitVecEnum(EnumBase):
    def __init__(self, name, items, ctx):
        self.sort = bv_sort(len(items), ctx)
        super().__init__(items, [ i for i, _ in enumerate(items) ])

    def get_from_model_val(self, val):
        return self.cons_to_item[val.as_long()]

    def add_range_constr(self, solver, var):
        solver.add(ULT(var, len(self.item_to_cons)))
