import tyro

from dataclasses import dataclass
from z3 import *
from synth.spec import Spec, Task, Prg
from synth.oplib import Bv
from synth.synth_n import LenCegis
from synth import synth_n, util

def prg_to_exp(prg: Prg, ans: ExprRef, a: list[ExprRef], op_dict):
    var_to_exp = {str(in_var): in_var for in_var in a}
    for i, (op, opnds) in enumerate(prg.insns):
        x_nr = len(prg.in_vars) + i
        args = []
        for is_const, v in opnds:
            if is_const:
                args.append(v)
            else:
                args.append(var_to_exp[prg.var_name(v)])
        var_to_exp[f'x{x_nr}'] = op_dict[str(op)](*args)

    is_const, v = prg.outputs[0]
    if is_const:
        return v
    else:
        return var_to_exp[f'x{v}']

@dataclass(frozen=True)
class Settings:
    length: int = 3
    """The maximum length allowed."""

    bitwidth: int = 4
    """The bitwidth to use."""

    def exec(self):
        bv = Bv(self.bitwidth)
        ops = {bv.neg_: None,
           bv.not_: None,
           bv.and_: None,
           bv.or_: None,
           bv.xor_: None,
           bv.add_: None,
           bv.sub_: None,
           #bv.shl_: None,
           #bv.ashr_: None,
           bv.mul_: None}
        op_dict = {
            "neg": lambda x: -x,
            "not": lambda x: ~x,
            "and": lambda x, y: x & y,
            "or": lambda x, y: x | y,
            "xor": lambda x, y: x ^ y,
            "add": lambda x, y: x + y,
            "sub": lambda x, y: x - y,
            #"shl": lambda x, y: x << y,
            #"ashr": lambda x, y: x >> y,
            "mul": lambda x, y: x * y,
        }
        ans, e = BitVecs('ans e', self.bitwidth)
        a = []
        constraints = [True]
        const_map = {BitVecVal(0, self.bitwidth): None, BitVecVal(1, self.bitwidth): None}

        for len in range(1, self.length + 1):
            a.append(BitVec(f'a{len * 2 - 2}', self.bitwidth))
            a.append(BitVec(f'a{len * 2 - 1}', self.bitwidth))

            while True:
                spec = Spec("", And(constraints), [ans], a)
                task = Task(spec, ops, const_map=const_map)
                synth = LenCegis(no_const_expr=True, no_semantic_eq=True, size_range=(len, len))
                prg, stats = synth.synth(task)
                if prg is None:
                    break
                exp = prg_to_exp(prg, ans, a, op_dict)
                prg_spec = Spec("", ans == exp, [ans], a)
                prg_task = Task(prg_spec, ops, const_map=const_map)
                print("New Set:                          " + str(exp))

                synth2 = LenCegis(no_const_expr=True, no_semantic_eq=True, size_range=(len, self.length))
                for prg, stats in synth2.synth_all(prg_task):
                    print(str(prg) + "\n")

                constraints.append(Exists([e], And([e == exp, e != ans])))


if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()
