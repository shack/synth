import tyro

from dataclasses import dataclass
from z3 import *
from synth.spec import Spec, Task, Prg
from synth.oplib import Bv
from synth.synth_n import LenCegis
from synth import synth_n, util

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
        ans = BitVec('ans', self.bitwidth)
        a = []
        synth_len = []
        const_map = {}  #{BitVecVal(0, self.bitwidth): None, BitVecVal(1, self.bitwidth): None}

        for l in range(1, self.length + 1):
            a.append(BitVec(f'a{l * 2 - 2}', self.bitwidth))
            a.append(BitVec(f'a{l * 2 - 1}', self.bitwidth))
            synth = LenCegis(no_const_expr=True, no_semantic_eq=True, size_range=(l, l), init_samples=10)
            spec = Spec("", BoolVal(True), [ans], a.copy())
            task = Task(spec, ops, const_map=const_map)
            synth_len.append(synth.create_synth(task, l))

        for l in range(1, self.length + 1):
            for prg, stats in synth_len[l - 1].synth_all_prgs():
                exp = prg.prg_to_exp(a, op_dict)
                prg_spec = Spec("", ans == exp, [ans], a)
                prg_task = Task(prg_spec, ops, const_map=const_map)
                print("New Set:                          " + str(exp))

                synth = LenCegis(no_const_expr=True, no_semantic_eq=True, size_range=(l, self.length))
                continue
                for prg, stats in synth.synth_all(prg_task):
                    print(str(prg) + "\n")
                    prg_len = len(prg.insns)
                    synth_len[prg_len - 1].exclude_program(prg)

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()
