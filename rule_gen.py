import tyro

from dataclasses import dataclass
from z3 import *
from synth.spec import Spec, Task, Prg
from synth.oplib import Bv
from synth.synth_n import _Ctx
from synth.cegis import cegis
from synth import synth_n

def prg_to_spec(prg: Prg, ans: ExprRef, a: list[ExprRef], op_dict):
    var_to_exp = {}
    for in_var in a:
        var_to_exp[str(in_var)] = in_var
        
    x_nr = len(prg.in_vars)
    for insn in prg.insns:
        args = []
        for var in insn[1]:
            if var[0] == True:
                args.append(var[1])
            else:
                args.append(var_to_exp[prg.var_name(var[1])])
        op = str(insn[0])
        var_to_exp[f'x{x_nr}'] = op_dict[op](*args)
        x_nr += 1
    
    output = prg.outputs[0]
    if output[0] == True:
        exp = output[1]
    else:
        exp = var_to_exp[f'x{output[1]}']
    return Spec("", ans == exp, [ans], a)
    
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
           bv.shl_: None,
           bv.ashr_: None,
           bv.mul_: None}
        op_dict = {
            "neg": lambda x: -x,
            "not": lambda x: ~x,
            "and": lambda x, y: x & y,
            "or": lambda x, y: x | y,
            "xor": lambda x, y: x ^ y,
            "add": lambda x, y: x + y,
            "sub": lambda x, y: x - y,
            "shl": lambda x, y: x << y,
            "ashr": lambda x, y: x >> y,
            "mul": lambda x, y: x * y,
        }
        ans = BitVec('ans', self.bitwidth)
        a = []
        synth = synth_n.LenCegis()
        cnt = 1
            
        for len in range(1, self.length + 1):
            for i in range(len * 2 - 2, len * 2):
                a.append(BitVec(f'a{i}', self.bitwidth))
            spec = Spec("", a[0] == a[0], [ans], a)
            task = Task(spec, ops, theory='QF_BV', const_map={z3.BitVecVal(0, 4): 10, z3.BitVecVal(1, 4): 10})
            s = _Ctx(synth, task, len)
            
            prg = cegis(task.spec, s)[0]
            starting_spec = prg_to_spec(prg, ans, a, op_dict)
            starting_task = Task(starting_spec, ops, theory='QF_BV', const_map={z3.BitVecVal(0, 4): 10, z3.BitVecVal(1, 4): 10})
            print("New Set:")
            
            for len2 in range(len, self.length + 1):
                s = _Ctx(synth, starting_task, len2)
                while True:
                    prg = cegis(starting_task.spec, s)[0]
                    if prg is None:
                        break
                    s.add_prg_constraints(prg)
                    print(f"Program no. {cnt}")
                    print(prg)
                    cnt = cnt + 1
                    if cnt > 40:
                        return
                    
            return
    
if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()
    