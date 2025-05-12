import tyro

from dataclasses import dataclass
from z3 import *
from synth.spec import Spec, Task, Prg
from synth.oplib import Bv
from synth.synth_n import LenCegis
from synth import synth_n, util

def is_compound(exp):
    return exp.num_args() > 0

def is_var(exp):
    return exp.num_args() == 0 and exp.decl().name()[0].isalpha()

def top_match(lhs, exp, var_ass):
    if is_compound(lhs):
        if not is_compound(exp) or lhs.decl() != exp.decl() or lhs.num_args() != exp.num_args():
            return False
        return all(top_match(c_lhs, c_exp, var_ass) for c_lhs, c_exp in zip(lhs.children(), exp.children()))
    else:
        if is_var(lhs):
            if lhs in var_ass:
                return exp == var_ass[lhs]
            var_ass[lhs] = exp
            return True
        return lhs == exp

def exp_match(lhs, exp):
    if top_match(lhs, exp, {}):
        return True
    return any(exp_match(lhs, c_exp) for c_exp in exp.children())

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
        open('rules.txt', 'w').close()
        open('rule_exists.txt', 'w').close()
        ans = BitVec('ans', self.bitwidth)
        a = []
        const_map = {}
        rules = []
        def rule_exists(exp):
            for lhs, rhs in rules:
                if exp_match(lhs, exp):
                    with open("rule_exists.txt", "a") as f:
                        f.write(f"for\n{exp}\napply\n{lhs} -> {rhs}\n\n")
                    return True
            return False

        for l in range(1, self.length + 1):
            a.append(BitVec(f'a{l * 2 - 2}', self.bitwidth))
            a.append(BitVec(f'a{l * 2 - 1}', self.bitwidth))
            synth = LenCegis(no_const_expr=True, no_semantic_eq=True, size_range=(l, l), init_samples = 10)
            spec = Spec("", BoolVal(True), [ans], a.copy())
            task = Task(spec, ops, const_map=const_map)
            for prg, stats in synth.synth_all(task):
                lhs = prg.prg_to_exp(a, op_dict)
                if not rule_exists(lhs):
                    synth2 = LenCegis(no_const_expr=False, no_semantic_eq=False, size_range=(1, l - 1))
                    prg_spec = Spec("", ans == lhs, [ans], a)
                    prg_task = Task(prg_spec, ops, const_map=const_map)
                    prg2, stats = synth2.synth(prg_task)
                    if prg2 is not None:
                        rhs = prg2.prg_to_exp(a, op_dict)
                        with open("rules.txt", "a") as f:
                            f.write(f"{lhs} -> {rhs}\n")
                        rules.append((lhs, rhs))

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()