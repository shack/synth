import tyro
import itertools

from dataclasses import dataclass
from z3 import *
from synth.spec import Func, Task, Prg
from synth.oplib import Bv
from synth.synth_n import LenCegis
from synth import synth_n, util
from synth.util import timer

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

def enum_prg(ops, vars, budget):
    if budget > 0:
        for name, cons in ops.items():
            arity = cons.__code__.co_argcount
            match arity:
                case 1:
                    for sub in enum_prg(ops, vars, budget - 1):
                        yield cons(sub)
                case 2:
                    new_budget = budget - 1
                    for b in range(new_budget):
                        for lhs in enum_prg(ops, vars, b):
                            for rhs in enum_prg(ops, vars, new_budget - b):
                                yield cons(lhs, rhs)
    else:
        for v in vars:
            yield v


@dataclass(frozen=True)
class Settings:
    length: int = 4
    """The maximum length allowed."""

    bitwidth: int = 4
    """The bitwidth to use."""

    vars: int = 3
    """The number of variables to use."""

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
        vs = [ BitVec(f'a{i}', self.bitwidth) for i in range(self.vars) ]
        const_map = {}
        rules = []
        def rule_exists(exp):
            for lhs, rhs in rules:
                if exp_match(lhs, exp):
                    with open("rule_exists.txt", "a") as f:
                        f.write(f"for\n{exp}\napply\n{lhs} -> {rhs}\n\n")
                    return True
            return False

        with timer() as elapsed:
            for l in range(1, self.length + 1):
                a = vs[:l]
                stat = { 'rewrite': 0, 'new': 0, 'fail': 0, 'n_prg': 0 }
                print(f'{elapsed() / 1e9:.3f}s', l, stat)
                print(f"length: {l}")
                for lhs in enum_prg(op_dict, a.copy(), l):
                    stat['n_prg'] += 1
                    if not rule_exists(lhs):
                        synth2 = LenCegis(size_range=(0, l - 1))
                        # prg_spec = Spec("", ans == lhs, [ans], a)
                        prg_spec = Func("", lhs, inputs=a)
                        prg_task = Task(prg_spec, ops, const_map=const_map)
                        print('synth', lhs, end=' ', flush=True)
                        prg2, stats = synth2.synth(prg_task)
                        print(prg2)
                        if prg2 is not None:
                            stat['new'] += 1
                            rhs = prg2.prg_to_exp(a, op_dict)
                            with open("rules.txt", "a") as f:
                                f.write(f"{lhs} -> {rhs}\n")
                            rules.append((lhs, rhs))
                            print(f'new: {lhs} -> {rhs}')
                        else:
                            stat['fail'] += 1
                    else:
                        stat['rewrite'] += 1
                    if stat['n_prg'] % 100 == 0:
                        print(f'{elapsed() / 1e9:.3f}s', l, stat)

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()