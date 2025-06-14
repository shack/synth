import tyro
import random

from dataclasses import dataclass
from z3 import *
from synth.spec import Func, Task, Prg
from synth.oplib import Bv
from synth.synth_n import LenCegis, OptCegis
from synth.optimizers import OperatorHaveCosts
from synth import synth_n, util
from synth.util import timer

def is_compound(exp):
    return exp.num_args() > 0

def is_var(exp):
    return exp.num_args() == 0 and str(exp)[0].isalpha()

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

def merge(cons, lhs, rhs, vars):
    def get_vars(exp):
        # returns all unique vars in an exp
        if is_var(exp):
            return {exp}
        if is_compound(exp):
            return {v for exp_ch in exp.children() for v in get_vars(exp_ch)}
        return {}

    def equivalences(lhs_vars, rhs_vars, unused_vars):
        # returns all ways to merge the equivalence classes in lhs and rhs
        if len(rhs_vars) == 0:
            yield {}
        else:
            for i in range(len(lhs_vars)):
                for mapping in equivalences(lhs_vars[:i] + lhs_vars[i + 1:], rhs_vars[1:], unused_vars):
                    yield mapping | {rhs_vars[0]: lhs_vars[i]}
            if len(unused_vars) > 0:
                for mapping in equivalences(lhs_vars, rhs_vars[1:], unused_vars[1:]):
                    yield mapping | {rhs_vars[0]: unused_vars[0]}

    def subst(exp, mapping):
        if is_var(exp):
            return mapping[exp]
        if is_compound(exp):
            op = exp.decl()
            args = [subst(arg, mapping) for arg in exp.children()]
            return op(*args)
        return exp

    lhs_vars = list(get_vars(lhs))
    rhs_vars = list(get_vars(rhs))
    unused_vars = [v for v in vars if v not in lhs_vars]
    for mapping in equivalences(lhs_vars, rhs_vars, unused_vars):
        yield (cons(*[lhs, subst(rhs, mapping)]))

def enum_irreducible(ops, small_prg, l, vars):
    for cons in ops.values():
        arity = cons.__code__.co_argcount
        match arity:
            case 1:
                for t in small_prg[l - 1]:
                    yield cons(*[t])
            case 2:
                for i in range(l):
                    for lhs in small_prg[i]:
                        for rhs in small_prg[l - 1 - i]:
                            for ans in merge(cons, lhs, rhs, vars):
                                yield ans

@dataclass(frozen=True)
class Settings:
    length: int = 3
    """The maximum length allowed."""

    bitwidth: int = 4
    """The bitwidth to use."""

    vars: int = 3
    """The number of variables to use."""

    norm: bool = True
    """Whether to find equivalence classes for irreducible terms"""

    assignments: int = 10
    """Number of random assignments to try before invoking Z3"""

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
           #bv.mul_: None}
        }
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
            #"mul": lambda x, y: x * y,
        }
        op_to_cost = {
            "neg": 0,
            "not": 1,
            "and": 2,
            "or": 3,
            "xor": 4,
            "add": 5,
            "sub": 6,
            "shl": 7,
            "ashr": 8,
            "id": 0
        }
        vs = [ BitVec(f'a{i}', self.bitwidth) for i in range(self.vars) ]
        open('rules_smart.txt', 'w').close()
        open('rule_exists_smart.txt', 'w').close()
        open('irreducible_smart.txt', 'w').close()
        minus_one = (1 << self.bitwidth) - 1
        min_int = 1 << (self.bitwidth - 1)
        #consts = [ 0, 1, minus_one, min_int, minus_one ^ min_int ]
        consts = [ ]
        rules = []
        irreducible = [[vs[0]] + [BitVecVal(c, self.bitwidth) for c in consts]]
        def rule_exists(exp):
            for lhs, rhs in rules:
                if top_match(lhs, exp, {}):
                    with open("rule_exists_smart.txt", "a") as f:
                        f.write(f"for\n{exp}\napply\n{lhs} -> {rhs}\n\n")
                    return True
            return False

        def print_stats():
            nonlocal l, stat, synth_time
            print(f'{elapsed() / 1e9:.3f}s', f'{synth_time / 1e9:.3f}s', l, stat)

        synth_time = 0
        with timer() as elapsed:
            stat = { 'rewrite': 0, 'new': 0, 'fail': 0, 'n_prg': 0 }
            for l in range(1, self.length + 1):
                irreducible_l = []
                print(f"length: {l}")
                print_stats()
                #for lhs in enum_prg(op_dict, vs, const_map, l):
                for lhs in enum_irreducible(op_dict, irreducible, l, vs):
                    stat['n_prg'] += 1
                    if not rule_exists(lhs):
                        synth2 = LenCegis(size_range=(0, l - 1))
                        # prg_spec = Spec("", ans == lhs, [ans], a)
                        prg_spec = Func("", lhs, inputs=vs)
                        prg_task = Task(prg_spec, ops, const_map=None)
                        # print('synth', lhs, end=' ', flush=True)
                        prg2, stats = synth2.synth(prg_task)
                        synth_time += stats['time']
                        # print(prg2)
                        if prg2 is not None:
                            stat['new'] += 1
                            rhs = prg2.prg_to_exp(vs, op_dict)
                            with open("rules_smart.txt", "a") as f:
                                f.write(f"{lhs} -> {rhs}\n")
                            rules.append((lhs, rhs))
                            print(f'new: {lhs} -> {rhs}')
                        else:
                            irreducible_l.append(lhs)
                            stat['fail'] += 1
                    else:
                        stat['rewrite'] += 1
                    if stat['n_prg'] % 100 == 0:
                        print_stats()
                irreducible.append(irreducible_l)
            print_stats()

            if not self.norm:
                return
            stat = { 'classes': 0, 'equivalent': 0, 'n_prg': 0 }
            classes = {}
            def has_equivalent(exp):
                def get_assignment():
                    return [BitVecVal(random.randrange(1<<self.bitwidth), self.bitwidth) for _ in range(0, self.vars)]
                def check_eq(exp, repr):
                    for i in range(1, self.assignments):
                        assignment = get_assignment()
                        subt = list(zip(vs, assignment))
                        exp2 = substitute(exp, *subt)
                        repr2 = substitute(repr, *subt)
                        if simplify(exp2).as_long() != simplify(repr2).as_long():
                            return False
                    s = Solver()
                    s.add(exp != repr)
                    return s.check() == unsat

                for repr in classes.keys():
                    if check_eq(exp, repr):
                        classes[repr].append(exp)
                        stat['equivalent'] += 1
                        return True
                return False

            for l in range(1, self.length + 1):
                classes = {}
                for exp in irreducible[l]:
                    stat['n_prg'] += 1
                    if not has_equivalent(exp):
                        print(f"new class: {exp}")
                        classes[exp] = [exp]
                        stat['classes'] += 1
                    if stat['n_prg'] % 100 == 0:
                        print_stats()
                f = open("irreducible_smart.txt", "a")
                for repr, exps in classes.items():
                    f.write(f"Class of {repr}, size {len(exps)}:\n")
                    for exp in exps:
                        f.write(f"{exp}\n")
                    f.write("\n")
                f.close()
            print_stats()

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()