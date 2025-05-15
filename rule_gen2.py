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

def enum_tree(ops, consts, budget):
    if budget > 0:
        for cons in ops.values():
            arity = cons.__code__.co_argcount
            match arity:
                case 1:
                    for t in enum_tree(ops, consts, budget - 1):
                        yield (cons, t)
                case 2:
                    new_budget = budget - 1
                    for b in range(new_budget + 1):
                        for lhs in enum_tree(ops, consts, b):
                            for rhs in enum_tree(ops, consts, new_budget - b):
                                yield (cons, lhs, rhs)
    else:
        assert budget == 0
        for c in consts:
            yield (c,)
        # yield a variable placeholder
        yield ()


def enum_prg(ops, vars, consts, budget):
    # enumerate all possible trees of a given budget modulo alpha equivalence (i.e. variable renaming)

    def equivalences(n, max_cls):
        # this enumerates all equivalence classes of n variables of at most max_cls classes
        # we use this to assign variables to different leaves of the tree
        def enumerate(partitions, i):
            if i >= n:
                yield partitions
            else:
                for j in range(len(partitions)):
                    nw = partitions[:j] + [partitions[j] + [i]] + partitions[j + 1:]
                    yield from enumerate(nw, i + 1)
                if len(partitions) < max_cls:
                    yield from enumerate(partitions + [[i]], i + 1)
        yield from enumerate([], 0)

    def count_var_leaves(exp):
        return 1 if exp == () else sum(count_var_leaves(c) for c in exp[1:])

    def all_const(exp):
        match exp:
            case (_,):
                return True
            case ():
                return False
            case (_, *args):
                return all(all_const(a) for a in args)

    def subst(t, var_list):
        match t:
            case ():
                return (var_list[0], var_list[1:])
            case (c,):
                return (c, var_list)
            case (cons, *args):
                es = []
                for a in args:
                    e, var_list = subst(a, var_list)
                    es += [ e ]
                return cons(*es), var_list

    for t in enum_tree(ops, consts, budget):
        if all_const(t):
            continue
        n_leaves = count_var_leaves(t)
        # instantiate the leaves with variables
        for eq in equivalences(n_leaves, len(vars)):
            cls = { q: i for i, p in enumerate(eq) for q in p }
            vs = [ vars[cls[i]] for i in range(n_leaves) ]
            yield subst(t, list(vs))[0]


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
        vs = [ BitVec(f'a{i}', self.bitwidth) for i in range(self.vars) ]
        open('rules.txt', 'w').close()
        open('rule_exists.txt', 'w').close()
        minus_one = (1 << self.bitwidth) - 1
        min_int = 1 << (self.bitwidth - 1)
        # consts = [ 0, 1, minus_one, min_int, minus_one ^ min_int ]
        consts = [ ]
        const_map = { BitVecVal(c, self.bitwidth): None for c in consts }
        rules = []
        def rule_exists(exp):
            for lhs, rhs in rules:
                if exp_match(lhs, exp):
                    with open("rule_exists.txt", "a") as f:
                        f.write(f"for\n{exp}\napply\n{lhs} -> {rhs}\n\n")
                    return True
            return False

        def print_stats():
            nonlocal l, stat, synth_time
            print(f'{elapsed() / 1e9:.3f}s', f'{synth_time / 1e9:.3f}s', l, stat)

        synth_time = 0
        with timer() as elapsed:
            for l in range(1, self.length + 1):
                stat = { 'rewrite': 0, 'new': 0, 'fail': 0, 'n_prg': 0 }
                print(f"length: {l}")
                print_stats()
                for lhs in enum_prg(op_dict, vs, const_map, l):
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
                            with open("rules.txt", "a") as f:
                                f.write(f"{lhs} -> {rhs}\n")
                            rules.append((lhs, rhs))
                            print(f'new: {lhs} -> {rhs}')
                        else:
                            stat['fail'] += 1
                    else:
                        stat['rewrite'] += 1
                    if stat['n_prg'] % 100 == 0:
                        print_stats()
            print_stats()

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()