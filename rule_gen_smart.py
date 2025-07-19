import json
import tyro
import random

from typing import Literal
from dataclasses import dataclass
from z3 import *
from synth.spec import Func, Task
from synth.oplib import Bl, Bv
from synth.synth_n import LenCegis
from synth.util import timer

def is_compound(exp):
    return exp.num_args() > 0

def is_var(exp):
    return exp.num_args() == 0 and str(exp)[0].isalpha() and str(exp) != "True" and str(exp) != "False"

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

def get_bool(vars, length):
    file_name = f"bool-{vars}vars-{length}iters.json"
    ops = {Bl.and2: None,
           Bl.or2: None,
           Bl.xor2: None,
           Bl.not1: None
        }
    op_dict = {
            "not1": lambda x: ~x,
            "and2": lambda x, y: x & y,
            "or2": lambda x, y: x | y,
            "xor2": lambda x, y: x ^ y
        }
    vs = [ Bool(f'a{i}') for i in range(vars) ]
    consts = [True, False]
    irreducible = [[vs[0]] + [BoolVal(c) for c in consts]]
    return (file_name, ops, op_dict, vs, irreducible)

def get_bv(vars, length, bitwidth):
    file_name = f"bv{bitwidth}-{vars}vars-{length}iters.json"
    bv = Bv(bitwidth)
    ops = {bv.neg_: None,
        bv.not_: None,
        bv.and_: None,
        bv.or_: None,
        bv.xor_: None,
        bv.add_: None,
        bv.sub_: None,
        bv.shl_: None,
        bv.lshr_: None,
        bv.mul_: None
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
        "lshr": lambda x, y: LShR(x, y),
        "mul": lambda x, y: x * y,
    }
    vs = [ BitVec(f'a{i}', bitwidth) for i in range(vars) ]
    #minus_one = (1 << self.bitwidth) - 1
    #min_int = 1 << (self.bitwidth - 1)
    #consts = [ 0, 1, minus_one, min_int, minus_one ^ min_int ]
    consts = [0]
    irreducible = [[vs[0]] + [BitVecVal(c, bitwidth) for c in consts]]
    return (file_name, ops, op_dict, vs, irreducible)

def convert_op(op, nop):
    match op:
        case "-":
            return '-' * nop
        case "LShR":
            return ">>"
        case "And":
            return "&"
        case "Or":
            return "|"
        case "Xor":
            return "^"
        case "Not":
            return "~"
        case _:
            return op

def get_val(mode, bitwidth):
    match mode:
        case "bool":
            return BoolVal(random.choice([True, False]))
        case "bv":
            return BitVecVal(random.randrange(1<<bitwidth), bitwidth)

@dataclass(frozen=True)
class Settings:
    mode: Literal["bool", "bv"] = "bv"
    """The theory."""

    bitwidth: int = 4
    """The bitwidth, in case of bv."""

    length: int = 2
    """The maximum length allowed."""

    vars: int = 3
    """The number of variables allowed."""

    norm: bool = True
    """Whether to find equivalence classes for irreducible terms."""

    assignments: int = 10
    """Number of random assignments to try before invoking Z3."""

    def exec(self):
        rules = []
        open('rules_smart.txt', 'w').close()
        open('rule_exists_smart.txt', 'w').close()
        open('irreducible_smart.txt', 'w').close()
        match self.mode:
            case "bool":
                file_name, ops, op_dict, vs, irreducible = get_bool(self.vars, self.length)
            case "bv":
                file_name, ops, op_dict, vs, irreducible = get_bv(self.vars, self.length, self.bitwidth)

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
                for lhs in enum_irreducible(op_dict, irreducible, l, vs):
                    stat['n_prg'] += 1
                    if not rule_exists(lhs):
                        synth2 = LenCegis(size_range=(0, l - 1))
                        prg_spec = Func("", lhs, inputs=vs)
                        prg_task = Task(prg_spec, ops, const_map=None)
                        prg2, stats = synth2.synth(prg_task)
                        synth_time += stats['time']
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

            def write_sexpr(exp):
                if is_var(exp):
                    return f"?{exp}"
                if is_compound(exp):
                    operator = convert_op(str(exp.decl()), len(exp.children()))
                    return f"({operator} " + ' '.join(f"{write_sexpr(c)}" for c in exp.children()) + ')'
                return f"{exp}"

            json_dict = {"time": round(elapsed() / 1e9, 3),
                         "eqs": []}
            for (lhs, rhs) in rules:
                rule_dict = {"lhs": write_sexpr(lhs),
                             "rhs": write_sexpr(rhs),
                             "bidirectional": True}
                json_dict["eqs"].append(rule_dict)
            with open(f"results/rule_gen/{file_name}", "w") as f:
                json.dump(json_dict, f, indent=2)

            if not self.norm:
                return
            stat = { 'classes': 0, 'equivalent': 0, 'n_prg': 0 }
            classes = {}
            def has_equivalent(exp):
                def get_assignment():
                    return [get_val(self.mode, self.bitwidth) for _ in range(0, self.vars)]
                def check_eq(exp, repr):
                    for i in range(1, self.assignments):
                        assignment = get_assignment()
                        subt = list(zip(vs, assignment))
                        exp_simpl = simplify(substitute(exp, *subt))
                        repr_simpl = simplify(substitute(repr, *subt))
                        exp_val = exp_simpl.as_long() if self.mode == "bv" else is_true(exp_simpl)
                        repr_val = repr_simpl.as_long() if self.mode == "bv" else is_true(repr_simpl)
                        if exp_val != repr_val:
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