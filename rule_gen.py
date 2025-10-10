import json
import tyro
import random

from typing import Literal
from dataclasses import dataclass
from z3 import *
from synth.spec import Func, Task
from synth.oplib import Bl, Bv, Re
from synth.synth_n import LenCegis
from synth.util import timer

def get_bl(vars, length):
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
    #consts = [True, False]
    consts = []
    irreducible = [[vs[0]] + [BoolVal(c) for c in consts]]
    return (file_name, ops, op_dict, vs, irreducible)

def get_bv(vars, length, bitwidth):
    file_name = f"bv{bitwidth}-{vars}vars-{length}iters.json"
    bv = Bv(bitwidth)
    ops = {bv.neg_: None,
        bv.not_: None,
        bv.and_: None,
        bv.or_: None,
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
    consts = []
    irreducible = [[vs[0]] + [BitVecVal(c, bitwidth) for c in consts]]
    return (file_name, ops, op_dict, vs, irreducible)

def get_re(vars, length):
    file_name = f"float-{vars}vars-{length}iters.json"
    ops = {Re.neg: None,
        Re.add: None,
        Re.sub: None,
        Re.fabs: None,
        Re.mul: None
    }
    op_dict = {
        "neg": lambda x: -x,
        "add": lambda x, y: x + y,
        "sub": lambda x, y: x - y,
        "fabs": lambda x: If(x >= 0, x, -x),
        "mul": lambda x, y: x * y,
    }
    vs = [ Real(f'a{i}') for i in range(vars) ]
    #minus_one = (1 << self.bitwidth) - 1
    #min_int = 1 << (self.bitwidth - 1)
    #consts = [ 0, 1, minus_one, min_int, minus_one ^ min_int ]
    #consts = [0, -1, 1, 2, -2, 1/2, -1/2]
    consts = []
    irreducible = [[vs[0]] + [RealVal(c) for c in consts]]
    return (file_name, ops, op_dict, vs, irreducible)

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

def get_vars(exp):
    # returns all unique vars in an exp
    if is_var(exp):
        return {exp}
    if is_compound(exp):
        return {v for exp_ch in exp.children() for v in get_vars(exp_ch)}
    return {}

def merge(cons, lhs, rhs, vars):
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

def enum_terms(ops, subterms, length, vars):
    for cons in ops.values():
        arity = cons.__code__.co_argcount
        if arity == 1:
            for t in subterms[length - 1]:
                yield cons(*[t])
        elif arity == 2:
            for i in range(length):
                for l in subterms[i]:
                    for r in subterms[length - 1 - i]:
                        for ans in merge(cons, l, r, vars):
                            yield ans

def rule_exists(rules, exp):
    for lhs, rhs in rules:
        if top_match(lhs, exp, {}):
            with open("logs/rule_exists.txt", "a") as f:
                f.write(f"for\n{exp}\napply\n{lhs} -> {rhs}\n\n")
            return True
    return False

def write_json(elapsed_time, synth_time, rules, stat, file_name):
    def convert_op(op, children):
        if op == "-":
            return ('-' * len(children), children)
        elif op == "LShR":
            return (">>", children)
        elif op == "And":
            return ("&", children)
        elif op == "Or":
            return ("|", children)
        elif op == "Xor":
            return ("^", children)
        elif op == "Not":
            return ("~", children)
        elif op == "If":
            return ("fabs", [children[1]])
        else:
            return (op, children)

    def write_sexpr(exp):
        if is_var(exp):
            return f"?{exp}"
        if is_compound(exp):
            operator, children = convert_op(str(exp.decl()), exp.children())
            return f"({operator} " + ' '.join(f"{write_sexpr(c)}" for c in children) + ')'
        return f"{exp}"

    json_dict = {"elapsed_time": elapsed_time,
                 "synthesis_time": synth_time,
                 "rule_applies": stat['rewrite'],
                 "irreducible": stat['fail'],
                 "no_rules": stat['new'],
                 "eqs": []}
    for (lhs, rhs) in rules:
        rule_dict = {"lhs": write_sexpr(lhs),
                        "rhs": write_sexpr(rhs),
                        "bidirectional": True}
        json_dict["eqs"].append(rule_dict)
    with open(f"results/rule_gen/{file_name}", "w") as f:
        json.dump(json_dict, f, indent=2)

def get_val(mode, bitwidth):
    if mode == "bl":
            return BoolVal(random.choice([True, False]))
    if mode == "bv":
            return BitVecVal(random.randrange(1<<bitwidth), bitwidth)

@dataclass(frozen=True)
class Settings:
    mode: Literal["bl", "bv", "re"] = "bv"
    """The theory."""

    bitwidth: int = 4
    """The bitwidth, in case of bv."""

    max_length: int = 2
    """The maximum length allowed."""

    vars: int = 3
    """The number of variables allowed."""

    norm: bool = True
    """Whether to find equivalence classes for irreducible terms."""

    assignments: int = 10
    """Number of random assignments to try before invoking Z3."""

    def exec(self):
        rules = []
        open('logs/rules.txt', 'w').close()
        open('logs/rule_exists.txt', 'w').close()
        open('logs/irreducible.txt', 'w').close()
        if self.mode == "bl":
            file_name, ops, op_dict, vs, irreducible = get_bl(self.vars, self.max_length)
        if self.mode == "bv":
            file_name, ops, op_dict, vs, irreducible = get_bv(self.vars, self.max_length, self.bitwidth)
        if self.mode == "re":
            file_name, ops, op_dict, vs, irreducible = get_re(self.vars, self.max_length)

        def print_stats():
            nonlocal length, stat, synth_time
            print(f'Elapsed Time: {elapsed() / 1e9:.3f}s', f'Synthesis Time: {synth_time / 1e9:.3f}s', f'Length: {length}', stat)

        synth_time = 0
        with timer() as elapsed:
            stat = { 'rewrite': 0, 'new': 0, 'fail': 0, 'n_prg': 0 }
            for length in range(1, self.max_length + 1):
                irreducible_l = []
                print(f"Length: {length}")
                print_stats()
                for lhs in enum_terms(op_dict, irreducible, length, vs):
                    stat['n_prg'] += 1
                    if not rule_exists(rules, lhs):
                        synth = LenCegis(size_range=(0, length - 1))
                        prg_spec = Func("", lhs, inputs = list(get_vars(lhs)))
                        prg_task = Task(prg_spec, ops, max_const=0)
                        prg, stats = synth.synth(prg_task)
                        synth_time += stats['time']
                        if prg is not None:
                            rhs = prg.prg_to_exp(list(get_vars(lhs)), op_dict)
                            rules.append((lhs, rhs))
                            with open("logs/rules.txt", "a") as f:
                                f.write(f"{lhs} -> {rhs}\n")
                            print(f'new: {lhs} -> {rhs}')
                            stat['new'] += 1
                        else:
                            irreducible_l.append(lhs)
                            stat['fail'] += 1
                    else:
                        stat['rewrite'] += 1
                    if stat['n_prg'] % 100 == 0:
                        print_stats()
                irreducible.append(irreducible_l)
            print_stats()
            write_json(round(elapsed() / 1e9, 3), round(synth_time / 1e9, 3), rules, stat, file_name)

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

            for length in range(1, self.max_length + 1):
                classes = {}
                for exp in irreducible[length]:
                    stat['n_prg'] += 1
                    if not has_equivalent(exp):
                        print(f"new class: {exp}")
                        classes[exp] = [exp]
                        stat['classes'] += 1
                    if stat['n_prg'] % 100 == 0:
                        print_stats()
                f = open("logs/irreducible.txt", "a")
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