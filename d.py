import json
import tyro

from dataclasses import dataclass, field
from sexpdata import loads, Symbol
from pathlib import Path
from egglog.bindings import EGraph
import copy
import time

@dataclass
class Expr:
    def get_size(self):
        pass

    def __str__(self):
        pass

    def to_rule(self):
        pass

@dataclass
class Num(Expr):
    v: int

    def get_size(self):
        return 0

    def __str__(self):
        return f"(Num {self.v})"

    def to_rule(self):
        return f"{self.v}"

@dataclass
class Var(Expr):
    v: str

    def get_size(self):
        return 0

    def __str__(self):
        return f"(Var \"{self.v}\")"

    def to_rule(self):
        return f"{self.v}"

@dataclass
class OpExpr(Expr):
    op: str
    args: list[Expr] = field(default_factory=list)

    def get_size(self):
        return 1 + sum(arg.get_size() for arg in self.args)

    def __str__(self):
        return "(" + self.op + "".join(f" {arg}" for arg in self.args) + ")"

    def to_rule(self):
        return "(" + self.op + "".join(f" {arg.to_rule()}" for arg in self.args) + ")"

def parse_sexpr(op_map, expr_list):
    if isinstance(expr_list, list):
        e = OpExpr(op_map[str(expr_list[0])], [])
        for arg in expr_list[1:]:
            e.args.append(parse_sexpr(op_map, arg))
        return e
    else:
        if isinstance(expr_list, Symbol):
            return Var(str(expr_list))
        else:
            return Num(expr_list)

def parse_rulegen_term(term):
    op_map = {"+": "Add", "-": "USub", "--": "BSub", "*": "Mul", "~": "Not", "&": "And", "|": "Or", "^": "Xor", "<<": "Lsh", ">>": "Rsh"}
    sterm = loads(term)
    return parse_sexpr(op_map, sterm)

def get_rules(file):
    def get_size(term):
        if isinstance(term, OpExpr):
            return 1 + sum(get_size(child) for child in term.args)
        return 0
    rules = []
    with open(file, "r") as f:
        data = json.load(f)
        for rule in data["eqs"]:
            lhs = parse_rulegen_term(rule["lhs"])
            rhs = parse_rulegen_term(rule["rhs"])
            if get_size(lhs) != 0:
                rules.append((lhs, rhs))
                if rule["bidirectional"] and get_size(rhs) != 0:
                    rules.append((rhs, lhs))
            else:
                rules.append((rhs, lhs))
    return rules

def build_egglog_header(rules):
    prog_header = "(datatype Expr\n(Num i64 :cost 0)\n(Var String :cost 0)\n(Add Expr Expr :cost 10000)\n(USub Expr :cost 10000)\n(BSub Expr Expr :cost 10000)\n(Mul Expr Expr :cost 10000)\n(Div Expr Expr :cost 10000)\n(Mod Expr Expr :cost 10000)\n(Not Expr :cost 10000)\n(And Expr Expr :cost 10000)\n(Or Expr Expr :cost 10000)\n(Xor Expr Expr :cost 10000)\n(Lsh Expr Expr :cost 10000)\n(Rsh Expr Expr :cost 10000))\n"

    for lhs, rhs in rules:
        prog_header += f"(rewrite {lhs.to_rule()} {rhs.to_rule()})\n"
    return prog_header

def prove_rule(prog_header, lhs, rhs):
    prog = prog_header
    prog += f"(let lhs {lhs})\n"
    prog += f"(let rhs {rhs})\n"
    prog += "(run 4)\n"
    prog += f"(check (= lhs rhs))\n"
    e = EGraph()
    cmds = e.parse_program(prog)
    try:
        e.run_program(*cmds)
        return True
    except:
        return False

@dataclass(frozen=True)
class Settings:
    domain: str = "bv4"

    vars: int = 3

    iters: int = 2

    def exec(self):
        rulegen = f"results/rule_gen/{self.domain}-{self.vars}vars-{self.iters}iters-irr-enum-norm.json"
        ruler = f"results/ruler/{self.domain}-{self.vars}vars-{self.iters}iters.json"
        rulegen_rules = get_rules(rulegen)
        ruler_rules = get_rules(ruler)

        rulegen_header = build_egglog_header(rulegen_rules)
        ruler_header = build_egglog_header(ruler_rules)

        rulegen_provability = []
        rulegen_provable = 0
        rulegen_total = len(rulegen_rules)
        for rule in rulegen_rules:
            lhs, rhs = rule
            ruler_can_prove = prove_rule(ruler_header, lhs, rhs)
            if ruler_can_prove:
                rulegen_provable += 1
            rulegen_provability.append({
                "lhs": str(lhs),
                "rhs": str(rhs),
                "ruler_can_prove": ruler_can_prove
            })

        ruler_provability = []
        ruler_provable = 0
        ruler_total = len(ruler_rules)
        for rule in ruler_rules:
            lhs, rhs = rule
            rulegen_can_prove = prove_rule(rulegen_header, lhs, rhs)
            if rulegen_can_prove:
                ruler_provable += 1
            ruler_provability.append({
                "lhs": str(lhs),
                "rhs": str(rhs),
                "rulegen_can_prove": rulegen_can_prove
            })

        ans = {
            "rulegen_file": rulegen,
            "ruler_file": ruler,
            "rulegen_drv": ruler_provable / ruler_total,
            "ruler_drv": rulegen_provable / rulegen_total,
            "rulegen_rules": rulegen_provability,
            "ruler_rules": ruler_provability
        }

        with open(f"{self.domain}-{self.vars}vars-{self.iters}iters.json", "w") as f:
            json.dump(ans, f, indent=2)

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()