import json
import tyro

from dataclasses import dataclass, field
from sexpdata import loads, Symbol
from pathlib import Path
from egglog.bindings import EGraph
import copy

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

def parse_caviar_term(term):
    op_map = {"+": "Add", "-": "BSub", "*": "Mul", "/": "Div", "%": "Mod", "!": "Not", "&&": "And", "==": "Eq", "!=": "Neq", "<": "S<", "<=": "S<=", ">": "S>",">=": "S>=",  "min": "Min", "max": "Max"}
    sterm = loads(term)
    return parse_sexpr(op_map, sterm)

    exp = []
    for pttrn in data:
        expr_list = loads(pttrn["expression"]["start"])
        exp.append(parse_sexpr(expr_list))
    return exp

def parse_rulegen_term(term):
    op_map = {"+": "Add", "-": "USub", "--": "BSub", "*": "Mul", "~": "Not", "&": "And", "|": "Or", "^": "Xor", "<<": "Lsh", ">>": "Rsh", "==": "Eq", "!=": "Neq", "s<": "S<", "s<=": "S<=", "s>": "S>", "s>=": "S>=", "min": "Min", "max": "Max"}
    sterm = loads(term)
    return parse_sexpr(op_map, sterm)

def parse_random(data):
    exp = []
    for term in data:
        exp.append(parse_rulegen_term(term["term"]))
    return exp

def top_match(lhs, exp, var_ass):
    if isinstance(lhs, OpExpr):
        if not isinstance(exp, OpExpr) or lhs.op != exp.op or len(lhs.args) != len(exp.args):
            return False
        return all(top_match(c_lhs, c_exp, var_ass) for c_lhs, c_exp in zip(lhs.args, exp.args))
    elif isinstance(lhs, Var):
        if lhs.v in var_ass:
            return exp == var_ass[lhs.v]
        var_ass[lhs.v] = exp
        return True
    elif isinstance(lhs, Num):
        return lhs == exp

def rewrite_rhs(rhs, var_ass):
    if isinstance(rhs, OpExpr):
        e = OpExpr(rhs.op, [])
        for arg in rhs.args:
            e.args.append(rewrite_rhs(arg, var_ass))
        return e
    if isinstance(rhs, Var):
        return var_ass[rhs.v]
    return rhs

def top_rewrite(lhs, rhs, exp):
    var_ass = {}
    if not top_match(lhs, exp, var_ass):
        return (False, None)
    rewritten = rewrite_rhs(rhs, var_ass)
    return (True, rewritten)

def exp_rewrite(lhs, rhs, exp):
    (ok, ans) = top_rewrite(lhs, rhs, exp)
    if ok:
        return (True, ans)
    if isinstance(exp, OpExpr):
        for i in range(len(exp.args)):
            (ok, ans) = exp_rewrite(lhs, rhs, exp.args[i])
            if ok:
                exp.args[i] = ans
                return (True, exp)
    return (False, None)

def rulegen_rewrite(exp, rules):
    ok = True
    c_exp = copy.deepcopy(exp)
    while ok:
        ok = False
        for lhs, rhs in rules:
            (rewritten, new_exp) = exp_rewrite(lhs, rhs, c_exp)
            if rewritten:
                ok = True
                c_exp = new_exp
                print(f"{lhs} to {rhs}")
                print(c_exp)
                break
    return c_exp

def egglog_rewrite(prog_header, term):
    prog = prog_header + f"(let term {term})\n"
    prog += "(run 5)\n"
    prog += "(extract term)\n"
    e = EGraph()
    cmds = e.parse_program(prog)
    out = e.run_program(*cmds)
    return str(out[1])

@dataclass(frozen=True)
class Settings:
    folder_path: str = ""
    rule_file: str = ""

    def exec(self):
        prog_header = "(datatype Expr\n(Num i64 :cost 0)\n(Var String :cost 0)\n(Add Expr Expr :cost 1)\n(USub Expr :cost 1)\n(BSub Expr Expr :cost 1)\n(Mul Expr Expr :cost 1)\n(Div Expr Expr :cost 1)\n(Mod Expr Expr :cost 1)\n(Not Expr :cost 1)\n(And Expr Expr :cost 1)\n(Or Expr Expr :cost 1)\n(Xor Expr Expr :cost 1)\n(Lsh Expr Expr :cost 1)\n(Rsh Expr Expr :cost 1)\n(Eq Expr Expr :cost 1)\n(Neq Expr Expr :cost 1)\n(S< Expr Expr :cost 1)\n(S<= Expr Expr :cost 1)\n(S> Expr Expr :cost 1)\n(S>= Expr Expr :cost 1)\n(Min Expr Expr :cost 1)\n(Max Expr Expr :cost 1))\n"
        rules = []
        with open(self.rule_file, "r") as f:
            data = json.load(f)
            for rule in data["eqs"]:
                lhs = parse_rulegen_term(rule["lhs"])
                rhs = parse_rulegen_term(rule["rhs"])
                rules.append((lhs, rhs))
                prog_header += f"(rewrite {lhs.to_rule()} {rhs.to_rule()})\n"

        folder = Path(f"{self.folder_path}")
        for file in folder.rglob("*"):
            if file.suffix == ".json" and "rewritten" not in file.name:
                with open(file, "r") as f:
                    data = json.load(f)
                if isinstance(data, list):
                    exp = []
                    for termset in data:
                        term = termset["expression"]["start"]
                        exp.append(parse_caviar_term(term))
                else:
                    exp = []
                    for termset in data["terms"]:
                        term = termset["term"]
                        exp.append(parse_rulegen_term(term))
                ans = []
                for e in exp:
                    rulegen_e = rulegen_rewrite(e, rules)
                    egg_e = egglog_rewrite(prog_header, e)
                    ans.append({"original": str(e), "original_size": e.get_size(), "rewritten1": str(rulegen_e), "rewritten2": egg_e, "rewritten_size": rulegen_e.get_size(), "smaller": rulegen_e.get_size() < e.get_size()})
                with open(file.with_name(f"{file.stem}_rewritten.json"), "w") as f:
                    json.dump(ans, f, indent=2)

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()