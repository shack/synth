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

def get_size(term):
    if isinstance(term, OpExpr):
        return 1 + sum(get_size(child) for child in term.args)
    return 0

def top_rewrite(lhs, rhs, exp):
    var_ass = {}
    if not top_match(lhs, exp, var_ass):
        return (False, None)
    rewritten = rewrite_rhs(rhs, var_ass)
    if get_size(rewritten) < get_size(exp):
        return (True, rewritten)
    return (False, None)

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
                break
    return c_exp

def egglog_rewrite(prog_header, term):
    prog = prog_header + f"(let term {term})\n"
    prog += "(run 4)\n"
    prog += "(extract term)\n"
    e = EGraph()
    cmds = e.parse_program(prog)
    out = e.run_program(*cmds)
    print(out[1].cost)
    return (str(out[1]), out[1].cost)

@dataclass(frozen=True)
class Settings:
    file: str = "terms/random/random-3vars-10iters.json"
    rulegen: str = "results/rule_gen/bv4-3vars-3iters-irr-enum-no-comp.json"
    ruler: str = "results/ruler/bv4-3vars-3iters.json"

    def exec(self):
        rulegen_rules = []
        with open(self.rulegen, "r") as f:
            data = json.load(f)
            for rule in data["eqs"]:
                lhs = parse_rulegen_term(rule["lhs"])
                rhs = parse_rulegen_term(rule["rhs"])
                rulegen_rules.append((lhs, rhs))

        prog_header = "(datatype Expr\n(Num i64 :cost 0)\n(Var String :cost 0)\n(Add Expr Expr :cost 10000)\n(USub Expr :cost 10000)\n(BSub Expr Expr :cost 10000)\n(Mul Expr Expr :cost 10000)\n(Div Expr Expr :cost 10000)\n(Mod Expr Expr :cost 10000)\n(Not Expr :cost 10000)\n(And Expr Expr :cost 10000)\n(Or Expr Expr :cost 10000)\n(Xor Expr Expr :cost 10000)\n(Lsh Expr Expr :cost 10000)\n(Rsh Expr Expr :cost 10000)\n(Eq Expr Expr :cost 10000)\n(Neq Expr Expr :cost 10000)\n(S< Expr Expr :cost 10000)\n(S<= Expr Expr :cost 10000)\n(S> Expr Expr :cost 10000)\n(S>= Expr Expr :cost 10000)\n(Min Expr Expr :cost 10000)\n(Max Expr Expr :cost 10000))\n"
        with open(self.ruler, "r") as f:
            data = json.load(f)
            for rule in data["eqs"]:
                lhs = parse_rulegen_term(rule["lhs"])
                rhs = parse_rulegen_term(rule["rhs"])
                if get_size(lhs) != 0:
                    prog_header += f"(rewrite {lhs.to_rule()} {rhs.to_rule()})\n"
                    if rule["bidirectional"] and get_size(rhs) != 0:
                        prog_header += f"(rewrite {rhs.to_rule()} {lhs.to_rule()})\n"
                else:
                    prog_header += f"(rewrite {rhs.to_rule()} {lhs.to_rule()})\n"

        with open(self.file, "r") as f:
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
        ind = 0
        for e in exp:
            print(ind)
            ind += 1
            rulegen_e = rulegen_rewrite(e, rulegen_rules)
            egg_e, egg_size = egglog_rewrite(prog_header, e)
            egg_size = egg_size // 10000
            #egg_e = str(rulegen_e)
            ans.append({"original": str(e), "rule_gen": str(rulegen_e), "egg": egg_e, "original_size": e.get_size(), "rewritten_size": rulegen_e.get_size(), "egg_size": egg_size, "smaller": rulegen_e.get_size() < e.get_size()})
        with open(f"{self.file[:-5]}-rewritten.json", "w") as f:
            json.dump(ans, f, indent=2)

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()