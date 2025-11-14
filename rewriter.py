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

def greedy_rewrite(exp, rules):
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

def get_rules(file):
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
    prog_header = "(datatype Expr\n(Num i64 :cost 0)\n(Var String :cost 0)\n(Add Expr Expr :cost 10000)\n(USub Expr :cost 10000)\n(BSub Expr Expr :cost 10000)\n(Mul Expr Expr :cost 10000)\n(Div Expr Expr :cost 10000)\n(Mod Expr Expr :cost 10000)\n(Not Expr :cost 10000)\n(And Expr Expr :cost 10000)\n(Or Expr Expr :cost 10000)\n(Xor Expr Expr :cost 10000)\n(Lsh Expr Expr :cost 10000)\n(Rsh Expr Expr :cost 10000)\n(Eq Expr Expr :cost 10000)\n(Neq Expr Expr :cost 10000)\n(S< Expr Expr :cost 10000)\n(S<= Expr Expr :cost 10000)\n(S> Expr Expr :cost 10000)\n(S>= Expr Expr :cost 10000)\n(Min Expr Expr :cost 10000)\n(Max Expr Expr :cost 10000))\n"

    for lhs, rhs in rules:
        prog_header += f"(rewrite {lhs.to_rule()} {rhs.to_rule()})\n"
    return prog_header

def parse_terms(term_file):
    terms = []
    with open(term_file, "r") as f:
        data = json.load(f)
        if isinstance(data, list):
            for termset in data:
                term = termset["expression"]["start"]
                terms.append(parse_caviar_term(term))
        else:
            for termset in data["terms"]:
                term = termset["term"]
                terms.append(parse_rulegen_term(term))
    return terms

def rewrite(term, use_rulegen, use_egg, rulegen_rules, ruler_rules, rulegen_header, ruler_header):
    if use_rulegen:
        rules = rulegen_rules
        header = rulegen_header
    else:
        rules = ruler_rules
        header = ruler_header

    if use_egg:
        rew_term, rew_size = egglog_rewrite(header, term)
        rew_size = rew_size // 10000
    else:
        aux_term = greedy_rewrite(term, rules)
        rew_term = str(aux_term)
        rew_size = aux_term.get_size()
    return rew_term, rew_size

def get_name(use_rulegen, use_egg):
    name = ""
    if use_rulegen:
        name += "RuleGen_"
    else:
        name += "Ruler_"
    if use_egg:
        name += "Egglog"
    else:
        name += "Greedy"
    return name

@dataclass(frozen=True)
class Settings:
    file: str = "terms/random/random-3vars-100iters.json"
    """Term file."""

    rulegen: str = "results/rule_gen/bv4-3vars-3iters-irr-enum-no-comp.json"
    """RuleGen rule file."""

    ruler: str = "results/ruler/bv4-3vars-3iters.json"
    """Ruler rule file."""

    set1_rulegen: bool = True
    """Use rulegen for first rule set"""

    set1_egg: bool = False
    """Use equality saturation for first rule set."""

    set2_rulegen: bool = False
    """Use rulegen for second rule set"""

    set2_egg: bool = True
    """Use equality saturation for second rule set."""

    def exec(self):
        rulegen_rules = get_rules(self.rulegen)
        ruler_rules = get_rules(self.ruler)

        rulegen_header = build_egglog_header(rulegen_rules)
        ruler_header = build_egglog_header(ruler_rules)

        output_file = f"{self.file[:-5]}-"
        set1_name = get_name(self.set1_rulegen, self.set1_egg)
        set2_name = get_name(self.set2_rulegen, self.set2_egg)
        output_file += f"{set1_name}-{set2_name}"
        output_file += ".json"

        terms = parse_terms(self.file)
        rewritten_terms = []

        ind = 0
        set1_time = 0.0
        set2_time = 0.0
        for term in terms:
            print(ind)
            ind += 1

            start_time = time.perf_counter()
            set1_term, set1_size = rewrite(term, self.set1_rulegen, self.set1_egg, rulegen_rules, ruler_rules, rulegen_header, ruler_header)
            end_time = time.perf_counter()
            set1_time += end_time - start_time

            start_time = time.perf_counter()
            set2_term, set2_size = rewrite(term, self.set2_rulegen, self.set2_egg, rulegen_rules, ruler_rules, rulegen_header, ruler_header)
            end_time = time.perf_counter()
            set2_time += end_time - start_time

            rewritten_terms.append({"original": str(term), "set1": set1_term, "set2": set2_term, "original_size": term.get_size(), "set1_size": set1_size, "set2_size": set2_size, "smaller": set1_size < set2_size})

        ans = {
            "term_file": self.file,
            "rulegen_file": self.rulegen,
            "ruler_file": self.ruler,
            "set1": set1_name,
            "set2": set2_name,
            "set1_time": f"{set1_time:.3f}",
            "set2_time": f"{set2_time:.3f}",
            "terms": rewritten_terms,
        }
        with open(output_file, "w") as f:
            json.dump(ans, f, indent=2)

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()