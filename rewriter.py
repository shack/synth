import json
import tyro

from dataclasses import dataclass, field
from sexpdata import loads, Symbol
from pathlib import Path
import copy

@dataclass
class Expr:
    def get_size(self):
        pass

    def __str__(self):
        pass

@dataclass
class Num(Expr):
    v: int

    def get_size(self):
        return 0

    def __str__(self):
        return str(self.v)

@dataclass
class Var(Expr):
    v: str

    def get_size(self):
        return 0

    def __str__(self):
        return self.v

@dataclass
class OpExpr(Expr):
    op: str
    args: list[Expr] = field(default_factory=list)

    def get_size(self):
        return 1 + sum(arg.get_size() for arg in self.args)

    def __str__(self):
        return "(" + self.op + "".join(f" {str(arg)}" for arg in self.args) + ")"

def parse_llvm(data):
    def convert_op(op):
        match op:
            case "fmul":
                return "*"
            case "fadd":
                return "+"
            case "fsub":
                return "--"
            case "fdiv":
                return "/"
            case "fneg":
                return "-"

            case "add":
                return "+"
            case "sub":
                return "--"
            case "mul":
                return "*"
            case "sdiv":
                return "/"
            case "udiv":
                return "/"
            case "srem":
                return "%"
            case "urem":
                return "%"
            case "and":
                return "&"
            case "or":
                return "|"
            case "xor":
                return "^"
            case "shl":
                return "<<"
            case "lshr":
                return "lshr"
            case "ashr":
                return ">>"

            case "icmpeq":
                return "=="
            case "icmpne":
                return "!="
            case "icmpult":
                return "u<"
            case "icmpule":
                return "u<="
            case "icmpugt":
                return "u>"
            case "icmpuge":
                return "u>="
            case "icmpslt":
                return "s<"
            case "icmpsle":
                return "s<="
            case "icmpsgt":
                return "s>"
            case "icmpsge":
                return "s>="

            case "fcmpuno":
                return "fcmpuno"
            case "fcmpune":
                return "fcmpune"
            case "fcmpoeq":
                return "fcmpoeq"
            case "fcmpolt":
                return "fcmpolt"
            case "fcmpole":
                return "fcmpole"
            case "fcmpoge":
                return "fcmpoge"
            case "fcmpogt":
                return "fcmpogt"

            case "sitofp":
                return "sitofp"
            case "uitofp":
                return "uitofp"
            case "fptosi":
                return "fptosi"
            case "fptoui":
                return "fptoui"

            case "alloca":
                return "alloca"
            case "getelementptr":
                return "getelementptr"
            case "store":
                return "store"
            case "load":
                return "load"
            case "extractvalue":
                return "extractvalue"
            case "extractelement":
                return "extractelement"

            case "call":
                return "call"
            case "ret":
                return "ret"
            case "br":
                return "br"
            case "select":
                return "select"
            case "switch":
                return "switch"
            case "unreachable":
                return "unreachable"

            case "bitcast":
                return "bitcast"
            case "sext":
                return "sext"
            case "zext":
                return "zext"
            case "trunc":
                return "trunc"
            case "freeze":
                return "freeze"
            case "ptrtoint":
                return "ptrtoint"

            case _:
                raise ValueError(f"unknown op {op}")

    exp = []
    for pttrn in data["pttrns"]:
        inst_ass = {}
        lasti = ""
        for instr_sexp in pttrn["pttrn"]:
            instr = loads(instr_sexp)
            i = str(instr[1])
            lasti = i
            e = OpExpr(convert_op(str(instr[2][0])), [])
            for arg in instr[2][1:]:
                if isinstance(arg, list):
                    match str(arg[0]):
                        case "Var":
                            e.args.append(Var(arg[1]))
                        case "Num":
                            print(str(arg[1]))
                        case "_":
                            raise ValueError(f"unknown argument {str(arg[0])}")
                else:
                    assert str(arg)[0] == "i", f"weird argument {str(arg)}"
                    e.args.append(inst_ass[str(arg)])
            inst_ass[i] = e
        exp.append(inst_ass[lasti])
    return exp

def parse_caviar(data):
    def convert_op(op):
        match op:
            case "*":
                return "*"
            case "+":
                return "+"
            case "-":
                return "--"
            case "/":
                return "/"
            case "&&":
                return "&"
            case "min":     ######################
                return "min"
            case "max":     ######################
                return "max"
            case "==":
                return "=="
            case "<":
                return "s<"
            case "<=":
                return "s<="
            case ">=":
                return "s>="
            case ">":
                return "s>"
            case "%":
                return "%"
            case "!":
                return "~"
            case "!=":
                return "!="
            case _:
                raise ValueError(f"unknown op {op}")

    def parse_sexpr(expr_list):
        if isinstance(expr_list, list):
            e = OpExpr(convert_op(str(expr_list[0])), [])
            for arg in expr_list[1:]:
                e.args.append(parse_sexpr(arg))
            return e
        else:
            if isinstance(expr_list, Symbol):
                return Var(str(expr_list))
            else:
                return Num(expr_list)

    exp = []
    for pttrn in data:
        expr_list = loads(pttrn["expression"]["start"])
        exp.append(parse_sexpr(expr_list))
    return exp

def parse_rule(data):
    def parse_sexpr(expr_list):
        if isinstance(expr_list, list):
            e = OpExpr(str(expr_list[0]), [])
            for arg in expr_list[1:]:
                e.args.append(parse_sexpr(arg))
            return e
        else:
            if isinstance(expr_list, Symbol):
                return Var(str(expr_list))
            else:
                return Num(expr_list)

    return parse_sexpr(loads(data))

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

def rewrite(exp, rules):
    ok = True
    #exp = OpExpr("&", [Var("?a0"), OpExpr("|", [OpExpr("&", [Var("?a2"), Var("?a0")]), Var("?a1")])])
    #rules = [(OpExpr("&&", [Var("?a0"), OpExpr("||", [OpExpr("&&", [Var("?a2"), Var("?a0")]), Var("?a1")])]),
    #    OpExpr("&&", [Var("?a0"), OpExpr("||", [Var("?a1"), Var("?a2")])])
    #)]
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

@dataclass(frozen=True)
class Settings:
    folder_path: str = ""
    rule_file: str = ""

    def exec(self):
        rules = []
        with open(self.rule_file, "r") as f:
            data = json.load(f)
            for rule in data["eqs"]:
                rules.append((parse_rule(rule["lhs"]), parse_rule(rule["rhs"])))

        folder = Path(f"{self.folder_path}")
        for file in folder.rglob("*"):
            if file.suffix == ".json" and "rewritten" not in file.name:
                print(file.name)
                with open(file, "r") as f:
                    data = json.load(f)
                if isinstance(data, list):
                    exp = parse_caviar(data)
                else:
                    exp = parse_llvm(data)
                ans = []
                for e in exp:
                    print(e)
                    rew_e = rewrite(e, rules)
                    ans.append({"original": str(e), "original_size": e.get_size(), "rewritten": str(rew_e), "rewritten_size": rew_e.get_size(), "smaller": rew_e.get_size() < e.get_size()})
                with open(file.with_name(f"{file.stem}_rewritten.json"), "w") as f:
                    json.dump(ans, f, indent=2)

if __name__ == "__main__":
    args = tyro.cli(Settings)
    args.exec()