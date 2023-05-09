from synth_alt import *

def read_pla(pla_string):

    plain_constraints = []

    for line in pla_string.split("\n"):
        line = line.strip()
        if line.startswith(".o "):
            assert line.split(" ")[1] == "1", "only one output bit is currently supported"
            continue
        elif line.startswith(".i "):
            num_vars = int(line.split(" ")[1])
            params = [ get_var(Bool, ('var', i)) for i in range(num_vars) ]
            continue
        elif line.startswith(".") or line == "":
            continue

        assert num_vars != -1, "PLA needs to contain number of inputs"

        constraint, result = line.split(" ")
        if result == "0": continue # 0-lines are also often omitted.
        assert result == "1", "unknown result in clause"

        plain_constraints.append(constraint)

    def wrapper(params):
        clauses = []
        for constraint in plain_constraints:
            clause = []

            for i, literal in enumerate(constraint):
                if literal == "-":
                    continue
                elif literal == "1":
                    clause.append(params[i])
                elif literal == "0":
                    clause.append(Not(params[i]))
                else:
                    assert False, "invalid character in constraint"

            clause = And(clause)
            clauses.append(clause)
        return Or(clauses)
    return num_vars, wrapper

def test_pla(filename):
    with open(filename) as f:
        pla = f.read()

    num_vars, formula = read_pla(pla)

    spec = Op('and2', Bool, vars, formula)

    ops  = [ true0, false0, and2, or2, xor2, not1, id1 ]
    prg = synth_smallest(10, Bool, [ f'var{i}' for i in range(num_vars)], [spec], ops, 0)
    print(prg)

test_pla(sys.argv[1])

