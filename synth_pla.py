#! /usr/bin/env python3

from synth import *

def read_pla(pla_string, debug=0):
    plain_constraints = []

    for line in pla_string.split("\n"):
        line = line.strip()
        if line.startswith(".o "):
            assert line.split(" ")[1] == "1", "only one output bit is currently supported"
            continue
        elif line.startswith(".i "):
            num_vars = int(line.split(" ")[1])
            params = [ Bool(f'i{i}') for i in range(num_vars) ]
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
        for n, constraint in enumerate(plain_constraints):
            clause = []
            if debug >= 1 and n % 1000 == 0:
                print(f"processing clause {n}")

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
    return params, wrapper

def get_available_ops():
    def is_bool_op(op):
        return op.res_ty == BoolT and all([ ty == BoolT for ty in op.opnd_tys ])
    return [ op for name, op in globals().items() \
             if isinstance(op, Op) and is_bool_op(op) ]

if __name__ == "__main__":
    avail_ops = get_available_ops()
    avail_ops_names = ','.join([str(op) for op in avail_ops])

    import argparse
    parser = argparse.ArgumentParser(prog="synth_pla")
    parser.add_argument('-d', '--debug', type=int, default=0, help='debug level')
    parser.add_argument('-p', '--ops',   type=str, default=avail_ops_names, \
                        help='comma-separated list of operators')
    parser.add_argument('-s', '--stats', default=False, action='store_true', \
                        help='write stats to a JSON file')
    parser.add_argument('rest', nargs=argparse.REMAINDER)
    args = parser.parse_args()

    filename = args.rest[0]
    with open(filename) as f:
        pla = f.read()

    params, formula = read_pla(pla)
    spec = Op('spec', [ BoolT ] * len(params), BoolT, formula)
    # lookup operators in the global namespace
    ops = [ globals()[op] for op in args.ops.split(',') if op in globals() ]
    if args.debug >= 1:
        print(f'using operators:', ', '.join([ str(op) for op in ops ]))
    prg, stats = synth([spec], ops, 10, debug=args.debug)
    print(prg)
    if args.stats:
        import json
        with open(f'{filename}.stats.json', 'w') as f:
            json.dump(stats, f, indent=4)


