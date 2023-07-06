#! /usr/bin/env python3

from synth import *

def read_pla(file, outputs=None, debug=0):
    for n, line in enumerate(file):
        line = line.strip()
        if line.startswith(".o "):
            num_outs = int(line.split(" ")[1])
            if outputs is None:
                outputs = set(range(num_outs))
            else:
                assert all(i < num_outs for i in outputs), f'output index out of range: {i} >= {num_outs}'
            outs       = [ Bool(f'y{i}') for i in range(num_outs) ]
            clauses    = [ ([], []) for _ in range(num_outs) ]
            # assert line.split(" ")[1] == "1", "only one output bit is currently supported"
            continue
        elif line.startswith(".i "):
            num_vars = int(line.split(" ")[1])
            params = [ Bool(f'x{i}') for i in range(num_vars) ]
            continue
        elif line.startswith(".") or line == "":
            continue

        assert num_vars != -1, "PLA needs to contain number of inputs"

        constraint, result = line.split(" ")

        clause = []
        if debug >= 1 and n % 1000 == 0:
            print(f"reading clause {n}")

        for i, literal in enumerate(constraint):
            if literal == "-":
                continue
            elif literal == "1":
                clause.append(params[i])
            elif literal == "0":
                clause.append(Not(params[i]))
            else:
                assert False, "invalid character in constraint"

        for i, literal in enumerate(result):
            if not i in outputs:
                continue
            cl, dl = clauses[i]
            if literal == "0":
                continue # 0-lines are also often omitted.
            elif literal == "1":
                cl.append(And(clause))
            elif literal == "-":
                dl.append(And(clause))
            else:
                assert False, "unknown result in clause"

    spec = And([ And(Not(Or(dl)), res == Or(cl)) \
                for res, (cl, dl) in zip(outs, clauses) if len(cl) > 0 ])
    outs = [ o for i, o in enumerate(outs) if i in outputs ]
    return Spec('spec', spec, outs, params)

def get_available_ops():
    return [ op for _, op in vars(Bl).items() if isinstance(op, Func) ]

if __name__ == "__main__":
    avail_ops = { name: op for name, op in vars(Bl).items() if isinstance(op, Func) }
    avail_ops_names = ', '.join(avail_ops.keys())
    default_ops = 'not1,and2,or2,xor2,eq2'

    import argparse
    parser = argparse.ArgumentParser(prog="synth_pla")
    parser.add_argument('-d', '--debug', type=int, default=0, help='debug level')
    parser.add_argument('-m', '--maxlen', type=int, default=10, help='max program length')
    parser.add_argument('-o', '--outs',  type=str, default=None, \
                        help='comma-separated list output variables to consider')
    parser.add_argument('-p', '--ops',   type=str, default=default_ops, \
                        help=f'comma-separated list of operators ({avail_ops_names})')
    parser.add_argument('-s', '--stats', default=False, action='store_true', \
                        help='write stats to a JSON file')
    parser.add_argument('-g', '--graph', default=False, action='store_true', \
                        help='write the program graph to a DOT file')
    parser.add_argument('rest', nargs=argparse.REMAINDER)
    args = parser.parse_args()

    outputs = set(int(i) for i in args.outs.split(',')) if args.outs else None
    filename = args.rest[0]
    with open(filename) as f:
        spec = read_pla(f, outputs=outputs, debug=args.debug)

    # select operators
    ops = [ avail_ops[name] for name in args.ops.split(',') if name in avail_ops ]
    if args.debug >= 1:
        print(f'using operators:', ', '.join([ str(op) for op in ops ]))

    prg, stats = synth(spec, ops, args.maxlen, debug=args.debug, max_const=0)
    print(prg)
    if args.debug >= 1:
        total_time = sum(s['time'] for s in stats)
        print(f'synthesis time: {total_time / 1e9:.3f}s')
    if args.stats:
        import json
        with open(f'{filename}.stats.json', 'w') as f:
            json.dump(stats, f, indent=4)
    if prg and args.graph:
        with open(f'{filename}.dot', 'w') as f:
            prg.print_graphviz(f)



