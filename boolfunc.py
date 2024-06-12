#! /usr/bin/env python3

import importlib

from z3 import *

from cegis import Spec, Func, OpFreq
from oplib import Bl
from test import create_bool_func

def read_pla(file, name='func', outputs=None, debug=0):
    for n, line in enumerate(file):
        line = line.strip()
        if (have_o := line.startswith(".o ")) or line.startswith(".ob "):
            if have_o:
                num_outs = int(line.split()[1])
                names    = [ f'y{i}' for i in range(num_outs) ]
            else:
                names    = line.split()[1:]
                num_outs = len(names)
            if outputs is None:
                outputs = set(range(num_outs))
            else:
                assert all(i < num_outs for i in outputs), \
                           f'output index out of range: {i} >= {num_outs}'
            outs    = [ Bool(names[i]) for i in range(num_outs) ]
            clauses = [ ([], []) for _ in range(num_outs) ]
            continue
        elif line.startswith(".i "):
            num_vars = int(line.split()[1])
            ins      = [ Bool(f'x{i}') for i in range(num_vars) ]
            continue
        elif line.startswith(".ilb "):
            in_names = line.split()[1:]
            num_vars = len(in_names)
            ins      = [ Bool(n) for n in in_names ]
            continue
        elif line.startswith(".e"):
            break
        elif line.startswith(".") or line.startswith('#') or line == "":
            continue

        assert num_vars != -1, "PLA needs to contain number of inputs"

        constraint, result = line.split()

        clause = []
        if debug >= 1 and n % 1000 == 0:
            print(f"reading clause {n}")

        for param, literal in zip(ins, constraint):
            match literal:
                case "-":
                    continue
                case "1":
                    clause.append(param)
                case "0":
                    clause.append(Not(param))
                case _:
                    assert False, "invalid character in constraint"

        for i, literal in enumerate(result):
            if not i in outputs:
                continue
            cl, dl = clauses[i]
            match literal:
                case "0":
                    continue # 0-lines are also often omitted.
                case "1" | "4":
                    cl.append(And(clause))
                case "-" | "2":
                    dl.append(And(clause))
                case _:
                    assert False, "unknown result in clause"

    precond = And([ Not(Or(dl)) \
                    for i, (_, dl) in enumerate(clauses) \
                    if i in outputs ])
    spec    = And([ res == Or(cl) \
                    for i, (res, (cl, _)) in enumerate(zip(outs, clauses)) \
                 if i in outputs ])
    outs = [ o for i, o in enumerate(outs) if i in outputs ]
    return Spec(name, spec, outs, ins, precond=precond)

if __name__ == "__main__":
    avail_ops = { name: op for name, op in vars(Bl).items() if isinstance(op, Func) }
    avail_ops_names = ', '.join(avail_ops.keys())
    default_ops = 'not1,and2,or2,xor2'

    import argparse
    parser = argparse.ArgumentParser(prog="synth_pla")
    parser.add_argument('-d', '--debug', type=int, default=0, help='debug level')
    parser.add_argument('-c', '--const', type=int, default=1, help='max number of constants')
    parser.add_argument('-l', '--minlen', type=int, default=0, help='min program length')
    parser.add_argument('-L', '--maxlen', type=int, default=10, help='max program length')
    parser.add_argument('-e', '--samples', type=int, default=None, help='initial samples')
    parser.add_argument('-p', '--ops',   type=str, default=default_ops, \
                        help=f'comma-separated list of operators ({avail_ops_names})')
    parser.add_argument('-w', '--write', default=False, action='store_true', \
                        help='dump the individual SMT queries to files')
    parser.add_argument('-s', '--stats', default=False, action='store_true', \
                        help='write stats to a JSON file')
    parser.add_argument('-g', '--graph', default=False, action='store_true', \
                        help='write the program graph to a DOT file')
    parser.add_argument('-f', '--file', default=None, action='store', \
                        help='read boolean functions from a file (one per line)')
    parser.add_argument('-a', '--pla', default=None, action='store', \
                        help='read boolean function from a pla file')
    parser.add_argument('-o', '--outs',  type=str, action='store', \
                        help='comma-separated list output variables in pla file to consider')
    parser.add_argument('-y', '--synth',  type=str, action='store', default='synth_fa', \
                        help='module of synthesizer (default: synth_fa)')
    parser.add_argument('functions', nargs=argparse.REMAINDER, \
                        help='boolean function as a hex number (possibly multiple))')
    args = parser.parse_args()

    def debug(level, *a):
        if args.debug >= level:
            print(*a)

    functions = []
    if len(args.functions) > 0:
        functions += [ create_bool_func(f) for f in args.functions ]
    elif not args.file is None:
        with open(args.file, 'r') as f:
            functions += [ create_bool_func(line.strip()) for line in f.readlines() ]
    elif args.pla:
        outputs = set(int(i) for i in args.outs.split(',')) if args.outs else None
        with open(args.pla, 'r') as f:
            functions += [ read_pla(f, name=args.pla, outputs=outputs, debug=args.debug) ]
    else:
        parser.print_help()
        exit(1)

    # select operators
    ops = { avail_ops[name]: OpFreq.MAX for name in args.ops.split(',') if name in avail_ops }
    debug(1, f'using operators:', ', '.join([ str(op) for op in ops ]))

    # get the synthesis function
    m = importlib.import_module(args.synth)
    synth = getattr(m, 'synth')

    next = ''
    for spec in functions:
        func = spec.name
        print(f'{next}{func}:')
        n_samples = args.samples if args.samples else min(32, 2 ** len(spec.inputs))
        prg, stats = synth(spec, ops, range(args.minlen, args.maxlen + 1), \
                           debug=debug, max_const=args.const, \
                           n_samples=n_samples, theory='QF_FD', \
                           output_prefix=f'{func}' if args.write else None)
        print(prg)
        total_time = sum(s['time'] for s in stats)
        print(f'synthesis time: {total_time / 1e9:.3f}s')
        if args.stats:
            import json
            with open(f'{func}.stats.json', 'w') as f:
                json.dump(stats, f, indent=4)
        if prg and args.graph:
            with open(f'{func}.dot', 'w') as f:
                prg.print_graphviz(f)
        next = '\n'
