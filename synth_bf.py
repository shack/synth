#! /usr/bin/env python3

from synth import *

if __name__ == "__main__":
    avail_ops = { name: op for name, op in vars(Bl).items() if isinstance(op, Func) }
    avail_ops_names = ', '.join(avail_ops.keys())
    default_ops = 'not1,and2,or2,xor2'

    import argparse
    parser = argparse.ArgumentParser(prog="synth_pla")
    parser.add_argument('-d', '--debug', type=int, default=0, help='debug level')
    parser.add_argument('-m', '--maxlen', type=int, default=10, help='max program length')
    parser.add_argument('-l', '--samples', type=int, default=None, help='initial samples')
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
    parser.add_argument('functions', nargs=argparse.REMAINDER, \
                        help='boolean function as a hex number (possibly multiple))')
    args = parser.parse_args()

    if len(args.functions) > 0:
        functions = args.functions
    elif args.file is not None:
        with open(args.file, 'r') as f:
            functions = [ line.strip() for line in f.readlines() ]
    else:
        parser.print_help()
        exit(1)

    # select operators
    ops = [ avail_ops[name] for name in args.ops.split(',') if name in avail_ops ]
    if args.debug >= 1:
        print(f'using operators:', ', '.join([ str(op) for op in ops ]))

    next = ''
    for func in functions:
        print(f'{next}{func}:')
        spec = create_bool_func(func)
        n_samples = args.samples if args.samples else min(32, 2 ** len(spec.inputs))
        prg, stats = synth(spec, ops, range(args.maxlen), \
                           debug=args.debug, max_const=0, \
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