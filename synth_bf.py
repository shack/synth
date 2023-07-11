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
    parser.add_argument('-p', '--ops',   type=str, default=default_ops, \
                        help=f'comma-separated list of operators ({avail_ops_names})')
    parser.add_argument('-w', '--write', default=False, action='store_true', \
                        help='dump the individual SMT queries to files')
    parser.add_argument('-s', '--stats', default=False, action='store_true', \
                        help='write stats to a JSON file')
    parser.add_argument('-g', '--graph', default=False, action='store_true', \
                        help='write the program graph to a DOT file')
    parser.add_argument('functions', nargs=argparse.REMAINDER, \
                        help='boolean function as a hex number (possibly multiple))')
    args = parser.parse_args()

    if len(args.functions) < 1:
        parser.print_help()
        exit(1)

    for func in args.functions:
        n_bits = len(func) * 4
        bits = bin(int(func, 16))[2:].zfill(n_bits)
        # check if length of bit string is a power of 2
        if not (n_bits & (n_bits - 1)) == 0:
            print('length of function must be a power of 2')
            exit(1)

        n_vars  = int(math.log2(len(bits)))
        vars    = [ Bool(f'x{i}') for i in range(n_vars) ]
        clauses = []
        binary  = lambda i: bin(i)[2:].zfill(n_vars)

        for i, bit in enumerate(bits):
            if bit == '1':
                clauses += [ And([ vars[j] if b == '1' else Not(vars[j]) \
                                for j, b in enumerate(binary(i)) ]) ]

        if args.debug >= 4:
            print(clauses)
        spec = Func(func, Or(clauses))

        # select operators
        ops = [ avail_ops[name] for name in args.ops.split(',') if name in avail_ops ]
        if args.debug >= 1:
            print(f'using operators:', ', '.join([ str(op) for op in ops ]))

        prg, stats = synth(spec, ops, range(args.maxlen), \
                           debug=args.debug, max_const=0, \
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