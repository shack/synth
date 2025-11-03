import random
import argparse
import json

def generate(n_nodes: int, n_inputs: int, operators: list[tuple[str, int]]):
    def recurse(n: int):
        if n == 0:
            input = random.choice(range(n_inputs))
            return f'v{input}'
        else:
            op, arity = random.choice(operators)
            sub = ()
            n = n - 1
            for i in range(arity - 1):
                size = random.choice(range(n + 1))
                sub += (recurse(size), )
                n = n - size
            return (op,) + sub + (recurse(n), )
    return recurse(n_nodes)


parser = argparse.ArgumentParser(description='Generate random terms')
parser.add_argument('-t', '--terms', type=int, required=True, help='number of terms to generate')
parser.add_argument('-n', '--nodes', type=int, required=True, help='number of interior nodes')
parser.add_argument('-i', '--inputs', type=int, required=True, help='number of inputs')
parser.add_argument('-o', '--operators', type=str, required=True, help='operators with their arities (e.g. add:2,sub:2,neg:1)')
args = parser.parse_args()

ops = [ a.split(':') for a in args.operators.split(',') ]
ops = [ (f.strip(), int(a.strip())) for f, a in ops ]

terms = []
for i in range(0, args.terms):
    res = generate(args.nodes, args.inputs, ops)
    res = str(res).replace(',', '').replace(r"'", '')
    terms.append({"term": res})

ans = {"terms": terms}
with open(f"../../terms/random/random-{args.inputs}vars-{args.nodes}iters.json", "w") as f:
    json.dump(ans, f, indent=2)

#python3 termgen.py --nodes 4 --inputs 3 --operators="-:1,~:1,&:2,|:2,^:2,+:2,--:2,<<:2,>>:2,*:2"