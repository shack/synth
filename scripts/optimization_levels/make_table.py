import csv
import sys
import json

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def make_row(filename):
    with open(filename) as f:
        rule_data = json.load(f)

    data = {
        "Domain": rule_data["domain"],
        "# Vars": rule_data["vars"],
        "# Iters": rule_data["iters"],
        "Opt": rule_data["opt_level"],
        "Time (s)": rule_data["elapsed_time"],
        "Synth (s)": rule_data["synthesis_time"],
        "# Rules": rule_data["no_rules"],
        "# Appl": rule_data["rule_applies"],
        "# Irr": rule_data["irreducible"],
        "# Terms": rule_data["no_rules"] + rule_data["rule_applies"] + rule_data["irreducible"]
    }

    return data

if __name__ == '__main__':
    files = sys.argv[1:]

    rows = [make_row(f) for f in files]

    writer = csv.DictWriter(sys.stdout, rows[0].keys())
    writer.writeheader()
    for row in rows:
        row = {k: v for k,v in row.items()}
        writer.writerow(row)

