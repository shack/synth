chips = {
    "74x08": ("and2", 4),
    "74x00": ("nand2", 4),
    "74x32": ("or2", 4),
    "74x02": ("nor2", 4),
    "74x86": ("xor2", 4),
    "74x7266": ("xnor2", 4),
    
    "74x11": ("and3", 3),
    "74x10": ("nand3", 3),
    "74x4075": ("or3", 3),
    "74x27": ("nor3", 3),
    
    "74x21": ("and4", 2),
    "74x20": ("nand4", 2),
    "74x4072": ("or4", 2),
    "74x29": ("nor4", 2),
    
    "74x30": ("nand8", 1),
    "74x4078": ("or8", 1),
    "74x4078": ("nor8", 1),
    
    "74x7001": ("and2", 4),
    "74x132": ("nand2", 4),
    "74x7032": ("or2", 4),
    "74x7002": ("nor2", 4),
    
    "74x13": ("nand4", 2),
    
    "74x09": ("and2", 4),
    "74x03": ("nand2", 4),
    "74x33": ("nor2", 4),
    "74x136": ("xor2", 4),
    "74x266": ("xnor2", 4),
    
    "74x15": ("and3", 3),
    "74x12": ("nand3", 3),
    
    "74x22": ("nand4", 2)
}

def parse_chips(file):
    ops = { }
    with open(file, 'r') as f:
        for n, line in enumerate(f):
            line = line.strip().split()
            if len(line) == 0:
                continue
            chip = line[0]
            chip_count = int(line[1])
            if chip not in chips:
                raise ValueError(f"Unknown chip: line {n + 1}")
            operation = chips[chip][0]
            logic_gate_count = chips[chip][1]
            ops[operation] = ops.get(operation, 0) + chip_count * logic_gate_count
    return ops