from z3 import *
from itertools import combinations as comb

def get_var(ty, args):
    if args in get_var.vars:
        v = get_var.vars[args]
    elif ty:
        v = ty('_'.join(map(str, args)))
        get_var.vars[args] = v
    else:
        assert False
    return v
get_var.vars = {}

class InsnInstance:
    def __init__(self, insn, serial):
        self.insn   = insn
        self.serial = serial
        self.prefix = (insn.name, self.serial)
        
    def ins(self):
        return [ get_var(ty, self.prefix + ('in', i)) for i, ty in enumerate(self.insn.sig.arg_tys) ]

    def ins_with_loc(self):
        return zip(self.ins(), self.insn.ins_loc())

    def out(self):
        return get_var(self.insn.sig.res_ty, self.prefix + ('out',))

    def out_loc(self):
        return self.insn.out_loc()

    def ins_loc(self):
        return self.insn.ins_loc()

class Sig:
    def __init__(self, res_ty, arg_tys):
        self.res_ty  = res_ty
        self.arg_tys = arg_tys

    def arity(self):
        return len(self.arg_tys)

class Template(Sig):
    def __init__(self, name: str, res_ty, arg_tys: list, phi):
        super().__init__(res_ty, arg_tys)
        self.name    = name
        self.phi     = phi 

    def __str__(self):
        return self.name

class Insn:
    def __init__(self, name, sig: Sig):
        self.name  = name
        self.sig   = sig

    def ins_loc(self):
        return [ get_var(Int, (self.name, 'loc', 'in', i)) for i in range(self.sig.arity()) ]

    def out_loc(self):
        return get_var(Int, (self.name, 'loc', 'out'))

class TemplateInsnInstance(InsnInstance):
    def spec(self):
        return self.out() == self.insn.template.phi(self.ins())

class TemplateInsn(Insn):
    def __init__(self, template, name):
        super().__init__(name, template)
        self.template = template

    def instantiate_synth(self, serial):
        return TemplateInsnInstance(self, serial)

    def instantiate_verif(self):
        return self.instantiate_synth('verif')

class SynthInputInstance(InsnInstance):
    def __init__(self, template, serial, value):
        super().__init__(template, serial)
        self.value = value

    def spec(self):
        return self.out() == self.value

class VerifInputInstance(InsnInstance):
    def __init__(self, template):
        super().__init__(template, 'verif')

    def spec(self):
        return True

class InputInsn(Insn):
    def __init__(self, number, ty):
        super().__init__('input' + str(number), Sig(ty, []))
        self.number = number
    
    def instantiate_synth(self, serial, value):
        return SynthInputInstance(self, serial, value)

    def instantiate_verif(self):
        return VerifInputInstance(self)

    def out_loc(self):
        return self.number

class OutputInstance(InsnInstance):
    def __init__(self, insn, serial):
        super().__init__(insn, serial)

    def spec(self):
        return True

class OutputInsn(Insn):
    def __init__(self, arg_tys, position):
        super().__init__('output', Sig(None, arg_tys))
        self.position = position

    def out_loc(self):
        return self.position
    
    def instantiate_synth(self, serial):
        return OutputInstance(self, serial)

    def instantiate_verif(self):
        return self.instantiate_synth('verif')

def add_constr_wfp(solver: Solver, templates: list[Insn]):
    # all "line numbers" of output variables are different
    for lx, ly in comb((c.out_loc() for c in templates), 2):
        solver.add(lx != ly)
    for c in templates:
        # acyclicity: line numbers of uses are lower than line number of definition
        for lx in c.ins_loc():
            solver.add(lx < c.out_loc())
        # output variables range from I to M where I is number of inputs and M is lib size
        solver.add(And(0 <= c.out_loc(), c.out_loc() < len(templates)))
        # input variables range from 0 to lib size
        for l in c.ins_loc():
            solver.add(And([ 0 <= l, l < len(templates)]))

def add_constr_conn(solver, instances):
    for i in instances:
        for o in instances:
            for xi, li in i.ins_with_loc():
                if i != o and o.insn.sig.res_ty:
                    solver.add(Implies(o.out_loc() == li, o.out() == xi))

def add_constr_set_l(solver, templates, out, model):
    for t in templates + [ out ]:
        for i in t.ins_loc():
            solver.add(i == model[i])
    for t in templates:
        solver.add(t.out_loc() == model[t.out_loc()])

def add_constr_spec(solver, specs, out_instance, in_instances, f):
    for o, s in zip(out_instance.ins(), specs):
        solver.add(f(o == s.phi([ i.out() for i in in_instances ])))

def sample(specs: Template):
    s = Solver()
    ins = [ get_var(ty, ('sample', 'in', i)) for i, ty in enumerate(specs[0].arg_tys) ]
    for i, spec in enumerate(specs):
        res = get_var(spec.res_ty, ('sample', 'out', i))
        s.add(res == spec.phi(ins))
    s.check()
    m = s.model()
    return [ m[i] for i in ins ]

class Prg:
    """A straight-line program.

    Attributes:
        n_inputs: Number of parameters of the program.
        v_output: List of variable numbers of the return values.
        insns: Instructions of the program. The list 
            consists of pairs. Each pair contains the
            instruction template of the instruction and
            the variable numbers of the operands.
    """
    def __init__(self, n_inputs, v_output, insns):
        self.n_inputs = n_inputs
        self.v_output = v_output
        self.insns    = insns

    def __iter__(self):
        return self.insns.__iter__()

    def __str__(self):
        res = ''
        jv = lambda args: ', '.join(map(lambda n: 'v' + str(n), args))
        for i, (t, args) in enumerate(self.insns):
            res += f'v{i + self.n_inputs} = {t.sig.name}({jv(args)}); '
        return res + f'return ({jv(args)})'

    def str_multiline(self):
        return '\n'.join(str(self).split('; '))

def synth(lib : list[TemplateInsn], specs: list[Template], debug=False):
    """Synthesizes a straight-line program that fulfils the specification `spec`
    from the instruction templates in `lib`.
    Returns an object of type Prg if such a program exists or None otherwise.
    """

    assert(len(specs) > 0)
    arg_tys = specs[0].arg_tys
    for s in specs[1:]:
        assert arg_tys == s.arg_tys

    ins = [ InputInsn(i, ty) for i, ty in enumerate(specs[0].arg_tys) ]
    out = OutputInsn([ s.res_ty for s in specs ], len(lib) + len(ins))
    all = lib + ins + [ out ]

    # setup the synthesis constraint
    synth = Solver()
    add_constr_wfp(synth, all)

    # setup the verification constraint
    verif = Solver()
    verif_ins = [ i.instantiate_verif() for i in ins ]
    verif_out = out.instantiate_verif()
    verif_lib = [ t.instantiate_verif() for t in lib ]
    verif_all = verif_ins + verif_lib + [ verif_out ]
    for inst in verif_all:
        verif.add(inst.spec())
    add_constr_conn(verif, verif_all)
    add_constr_spec(verif, specs, verif_out, verif_ins, Not)

    # sample the specification once for an initial set of input samples
    counter_example = sample(specs)

    i = 0
    while True:
        if debug:
            print('counter example', counter_example)
        # create new input instances
        in_instances  = [ it.instantiate_synth(i, v) for it, v in zip(ins, counter_example) ]
        out_instance  = out.instantiate_synth(i)
        # construct new template instances for the new counter example
        lib_instances = [ t.instantiate_synth(i) for t in lib ]
        all_instances = in_instances + lib_instances + [ out_instance ]

        # add the template specifications
        for inst in all_instances:
           synth.add(inst.spec())

        # add the connection constraints
        add_constr_conn(synth, all_instances)

        # add the specification constraint
        add_constr_spec(synth, specs, out_instance, in_instances, lambda x: x)
        if debug:
            print('synth', i, synth)

        if synth.check() == sat:
            # if sat, we found location variables
            m = synth.model()
            # push a new verification solver state
            verif.push()
            # add constraints that set the location variables 
            # in the verification constraint
            add_constr_set_l(verif, lib, out, m)
            if debug:
                print('verif', i, verif)

            if verif.check() == sat:
                # there is a counterexample, reiterate
                m = verif.model()
                counter_example = [ bool(m[i.out()]) for i in verif_ins ]
                verif.pop()
                i += 1
            else:
                # we found no counterexample, the program is therefore correct
                arity = len(ins)
                insns = [ None ] * len(lib)
                for t in lib:
                    idx = m[t.out_loc()].as_long() - arity
                    insns[idx] = (t, [ m[i].as_long() for i in t.ins_loc() ])
                return Prg(arity, m[out.ins_loc()[0]].as_long(), insns)
        else:
            # print('synthesis failed')
            return None

def synth_from_smallest(lib, specs, start_len=1):
    seen = set()
    for i in range(start_len, len(lib)):
        for c in comb(lib, i):
            curr_lib = list(c)
            # create a tuple containing the names of all templates
            # and use it as an id for the currently selected library 
            # templates to check if that combinations has been tried before
            selected = tuple(sorted(map(lambda t: t.template.name, curr_lib)))
            if not selected in seen:
                seen.add(selected)
                if prg := synth(curr_lib, specs):
                    yield prg

def create_lib(sigs: list[(Sig, int)]):
    return [ TemplateInsn(s, f'{s.name}#{i}') for s, n in sigs for i in range(n) ]

Bool1 = [ Bool ]
Bool2 = [ Bool ] * 2
Bool3 = [ Bool ] * 3
Bool4 = [ Bool ] * 4

not1  = Template('not',   Bool, Bool1, lambda ins: Not(ins[0]))         #7404
nand2 = Template('nand2', Bool, Bool2, lambda ins: Not(And(ins)))       #7400
nor2  = Template('nor2',  Bool, Bool2, lambda ins: Not(Or(ins)))        #7402
and2  = Template('and2',  Bool, Bool2, And)                             #7408
or2   = Template('or2',   Bool, Bool2, Or)                              #7432
xor2  = Template('xor2',  Bool, Bool2, lambda ins: Xor(ins[0], ins[1])) #7486
        
nand3 = Template('nand3', Bool, Bool3, lambda ins: Not(And(ins)))       #7410
nor3  = Template('nor3',  Bool, Bool3, lambda ins: Not(Or(ins)))        #7427
and3  = Template('and3',  Bool, Bool3, And)                             #7411
        
nand4 = Template('nand4', Bool, Bool4, lambda ins: Not(And(ins)))       #7420
and4  = Template('and4',  Bool, Bool4, And)                             #7421
nor4  = Template('nor4',  Bool, Bool4, lambda ins: Not(Or(ins)))        #7429
        
mux2  = Template('mux2',  Bool, Bool2, lambda i: Or(And(i[0], i[1]), And(Not(i[0]), i[2])))

def test_and():
    spec = Template('and', Bool, Bool2, And)
    lib = create_lib([
        (nand2, 2),
    ])

    if prg := synth(lib, [ spec ]):
        print(prg.str_multiline())


def test_mux():
    spec = Template('mux2', Bool, Bool3, lambda i: Or(And(i[0], i[1]), And(Not(i[0]), i[2])))
    lib = create_lib([
        (and2, 2),
        (xor2, 2),
        (nand2, 4),
        (or2, 2),
        (not1, 1),
    ])

    for prg in synth_from_smallest(lib, [ spec ], start_len=3):
        print(prg.str_multiline())

if __name__ == "__main__":
    test_and()
    test_mux()