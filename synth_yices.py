
import subprocess
from z3 import *
from cegis import *
from synth_n import *
from synth_fa import SynthFA
from util import bv_sort


yices_path = "/Users/nicolasedelmann/Downloads/yices-2.6.4/bin/yices-smt2"

def get_yices_command(filename):
    return f'{yices_path} {filename} --smt2-model-format'



class SynthYC(SynthN):
    def __init__(self, spec: Spec, ops: list[Func], n_insns, \
        debug=no_debug, timeout=None, max_const=None, const_set=None, \
        output_prefix=None, theory=None, reset_solver=True, \
        opt_no_dead_code=True, opt_no_cse=True, opt_const=True, \
        opt_commutative=True, opt_insn_order=True):
        assert all(insn.ctx == spec.ctx for insn in ops)
        self.ctx       = ctx = Context()
        self.orig_spec = spec
        self.spec      = spec = spec.translate(ctx)

        if len(ops) == 0:
            ops = { Func('dummy', Int('v') + 1): 0 }
        elif type(ops) == list or type(ops) == set:
            ops = { op: OpFreq.MAX for op in ops }

        self.orig_ops  = { op.translate(ctx): op for op in ops }

        self.op_from_orig = { orig: new for new, orig in self.orig_ops.items() }

        self.op_freqs  = { op_new: ops[op_old] for op_new, op_old in self.orig_ops.items() }
        self.ops       = ops = list(self.orig_ops.keys())
        self.n_insns   = n_insns

        self.in_tys    = spec.in_types
        self.out_tys   = spec.out_types
        self.n_inputs  = len(self.in_tys)
        self.n_outputs = len(self.out_tys)
        self.out_insn  = self.n_inputs + self.n_insns
        self.length    = self.out_insn + 1
        max_arity      = max(op.arity for op in ops)
        self.arities   = [ 0 ] * self.n_inputs \
                       + [ max_arity ] * self.n_insns \
                       + [ self.n_outputs ]

        assert all(o.ctx == ctx for o in self.ops)
        assert all(op.ctx == spec.ctx for op in self.orig_ops)
        types = set(ty for op in ops for ty in op.out_types + op.in_types)

        # prepare operator bv sort -> EnumSort not supported by Yices due to lack of (declare-datatypes)
        self.op_enum = BitVecEnum('Operators', ops, ctx)
        # create map of types to their id
        self.ty_enum = BitVecEnum('Types', types, ctx)

        # get the sorts for the variables used in synthesis
        self.ty_sort = self.ty_enum.sort
        self.op_sort = self.op_enum.sort
        self.ln_sort = bv_sort(self.length - 1, ctx)
        self.bl_sort = BoolSort(ctx=ctx)

        # set options
        self.d = debug
        self.n_samples = 0
        self.output_prefix = output_prefix
        self.reset_solver = reset_solver

        if theory:
            self.synth_solver = SolverFor(theory, ctx=ctx)
        else:
            self.synth_solver = Tactic('psmt', ctx=ctx).solver()
        if not timeout is None:
            self.synth_solver.set('timeout', timeout)
        self.synth = Goal(ctx=ctx) if reset_solver else self.synth_solver
        # add well-formedness, well-typedness, and optimization constraints
        self.add_constr_wfp(max_const, const_set)
        self.add_constr_ty()
        self.add_constr_opt(opt_no_dead_code, opt_no_cse, opt_const, \
                            opt_commutative, opt_insn_order)
        self.d(1, 'size', self.n_insns)


    # a little bit of spaghetti code to get the correct variable for the given type
    def parse_smt2_output(self, model_string):
        model = {}
        for line in model_string.split('\n'):
            line = line.strip()
            if line.startswith('(define-fun '):
                # remove all leading and trailing parentheses
                while line.startswith('('):
                    line = line[1:]
                
                while line.endswith(')'):
                    line = line[:-1]


                _, var, _, type_with_val = line.split(' ', 3)
                
                # parse type and value
                # TODO: implement more types as needed
                if type_with_val.startswith('(_ BitVec'):
                    # size contains the closing parenthesis
                    _, _, size, val = type_with_val.split(' ', 3)
                    # remove closing parenthesis and prefix #b
                    val = val[2:]
                    size = size[:-1]
                    model[var] = BitVecVal(int(val, 2), int(size), ctx=self.ctx)
                elif type_with_val.startswith('Bool'):
                    _, val = type_with_val.split(' ', 1)
                    model[var] = val == 'true'
                elif type_with_val.startswith('Int'):
                    _, val = type_with_val.split(' ', 1)
                    model[var] = int(val)
                else:
                    print("Unknown type in model: " + type_with_val)
                    print("Full line: " + line)
                    exit(1)
                
                # extend model by piped version
                model[f'|{var}|'] = model[var]
        return model

    def create_prg_from_yices_model(self, model_string):
        model = self.parse_smt2_output(model_string)

        # print(model)

        def prep_opnds(insn, tys):
            for _, opnd, c, cv in self.iter_opnd_info_struct(insn, tys):
                opnd, c, cv = str(opnd), str(c), str(cv)
                if is_true(model[c]):
                    assert not model[cv] is None
                    yield (True, model[cv].translate(self.orig_spec.ctx))
                else:
                    assert not model[opnd] is None, str(opnd) + str(model)
                    yield (False, model[opnd].as_long())
        insns = []

        for insn in range(self.n_inputs, self.length - 1):
            val    = model[str(self.var_insn_op(insn))]
            op     = self.op_enum.get_from_model_val(val)
            opnds  = [ v for v in prep_opnds(insn, op.in_types) ]
            insns += [ (self.orig_ops[op], opnds) ]
        outputs      = [ v for v in prep_opnds(self.out_insn, self.out_tys) ]
        return Prg(self.orig_spec, insns, outputs)

    def synth_with_new_samples(self, samples):
        ctx       = self.ctx
        samples   = [ [ v.translate(ctx) for v in s ] for s in samples ]

        def write_smt2(*args):
            s = self.synth
            if not type(s) is Solver:
                s = Solver(ctx=ctx)
                s.add(self.synth)
            if self.output_prefix:
                filename = f'{self.output_prefix}_{"_".join(str(a) for a in args)}.smt2'
                with open(filename, 'w') as f:
                    print(s.to_smt2(), file=f)

        def write_smt2_for_yices():
            s = self.synth
            if not type(s) is Solver:
                s = Solver(ctx=ctx)
                s.add(self.synth)
            
            filename = f'to_be_solved_by_yices.smt2'
            with open(filename, 'w') as f:
                solving = s.to_smt2()

                # weird z3 syntax allowing simple *and* as expression, while yices reads it as identifier
                solving = solving.replace("and)", "(and true))")


                solving = "(set-option :produce-models true)\n(set-logic BV)\n" + solving + "\n(get-model)"
                print(solving, file=f)
                return solving
                
        # main synthesis algorithm.
        # 1) set up counter examples
        for sample in samples:
            # add a new instance of the specification for each sample
            self.add_constr_instance(self.n_samples)
            if self.spec.is_deterministic and self.spec.is_total:
                # if the specification is deterministic and total we can
                # just use the specification to sample output values and
                # include them in the counterexample constraints.
                out_vals = self.spec.eval(sample)
                self.add_constr_io_sample(self.n_samples, sample, out_vals)
            else:
                # if the spec is not deterministic or total, we have to
                # express the output of the specification implicitly by
                # the formula of the specification.
                self.add_constr_io_spec(self.n_samples, sample)
            self.n_samples += 1
        write_smt2('synth', self.n_insns, self.n_samples)

        if self.reset_solver:
            self.synth_solver.reset()
            self.synth_solver.add(self.synth)


        stat = {}

        _ = write_smt2_for_yices()

        cmd = get_yices_command('to_be_solved_by_yices.smt2')
        self.d(3, cmd)
        p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        output = p.stdout.decode('utf-8')
        # print(output)

        if output.startswith('sat'):
            print("SAT")
            model = output.split("\n",1)[1]

            # parse the model
            #ast = parse_smt2_string(model, decls=None, ctx=self.synth_solver.ctx)

            #print(ast)
            prg = self.create_prg_from_yices_model(model)

            print(model)
            print(prg)

            if [132] in samples:
               exit(1)

            return prg, stat



        else:
            print("UNSAT")
            return None, stat


        if self.reset_solver:
            self.synth_solver.reset()
            self.synth_solver.add(self.synth)
        self.d(3, 'synth', self.n_samples, self.synth_solver)
        with timer() as elapsed:
            res = self.synth_solver.check()
            synth_time = elapsed()
            stat['synth_stat'] = self.synth_solver.statistics()
            self.d(5, stat['synth_stat'])
            self.d(2, f'synth time: {synth_time / 1e9:.3f}')
            stat['synth_time'] = synth_time
        if res == sat:
            # if sat, we found location variables
            m = self.synth_solver.model()
            prg = self.create_prg(m)
            self.d(4, 'model: ', m)
            return prg, stat
        else:
            return None, stat


def synth(spec: Spec, ops, iter_range, n_samples=1, downsize=False, **args):
    print("RUNNING YICES")

    """Synthesize a program that computes the given function.

    Attributes:
    spec: Specification of the function to be synthesized.
    ops: Collection (set/list) of operations that can be used in the program.
    iter_range: Range of program lengths that are tried.
    n_samples: Number of initial I/O samples to give to the synthesizer.
    args: arguments passed to the synthesizer

    Returns:
    A tuple (prg, stats) where prg is the synthesized program (or None
    if no program has been found) and stats is a list of statistics for each
    iteration of the synthesis loop.
    """
    all_stats = []
    init_samples = spec.eval.sample_n(n_samples)
    for n_insns in iter_range:
        with timer() as elapsed:
            synthesizer = SynthYC(spec, ops, n_insns, **args)
            prg, stats = cegis(spec, synthesizer, init_samples=init_samples, \
                               debug=synthesizer.d)
            all_stats += [ { 'time': elapsed(), 'iterations': stats } ]
            if not prg is None:
                return prg, all_stats
    return None, all_stats