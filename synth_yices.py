
import subprocess
from z3 import *
from cegis import *
from synth_n import SynthN
from synth_fa import SynthFA


yices_path = "/Users/nicolasedelmann/Downloads/yices-2.6.4/bin/yices-smt2"

class SynthYC(SynthN):
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
            if self.output_prefix:
                filename = f'to_be_solved_by_yices.smt2'
                with open(filename, 'w') as f:
                    solving = s.to_smt2()
                    solving = "(set-logic BV)\n" + solving + "\n(get-model)"
                    print(solving, file=f)
                

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
        stat = {}

        write_smt2_for_yices()
        cmd = f'{yices_path} to_be_solved_by_yices.smt2 --smt2-model-format'
        self.d(3, cmd)
        p = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        output = p.stdout.decode('utf-8')
        print(output)

        if output.startswith('sat'):
            print("SAT")
            model = output.split("\n",1)[1]

            # parse the model
            #ast = parse_smt2_string(model, decls=None, ctx=self.synth_solver.ctx)

            #print(ast)

        else:
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