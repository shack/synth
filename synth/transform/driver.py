"""Synthesizers that solve transformed problems first.

`TransformSynth` tries a sequence of problem transformations (see
`synth.transform`): the transformed problem is solved with the `base`
synthesizer, each program found is lifted back to the original productions
and its constants are re-synthesized against the original problem
(`synth.const_synth.solve_constants`).  A lifted program whose constants
cannot be found is *spurious*; after `max_spurious` spurious programs the
next transformation is tried.  If no transformation yields a program, the
original problem is solved with `base` directly.

`Downscale` is the bit-vector instance: it synthesizes at smaller bit widths
first (4, 8, ... below the width of the problem) and re-synthesizes the
constants at full width.
"""
from dataclasses import dataclass, field
from typing import Any, ClassVar, Iterable

from synth import solvers, util
from synth.base_synths import BASE_SYNTHS
from synth.const_synth import solve_constants
from synth.spec import Prg, Problem
from synth.synth_n import LenCegis, _LenBase
from synth.transform import CannotTransform, ProblemTransform
from synth.transform.bv import BitVecDownscale, downscale_widths, max_bit_width


def _can_enumerate(base) -> bool:
    """`_LenBase.synth_all_prgs` enumerates all programs of the smallest
       size.  The objective-driven synthesizers inherit it but override
       `synth_prgs`; enumerating with them would ignore the objective."""
    return isinstance(base, _LenBase) and type(base).synth_prgs is _LenBase.synth_prgs


@dataclass(frozen=True, kw_only=True)
class TransformSynth(util.HasDebug, solvers.HasSolver):
    """Solve transformed problems first, lift the programs and re-synthesize
       their constants against the original problem; fall back to `base`.

       `synth_prgs` takes no `add_constraints` argument: the synthesizers
       that can serve as `base` do not agree on it."""

    base: BASE_SYNTHS = field(default_factory=LenCegis)
    """Synthesizer for the transformed problems and for the fallback."""

    max_spurious: int = 8
    """Give up on a transformation after this many lifted programs whose constants could not be found."""

    # the inherited `solver` is used for the constant re-synthesis

    tag: ClassVar[str] = 'transform'
    """Debug channel."""

    def transforms(self, problem: Problem) -> Iterable[ProblemTransform]:
        raise NotImplementedError

    def _candidates(self, problem: Problem):
        if _can_enumerate(self.base):
            yield from self.base.synth_all_prgs(problem)
        else:
            prgs, stats = self.base.synth_prgs(problem)
            if prgs is not None:
                yield prgs, stats

    def synth_prgs(self, problem: Problem) -> tuple[dict[str, Prg] | None, dict[str, Any]]:
        def d(msg):
            self.debug(self.tag, msg)
        def transform_debug(_tag, *args):
            self.debug(self.tag, *args)
        iterations = []
        verbose    = getattr(self.base, 'verbose', False)
        with util.timer() as elapsed:
            for tr in self.transforms(problem):
                it = { 'transform': str(tr), 'candidates': [], 'spurious': 0 }
                iterations.append(it)
                d(f'(transform "{tr}")')
                if not tr.is_pertinent(problem):
                    it['skipped'] = 'not pertinent'
                    d('(not-pertinent)')
                    continue
                with util.timer() as tr_time:
                    try:
                        tp = tr.transform_problem(problem, transform_debug)
                    except CannotTransform as ex:
                        tp = None
                        it['cannot_transform'] = str(ex)
                        d(f'(cannot-transform "{ex}")')
                    it['transform_time'] = tr_time()
                if tp is None:
                    continue
                it['dropped'] = [ p.sexpr for ps in tp.dropped.values() for p, _ in ps ]
                with util.timer() as it_time:
                    for prgs, stats in self._candidates(tp.transformed):
                        try:
                            lifted = tp.lift_prgs(prgs)
                        except CannotTransform as ex:
                            d(f'(cannot-lift "{ex}")')
                            lifted, res, const_stats = None, None, {}
                        else:
                            res, const_stats = solve_constants(problem, lifted, solver=self.solver,
                                                               d=self.debug, verbose=verbose)
                        it['candidates'].append({ 'synth': stats,
                                                  'const_synth': const_stats,
                                                  'success': res is not None })
                        if res is not None:
                            it['time'] = it_time()
                            d(f'(success "{tr}")')
                            return res, { 'time': elapsed(), 'fallback': False,
                                          'iterations': iterations }
                        it['spurious'] += 1
                        if lifted is not None:
                            d('(spurious ' + ' '.join(p.sexpr(n) for n, p in lifted.items()) + ')')
                        if it['spurious'] >= self.max_spurious:
                            d(f'(max-spurious {it["spurious"]})')
                            break
                    it['time'] = it_time()
            d('(fallback)')
            prgs, stats = self.base.synth_prgs(problem)
        return prgs, { 'time': elapsed(), 'fallback': True,
                       'iterations': iterations, 'fallback_stats': stats }


@dataclass(frozen=True, kw_only=True)
class Downscale(TransformSynth):
    """Bit-vector downscaling: synthesize at smaller bit widths first and
       re-synthesize the constants of the programs found at full width."""

    target_widths: list[int] = field(default_factory=list)
    """Bit widths to try, in order.  Empty: 4, 8, ... below the width of the problem."""

    tag: ClassVar[str] = 'downscale'

    def transforms(self, problem: Problem):
        widths = self.target_widths or downscale_widths(max_bit_width(problem))
        return [ BitVecDownscale(target_width=w) for w in widths ]
