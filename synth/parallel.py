"""Trying several program lengths at the same time.

`search` runs one worker process per program length.  Z3 contexts must not
be shared between threads and all of the code uses the global context, so
the workers are forked: they inherit the problem, the synthesis session
(with its samples) and closures such as the `add_constraints` of
`OptSearch`.  Killing a worker is also the only reliable way to stop a
running solver call.

The workers send their results through a pipe.  Z3 terms cannot be pickled
(they are ctypes pointers), so `Transport` writes them as SMT-LIB text and
sends the objects the parent has as well (the synthesized functions, their
productions and weight variables) as references.
"""
import io
import multiprocessing
import multiprocessing.connection
import os
import pickle
import signal
import sys
import threading
import time
import traceback

from enum import Enum, auto

from z3 import *

from synth import util
from synth.spec import Func, Problem


class ParMode(Enum):
    MIN = auto()
    """Return a shortest program: the program of a length is returned once
       all shorter lengths turned out to have none."""

    FIRST = auto()
    """Return the first program that any worker finds (not necessarily a
       shortest one)."""


_PLACEHOLDER = '$transport'

def _load_value(sort, val):
    # Some values come back as applications, e.g. (- 5) or (/ 1.0 3.0);
    # simplify turns them into numerals again.
    a, = parse_smt2_string(f'(declare-const |{_PLACEHOLDER}| {sort}) '
                           f'(assert (= |{_PLACEHOLDER}| {val}))')
    return simplify(_other_side(a))

def _load_expr(smt2):
    s = Solver()
    s.from_string(smt2)
    return _other_side(s.assertions()[0])

def _other_side(eq):
    # z3 may swap the sides of an equation, e.g. to put a numeral first
    return next(c for c in eq.children()
                if not (is_const(c) and c.decl().name() == _PLACEHOLDER))

def _reduce_expr(e):
    if util.is_val(e):
        return _load_value, (e.sort().sexpr(), e.sexpr())
    s = Solver()
    s.add(Const(_PLACEHOLDER, e.sort()) == e)
    return _load_expr, (s.to_smt2(),)

def _load_func(name, func, precond, inputs):
    return Func(name, func, precond=precond, inputs=inputs)

class Transport:
    """Pickles the messages of the workers of `search` for `problem`.

    The synthesized functions, their productions and their weight variables
    are sent as references: the table of them is built before the workers
    are forked, so a worker has the very same objects.  Z3 terms are sent as
    SMT-LIB text.  Productions the worker created itself (the nop
    instruction of `LenConstraints`) are sent by value."""

    def __init__(self, problem: Problem):
        shared = []
        for f in problem.funcs.values():
            shared.append(f)
            for nt in f.nonterminals.values():
                shared.extend(nt.productions)
            shared.extend(var for _, var in f.weights.values())
        self.shared = shared
        # The objects in `shared` stay alive in the worker, so no object the
        # worker creates can have the id of one of them.
        self.index  = { id(o): i for i, o in enumerate(shared) }

    def dumps(self, obj) -> bytes:
        f = io.BytesIO()
        _Pickler(f, self).dump(obj)
        return f.getvalue()

    def loads(self, data: bytes):
        return _Unpickler(io.BytesIO(data), self).load()

class _Pickler(pickle.Pickler):
    def __init__(self, file, transport):
        super().__init__(file)
        self.transport = transport

    def persistent_id(self, obj):
        return self.transport.index.get(id(obj))

    def reducer_override(self, obj):
        if isinstance(obj, ExprRef):
            return _reduce_expr(obj)
        if isinstance(obj, Func):
            return _load_func, (obj.name, obj.func, obj.precond, obj.inputs)
        return NotImplemented

class _Unpickler(pickle.Unpickler):
    def __init__(self, file, transport):
        super().__init__(file)
        self.transport = transport

    def persistent_load(self, pid):
        return self.transport.shared[pid]


def _watch_parent(ppid):
    # If the parent is killed (and not its process group with it), the
    # worker would run on.
    while True:
        time.sleep(1)
        if os.getppid() != ppid:
            os._exit(1)

def _work(conn, transport, gen_fn, n_insns, ppid, inherited):
    """Body of the worker process for `n_insns` instructions.

    Sends ('prg', (prgs, stats)) for every program that `gen_fn(n_insns)`
    yields, and then ('done', stats) with the stats of the last attempt
    without a program (or None).  On an exception it sends ('error',
    (pickled exception or None, traceback))."""
    for c in inherited:
        c.close()
    # On Ctrl-C, the parent kills the workers.
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    threading.Thread(target=_watch_parent, args=(ppid,), daemon=True).start()
    try:
        final = None
        for prgs, stats in gen_fn(n_insns):
            if prgs is None:
                final = stats
            else:
                conn.send_bytes(pickle.dumps(('prg', transport.dumps((prgs, stats)))))
        msg = ('done', transport.dumps(final))
    except Exception as e:
        tb = traceback.format_exc()
        try:
            exc = pickle.dumps(e)
        except Exception:
            exc = None
        msg = ('error', (exc, tb))
    sys.stdout.flush()
    conn.send_bytes(pickle.dumps(msg))
    conn.close()

class _Worker:
    def __init__(self, ctx, transport, gen_fn, n_insns, inherited):
        self.n_insns = n_insns
        self.conn, child = ctx.Pipe(duplex=False)
        # daemon: workers that are left over at exit are terminated
        self.process = ctx.Process(target=_work, daemon=True,
                                   args=(child, transport, gen_fn, n_insns,
                                         os.getpid(), inherited))
        self.process.start()
        # The parent must not keep the write end, otherwise it would not see
        # the end of the pipe when the worker dies.
        child.close()
        # first program of the worker, not yet unpickled (see search)
        self.prg = None

    def recv(self):
        try:
            return pickle.loads(self.conn.recv_bytes())
        except EOFError:
            self.process.join()
            raise RuntimeError(f'worker for {self.n_insns} instructions died '
                               f'(exit code {self.process.exitcode})')

    def join(self):
        # the worker exits right after its last message
        self.process.join()
        self.conn.close()

    def kill(self):
        self.process.kill()
        self.join()

def _raise(n_insns, exc, tb):
    note = f'in the worker for {n_insns} instructions:\n{tb}'
    try:
        e = pickle.loads(exc) if exc is not None else None
    except Exception:
        e = None
    if e is None:
        raise RuntimeError(note)
    e.add_note(note)
    raise e

def search(gen_fn, lo: int, hi: int, workers: int, mode: ParMode,
           transport: Transport, d=util.no_debug, stats=None):
    """Searches the program lengths lo..hi with `workers` lengths at a time.

    `gen_fn(n_insns)` is run in a forked worker; it yields pairs (prgs,
    stats) where prgs is None for the stats of an attempt without a program.
    The lengths are started in increasing order, a new one whenever a
    worker finishes without a program.  The length to return programs of
    depends on `mode`:

    - MIN: a program of length n stops (and kills) the workers of the
      lengths above n.  Its length is chosen once all lengths below it
      finished without programs.
    - FIRST: the first program that a worker finds chooses its length.

    Yields (None, stats) for every length that finished without programs,
    in increasing order, and then the pairs of all programs of the chosen
    length (the worker keeps enumerating until `gen_fn` stops).  If no
    length has a program, yields only the former.

    The parent unpickles the programs only after the length has been
    chosen and the stats of the other lengths contain no Z3 terms.  So it
    creates no Z3 terms while it forks workers: the worker of a length
    always starts from the same state, whatever the timing.  This matters
    because the ids of the terms steer the search of Z3 (see
    `util.disable_automatic_gc`).

    If `stats` is given, it receives the parameters of the search and the
    status ('unsat', 'prg' or 'killed'), start and run time (in s) of
    every length that was started."""
    if 'fork' not in multiprocessing.get_all_start_methods():
        raise RuntimeError('trying lengths in parallel requires the fork start method')
    ctx       = multiprocessing.get_context('fork')
    running   = {}   # n_insns -> _Worker
    finished  = {}   # n_insns -> stats of a length without programs
    records   = {}
    committed = None
    if stats is not None:
        stats.update(workers=workers, mode=mode.name, start=lo, lengths=[])

    def end(w, status):
        r = records[w.n_insns]
        r['status'] = status
        r['time']   = elapsed() / 1e9 - r['start']
        del running[w.n_insns]

    def kill(w):
        d('len', f'(par-kill {w.n_insns})')
        w.kill()
        end(w, 'killed')

    def commit(w, data):
        nonlocal committed
        committed = w
        d('len', f'(par-commit {w.n_insns} {elapsed() / 1e9:.2f}s)')
        for other in list(running.values()):
            if other is not w:
                kill(other)
        for n in sorted(finished):
            yield None, finished[n]
        yield transport.loads(data)
        while True:
            kind, data = w.recv()
            match kind:
                case 'prg':
                    yield transport.loads(data)
                case 'done':
                    w.join()
                    end(w, 'prg')
                    res = transport.loads(data)
                    if res is not None:
                        yield None, res
                    return
                case 'error':
                    _raise(w.n_insns, *data)

    next_n = lo
    best   = None
    with util.timer() as elapsed:
        try:
            while True:
                while len(running) < workers and next_n <= hi and best is None:
                    t = elapsed() / 1e9
                    d('len', f'(par-start {next_n} {t:.2f}s)')
                    inherited = [ w.conn for w in running.values() ]
                    running[next_n] = _Worker(ctx, transport, gen_fn, next_n, inherited)
                    records[next_n] = { 'n_insns': next_n, 'start': t }
                    next_n += 1
                # all lengths below best are started and none is running
                if best is not None and min(running) == best:
                    yield from commit(running[best], running[best].prg)
                    return
                if not running:
                    for n in sorted(finished):
                        yield None, finished[n]
                    return
                # in MIN mode, a worker that found a program is not read
                # until its length is chosen; it blocks once the pipe is full
                waiting = { w.conn: w for w in running.values() if w.prg is None }
                ready   = multiprocessing.connection.wait(list(waiting))
                for w in sorted((waiting[c] for c in ready), key=lambda w: w.n_insns):
                    if w.n_insns not in running:
                        # killed because of a shorter program found just now
                        continue
                    kind, data = w.recv()
                    t = elapsed() / 1e9
                    match kind:
                        case 'done':
                            d('len', f'(par-unsat {w.n_insns} {t:.2f}s)')
                            finished[w.n_insns] = transport.loads(data)
                            w.join()
                            end(w, 'unsat')
                        case 'prg':
                            d('len', f'(par-prg {w.n_insns} {t:.2f}s)')
                            if mode == ParMode.FIRST:
                                yield from commit(w, data)
                                return
                            w.prg = data
                            best  = w.n_insns if best is None else min(best, w.n_insns)
                            for other in list(running.values()):
                                if other.n_insns > best:
                                    kill(other)
                            shorter = [ str(n) for n in sorted(running) if n < best ]
                            if shorter:
                                d('len', f'(par-wait {" ".join(shorter)})')
                        case 'error':
                            _raise(w.n_insns, *data)
        finally:
            # left over after an exception or when the caller stops early
            for w in list(running.values()):
                if w is committed:
                    w.kill()
                    end(w, 'prg')
                else:
                    kill(w)
            if stats is not None:
                stats['lengths'] = [ records[n] for n in sorted(records) ]
