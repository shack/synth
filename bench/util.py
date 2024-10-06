from typing import Dict, Optional, Iterable
from dataclasses import dataclass
from contextlib import contextmanager

from synth.spec import Spec, Func

@contextmanager
def timeout(duration: Optional[int]):
    import signal
    def timeout_handler(signum, frame):
        raise TimeoutError(f'timeout after {duration} seconds')
    if not duration is None:
        signal.signal(signal.SIGALRM, timeout_handler)
        signal.alarm(duration)
    try:
        yield
    finally:
        if not duration is None:
            signal.alarm(0)

@dataclass(frozen=True)
class Bench:
    name: str
    spec: Spec
    ops: Dict[Func, Optional[int]]
    all_ops: Optional[Iterable[Func]] = None
    consts: Optional[Dict[ExprRef, int]] = None
    desc: Optional[str] = None
    theory: Optional[str] = None
