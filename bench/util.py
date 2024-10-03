from typing import Dict, Optional, Iterable
from dataclasses import dataclass

from synth.spec import Spec, Func
from z3 import ExprRef

@dataclass(frozen=True)
class Bench:
    name: str
    spec: Spec
    ops: Dict[Func, Optional[int]]
    all_ops: Iterable[Func] = None
    consts: Optional[Dict[ExprRef, int]] = None
    desc: Optional[str] = None
    theory: Optional[str] = None
