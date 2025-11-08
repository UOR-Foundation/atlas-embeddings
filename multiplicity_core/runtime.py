from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, Hashable, Iterable, Optional

from .lanes import MultiClassLaneStore
from .toggles import ToggleStreams
from .quantizer import Z96Quantizer
from .ace import ACEProjector, ACEParams
from .petc import PETCLedger
from .signature import digest

ClassID = Hashable

@dataclass
class MultiplicityRuntime:
    """Prime‑graded, contractive runtime with lanes, ACE, PETC, toggles, and Z₉₆ quantization.

    This is architecture glue. It does not implement Hecke/replicability; it just lays the core.
    """

    active_class: ClassID
    quantizer: Z96Quantizer = field(default_factory=Z96Quantizer)
    lanes: MultiClassLaneStore = field(init=False)
    toggles: ToggleStreams = field(default_factory=ToggleStreams)
    ledger: PETCLedger = field(default_factory=PETCLedger)

    def __post_init__(self) -> None:
        self.lanes = MultiClassLaneStore(self.active_class)

    # --- Class switching
    def switch_class(self, new_class: ClassID) -> None:
        self.lanes.switch_class(new_class)
        self.active_class = new_class
        self.ledger.append("switch_class", {"new_class": str(new_class)})

    # --- ACE projection and channel weights
    def ace_project(self, w_hat: Dict[int, float], bounds_b: Dict[int, float], params: ACEParams) -> Dict[int, float]:
        w, gapLB = ACEProjector.project_weighted_l1(w_hat, bounds_b, params.radius())
        self.ledger.append("ace_project", {
            "proposal": w_hat,
            "bounds_b": bounds_b,
            "R_t": params.radius(),
            "accepted": w,
            "gapLB": gapLB,
        })
        return w

    # --- Ingest: quantize and write to lanes gated by toggles
    def ingest(self, t: int, real_inputs: Dict[int, float]) -> Dict[int, int]:
        out: Dict[int, int] = {}
        for n, x in real_inputs.items():
            if self.toggles.is_on(n, t):
                z = self.quantizer.quantize(x)
                self.lanes.write(n, z)
                out[n] = z
        if out:
            self.ledger.append("ingest", {
                "t": int(t),
                "class": str(self.active_class),
                "lanes": out,
            })
        return out

    # --- Utility: batch read
    def read_lanes(self, indices: Iterable[int]) -> Dict[int, int]:
        return {n: self.lanes.read(n) for n in indices}

    # --- PETC audit helpers
    def last_digest(self) -> str:
        return self.ledger.rows[-1].digest if self.ledger.rows else "0" * 64

    def verify_ledger(self) -> bool:
        return self.ledger.verify()
