from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Tuple
import json
import hashlib

from atlas.aep.petc import eq_signatures, PETCLedger


# ---------------------------
# Types
# ---------------------------


@dataclass(frozen=True)
class OperatorDef:
    id: str
    in_sig: Dict[int, int]  # prime->exponent
    out_sig: Dict[int, int]  # prime->exponent
    norm_Q: int  # ||G|| in scale Q (integer)
    commutator_class: str  # for budget accounting


@dataclass(frozen=True)
class MoonshineConfig:
    Q: int  # global scale (>0)


@dataclass(frozen=True)
class SmallGainDecision:
    ok: bool
    product_scaled: int  # g1_Q * g2_Q  (scale Q^2)
    threshold: int  # Q^2


@dataclass(frozen=True)
class FeedbackAcceptance:
    typed_ok: bool
    small_gain: SmallGainDecision
    quarantine: bool  # true on any budget breach


@dataclass(frozen=True)
class ZKSketch:
    ledger_digest: str
    ace_digest: str
    challenge_hex: str
    checks: Dict[str, int]


# ---------------------------
# Typing and budgets
# ---------------------------


def check_typing(g1: OperatorDef, g2: OperatorDef) -> bool:
    # Composition requires out_sig(G1) == in_sig(G2)
    return eq_signatures(g1.out_sig, g2.in_sig)


def decrement_budgets_for_feedback(
    ledger: PETCLedger, g1: OperatorDef, g2: OperatorDef
) -> Tuple[Dict[str, int], bool]:
    """Decrement commutator budgets for both operator classes."""

    remaining: Dict[str, int] = {}
    quarantine = False
    for cls in (g1.commutator_class, g2.commutator_class):
        try:
            rem = ledger.decrement_commutator(cls, 1)
            remaining[cls] = rem
        except Exception:
            quarantine = True
    for cls, rem in ledger.commutator_budget.items():
        if cls not in remaining:
            remaining[cls] = rem
    return remaining, quarantine


# ---------------------------
# Small-gain check (integer)
# ---------------------------


def small_gain_accept(g1_norm_Q: int, g2_norm_Q: int, Q: int) -> SmallGainDecision:
    prod = g1_norm_Q * g2_norm_Q  # scale Q^2
    thr = Q * Q
    return SmallGainDecision(ok=prod < thr, product_scaled=prod, threshold=thr)


# ---------------------------
# ZK sketch (Fiat–Shamir style, integer-only)
# ---------------------------


def _digest(obj: Dict[str, object]) -> str:
    j = json.dumps(obj, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(j.encode("utf-8")).hexdigest()


def _fs_challenge_hex(*parts: str) -> str:
    h = hashlib.sha256()
    for p in parts:
        h.update(p.encode("utf-8"))
    return h.hexdigest()


def zk_sketch(
    ledger: PETCLedger,
    ace_metrics: List[Dict[str, int]],
    seed_hex: str = "00",
) -> ZKSketch:
    bud = {k: int(v) for k, v in sorted(ledger.commutator_budget.items())}
    ledger_digest = _digest({"commutator_budget": bud})
    ace_sorted: List[Dict[str, int]] = []
    for m in ace_metrics:
        ace_sorted.append({k: int(m[k]) for k in sorted(m.keys())})
    ace_digest = _digest({"ace": ace_sorted})
    chal = _fs_challenge_hex(seed_hex, ledger_digest, ace_digest)
    MOD = (1 << 61) - 1
    r = int(chal, 16) % (MOD - 1)
    if r == 0:
        r = 1
    c1 = 0
    i = 0
    for _, v in bud.items():
        i += 1
        c1 = (c1 + (v * pow(r, i, MOD))) % MOD
    c2 = 0
    j = 0
    for m in ace_sorted:
        j += 1
        slope = int(m.get("slope_scaled", 0))
        gap = int(m.get("gap_scaled", 0))
        c2 = (
            c2
            + (slope * pow(r, 2 * j, MOD))
            + (gap * pow(r, 2 * j + 1, MOD))
        ) % MOD
    return ZKSketch(
        ledger_digest=ledger_digest,
        ace_digest=ace_digest,
        challenge_hex=chal,
        checks={"c1": c1, "c2": c2, "mod": MOD, "r": r},
    )


# ---------------------------
# End-to-end feedback acceptance
# ---------------------------


def accept_feedback_interconnection(
    g1: OperatorDef,
    g2: OperatorDef,
    cfg: MoonshineConfig,
    ledger: PETCLedger,
    ace_metrics: List[Dict[str, int]],
    seed_hex: str = "00",
) -> Tuple[FeedbackAcceptance, ZKSketch, Dict[str, int]]:
    typed_ok = check_typing(g1, g2)
    sg = small_gain_accept(g1.norm_Q, g2.norm_Q, cfg.Q)
    remaining, quarantine = decrement_budgets_for_feedback(ledger, g1, g2)
    sketch = zk_sketch(ledger, ace_metrics, seed_hex)
    return (
        FeedbackAcceptance(typed_ok=typed_ok, small_gain=sg, quarantine=quarantine),
        sketch,
        remaining,
    )
