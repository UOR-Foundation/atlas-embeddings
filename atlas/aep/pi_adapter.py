from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, List, Tuple, Optional

import hashlib
import json

from atlas.aep.ace import (
    Budgets,
    ProjResult,
    ace_accept,
    project_dual_int,
    slope_bounds_scaled,
)
from atlas.aep.petc import PETCLedger


# ---------------------------
# Data shapes
# ---------------------------

MatVec = Callable[[List[int]], List[int]]  # input -> output, both scale Q


@dataclass(frozen=True)
class ChannelDef:
    id: str
    sigma: Dict[int, int]  # prime signature
    commutator_class: str
    B_norm_Q: int  # operator norm in scale Q
    B_matvec: MatVec  # respects scale Q (see build_K)


@dataclass(frozen=True)
class PiAtom:
    id: str
    channel_id: str
    wtilde_Q: int  # proposed weight, scale Q (can be negative)


@dataclass(frozen=True)
class PiConfig:
    Q: int
    budgets: Budgets  # ACE budgets (b, a, limits, Q)
    dim: int  # state dimension for K matvec


@dataclass(frozen=True)
class PiAudit:
    digest_hex: str  # sha256 of stable JSON
    petc_budgets: Dict[str, int]  # remaining per commutator class
    used_channels: List[str]  # nonzero weights
    quarantine: bool  # true on any PETC breach


@dataclass(frozen=True)
class PiStep:
    w_star_map_Q: Dict[str, int]  # channel_id -> projected weight (scale Q)
    proj: ProjResult
    slope_scaled: int  # scale Q^2
    gap_scaled: int  # Q^2 - slope
    rho_hat_scaled_opt: Optional[int]
    accepted: bool
    T_next: List[int]  # next state, scale Q
    audit: PiAudit


# ---------------------------
# Aggregation and projection
# ---------------------------


def aggregate_per_channel(atoms: List[PiAtom]) -> Dict[str, int]:
    agg: Dict[str, int] = {}
    for a in atoms:
        agg[a.channel_id] = agg.get(a.channel_id, 0) + int(a.wtilde_Q)
    return agg


def _normalize_vectors(
    channel_ids: List[str],
    agg: Dict[str, int],
    B_norms_Q: Dict[str, int],
) -> Tuple[List[int], List[int]]:
    wtilde_Q: List[int] = []
    norms_Q: List[int] = []
    for cid in channel_ids:
        wtilde_Q.append(int(agg.get(cid, 0)))
        norms_Q.append(int(B_norms_Q.get(cid, 0)))
    return wtilde_Q, norms_Q


# ---------------------------
# Build K as matvec without floats
# ---------------------------


def build_K_matvec(
    channel_ids: List[str],
    w_star_Q_vec: List[int],
    B_matvecs: Dict[str, MatVec],
    Q: int,
) -> MatVec:
    # For v (scale Q), each channel returns Bp(v) also scale Q.
    # Weighted sum: sum_p (w*_p * Bp(v)) // Q keeps scale Q.

    def K(v: List[int]) -> List[int]:
        acc: Optional[List[int]] = None
        for idx, cid in enumerate(channel_ids):
            wq = w_star_Q_vec[idx]
            if wq == 0:
                continue
            out = B_matvecs[cid](v)
            if acc is None:
                acc = [0] * len(out)
            for i in range(len(out)):
                acc[i] += (wq * out[i]) // Q
        if acc is None:
            return [0] * len(v)
        return acc

    return K


def apply_affine(F_Q: List[int], K: MatVec, T_Q: List[int]) -> List[int]:
    Kv = K(T_Q)
    out = [F_Q[i] + Kv[i] for i in range(len(F_Q))]
    return out


# ---------------------------
# PETC audit helpers
# ---------------------------


def petc_audit_and_update_ledger(
    ledger: PETCLedger,
    channels: Dict[str, ChannelDef],
    w_star_map_Q: Dict[str, int],
) -> Tuple[Dict[str, int], bool]:
    """
    Decrement commutator budgets for channels with nonzero weight.
    Returns (remaining_budgets, quarantine).
    """

    remaining: Dict[str, int] = {}
    quarantine = False
    used_classes: Dict[str, int] = {}
    for cid, wq in w_star_map_Q.items():
        if wq == 0:
            continue
        cls = channels[cid].commutator_class
        used_classes[cls] = used_classes.get(cls, 0) + 1
    for cls, cnt in used_classes.items():
        try:
            rem = ledger.decrement_commutator(cls, cnt)
            remaining[cls] = rem
        except Exception:
            quarantine = True
    # fill non-used classes state for reproducibility
    for cls, rem in ledger.commutator_budget.items():
        if cls not in remaining:
            remaining[cls] = rem
    return remaining, quarantine


def _stable_digest(obj: Dict[str, object]) -> str:
    j = json.dumps(obj, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(j.encode("utf-8")).hexdigest()


# ---------------------------
# End-to-end runtime step
# ---------------------------


def pi_runtime_step(
    atoms: List[PiAtom],
    channels: Dict[str, ChannelDef],
    cfg: PiConfig,
    ledger: PETCLedger,
    F_Q: List[int],
    T_Q: List[int],
    rho_hat_scaled_opt: Optional[int] = None,
) -> PiStep:
    """
    Pipeline:
      1) aggregate per-channel proposals
      2) ACE projection to S
      3) build K and step: T_{t+1} = F + K T_t
      4) AUDIT(PETC): ledger rows + digests; quarantine on breach
    """

    Q = cfg.Q
    # 1) aggregate
    agg = aggregate_per_channel(atoms)
    # normalize vectors in channel order
    channel_ids = sorted(channels.keys())
    B_norms_Q: Dict[str, int] = {cid: channels[cid].B_norm_Q for cid in channel_ids}
    wtilde_Q_vec, norms_Q_vec = _normalize_vectors(channel_ids, agg, B_norms_Q)
    # 2) project
    budgets = cfg.budgets
    proj = project_dual_int(wtilde_Q_vec, budgets)
    # 3) acceptance by slope / optional rho-hat
    slope_s, gap_s, metrics = slope_bounds_scaled(proj.w_star_Q, norms_Q_vec, Q)
    ok, metrics_after = ace_accept(proj.w_star_Q, norms_Q_vec, Q, rho_hat_scaled_opt)
    metrics_gap = metrics_after.gap_scaled if hasattr(metrics_after, "gap_scaled") else gap_s
    # K matvec
    B_mv: Dict[str, MatVec] = {cid: channels[cid].B_matvec for cid in channel_ids}
    K = build_K_matvec(channel_ids, proj.w_star_Q, B_mv, Q)
    T_next = apply_affine(F_Q, K, T_Q)
    # 4) PETC audit
    w_star_map = {cid: proj.w_star_Q[i] for i, cid in enumerate(channel_ids)}
    budgets_left, quarantine = petc_audit_and_update_ledger(ledger, channels, w_star_map)
    audit_payload = {
        "w_star_map_Q": w_star_map,
        "B_norms_Q": B_norms_Q,
        "budgets_left": budgets_left,
        "accepted": bool(ok),
        "quarantine": bool(quarantine),
    }
    digest = _stable_digest(audit_payload)
    audit = PiAudit(
        digest_hex=digest,
        petc_budgets=budgets_left,
        used_channels=[c for c, v in w_star_map.items() if v != 0],
        quarantine=quarantine,
    )
    gap_value = metrics_gap if ok else (Q * Q - slope_s)
    return PiStep(
        w_star_map_Q=w_star_map,
        proj=proj,
        slope_scaled=slope_s,
        gap_scaled=gap_value,
        rho_hat_scaled_opt=rho_hat_scaled_opt,
        accepted=bool(ok) and not quarantine,
        T_next=T_next,
        audit=audit,
    )


__all__ = [
    "ChannelDef",
    "PiAtom",
    "PiConfig",
    "PiAudit",
    "PiStep",
    "aggregate_per_channel",
    "build_K_matvec",
    "pi_runtime_step",
]
