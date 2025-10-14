from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, List, Optional, Tuple
import hashlib
import json

from atlas.aep.ace import Budgets, ProjResult, ace_accept, project_dual_int


# ---------------------------
# Types
# ---------------------------


GradFn = Callable[[List[int], int], List[int]]


@dataclass(frozen=True)
class SpascConfig:
    Q: int
    eta_Q: int
    budgets: Budgets
    B_norms_Q: List[int]
    ablate_mask: Optional[List[int]] = None
    seed: int = 0


@dataclass(frozen=True)
class SpascState:
    step: int
    w_Q: List[int]


@dataclass(frozen=True)
class SpascStepLog:
    step: int
    w_before_Q: List[int]
    grad_Q: List[int]
    w_tilde_Q: List[int]
    proj: ProjResult
    slope_scaled: int
    gap_scaled: int
    accepted: bool
    digest_hex: str


@dataclass(frozen=True)
class SpascResult:
    final: SpascState
    logs: List[SpascStepLog]
    pass_all: bool


# ---------------------------
# Helpers
# ---------------------------


def _apply_ablation(vec: List[int], mask: Optional[List[int]]) -> List[int]:
    if mask is None:
        return list(vec)
    out: List[int] = []
    for idx, value in enumerate(vec):
        m = 1 if idx >= len(mask) else int(mask[idx])
        out.append(int(value) if m != 0 else 0)
    return out


def _sgd_step_int(w_Q: List[int], grad_Q: List[int], eta_Q: int, Q: int) -> List[int]:
    if len(w_Q) != len(grad_Q):
        raise ValueError("grad length mismatch")
    step: List[int] = []
    for w, g in zip(w_Q, grad_Q):
        delta = (eta_Q * int(g)) // Q
        step.append(int(w) - delta)
    return step


def _stable_digest(obj: dict) -> str:
    payload = json.dumps(obj, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


# ---------------------------
# Core API
# ---------------------------


def spasc_step(
    state: SpascState,
    cfg: SpascConfig,
    grad_fn: GradFn,
) -> Tuple[SpascState, SpascStepLog]:
    Q = cfg.Q
    w = list(state.w_Q)
    grad = [int(x) for x in grad_fn(w, state.step)]
    if len(grad) != len(w):
        raise ValueError("grad length mismatch")

    w_tilde = _sgd_step_int(w, grad, cfg.eta_Q, Q)
    proj = project_dual_int(w_tilde, cfg.budgets)
    w_star = _apply_ablation(proj.w_star_Q, cfg.ablate_mask)

    accepted, metrics = ace_accept(w_star, cfg.B_norms_Q, Q, None)
    slope = metrics.slope_scaled

    next_state = SpascState(step=state.step + 1, w_Q=w_star)
    b = list(cfg.budgets.b)
    a = list(cfg.budgets.a)
    if len(b) < len(w_star):
        b.extend([0] * (len(w_star) - len(b)))
    if len(a) < len(w_star):
        a.extend([0] * (len(w_star) - len(a)))
    sum1 = sum(abs(w_star[i]) * abs(b[i]) for i in range(len(w_star)))
    sum2 = sum(abs(w_star[i]) * abs(a[i]) for i in range(len(w_star)))

    log_payload = {
        "step": state.step,
        "w_before_Q": w,
        "grad_Q": grad,
        "w_tilde_Q": w_tilde,
        "w_star_Q": w_star,
        "sum1": sum1,
        "sum2": sum2,
        "lam_Q": proj.lam_Q,
        "mu_Q": proj.mu_Q,
        "slope_scaled": slope,
        "gap_scaled": metrics.gap_scaled,
        "accepted": accepted,
        "Q": Q,
    }
    digest = _stable_digest(log_payload)

    log = SpascStepLog(
        step=state.step,
        w_before_Q=w,
        grad_Q=grad,
        w_tilde_Q=w_tilde,
        proj=ProjResult(
            w_star_Q=w_star,
            sum1=sum1,
            sum2=sum2,
            lam_Q=proj.lam_Q,
            mu_Q=proj.mu_Q,
        ),
        slope_scaled=slope,
        gap_scaled=metrics.gap_scaled,
        accepted=accepted,
        digest_hex=digest,
    )
    return next_state, log


def spasc_train(
    w0_Q: List[int],
    cfg: SpascConfig,
    grad_fn: GradFn,
    max_steps: int,
    stop_on_fault: bool = True,
) -> SpascResult:
    state = SpascState(step=0, w_Q=list(w0_Q))
    logs: List[SpascStepLog] = []
    pass_all = True

    for _ in range(max_steps):
        state, slog = spasc_step(state, cfg, grad_fn)
        logs.append(slog)
        if not slog.accepted:
            pass_all = False
            if stop_on_fault:
                break

    return SpascResult(final=state, logs=logs, pass_all=pass_all)


__all__ = [
    "GradFn",
    "SpascConfig",
    "SpascResult",
    "SpascState",
    "SpascStepLog",
    "spasc_step",
    "spasc_train",
]

