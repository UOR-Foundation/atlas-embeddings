from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Dict, List, Protocol, Tuple, Literal
import time
from decimal import Decimal, ROUND_HALF_EVEN

Status = Literal["PASS", "FAULT"]


@dataclass(frozen=True)
class AEP:
    C: List[str]
    K: "Kernel"
    W: Dict[str, Any]
    theta: Dict[str, Any]


class Kernel(Protocol):
    def eval(self, ctx: Dict[str, Any]) -> Dict[str, Any]:
        ...


class Predicate(Protocol):
    name: str
    code: int

    def check(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        ...

    def resolve(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        ...


@dataclass
class Decision:
    status: Status
    code: int
    reason: str
    evidence: Dict[str, Any]
    log: List[Dict[str, Any]]


def _event(op: str, **kv: Any) -> Dict[str, Any]:
    kv["op"] = op
    kv["ts"] = time.time_ns()
    return kv


# ---- Quantization helpers (no-float) ----
def _quantum(theta: Dict[str, Any]) -> int:
    try:
        q = int(theta.get("Q", 1_000_000))
    except Exception:
        q = 1_000_000
    return q if q > 0 else 1_000_000


def _to_int_vec(vec: List[Any], quantum: int) -> List[int]:
    out: List[int] = []
    for value in vec:
        scaled = (Decimal(str(value)) * Decimal(quantum)).to_integral_value(
            rounding=ROUND_HALF_EVEN
        )
        out.append(int(scaled))
    return out


def ISA_ASSERT_attrs(C: List[str], attrs: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
    missing = [k for k in C if k not in attrs.get("claims", [])]
    return len(missing) == 0, {"missing": missing, "attrs_claims": attrs.get("claims", [])}


def ISA_EVAL_kernel(K: Kernel, ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
    try:
        out = K.eval(ctx)
        return True, {"kernel_out": out}
    except Exception as exc:  # pragma: no cover - exception path
        return False, {"error": repr(exc)}


def ISA_AUDIT_witness(W: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
    ok = ("R_pre" in W and "R_post" in W) or ("delta_R" in W)
    return ok, {"keys": sorted(W.keys())}


def launch(aep: AEP, predicates: Dict[str, Predicate], attrs: Dict[str, Any]) -> Decision:
    log: List[Dict[str, Any]] = []

    ok, info_attrs = ISA_ASSERT_attrs(aep.C, attrs)
    log.append(_event("ASSERT", ok=ok, info=info_attrs))
    if not ok:
        return Decision("FAULT", 100, "attrs missing declared claims", info_attrs, log)

    ok, info_eval = ISA_EVAL_kernel(aep.K, {"theta": aep.theta})
    log.append(_event("EVAL", ok=ok, info=info_eval))
    if not ok:
        return Decision("FAULT", 120, "kernel eval failed", info_eval, log)

    ok, info_audit = ISA_AUDIT_witness(aep.W)
    log.append(_event("AUDIT", ok=ok, info=info_audit))
    if not ok:
        return Decision("FAULT", 140, "witness malformed", info_audit, log)

    kernel_ctx = {
        "kernel_out": info_eval.get("kernel_out", {}),
        "theta": aep.theta,
    }

    for cname in aep.C:
        predicate = predicates.get(cname)
        if predicate is None:
            continue
        ok, ev_check = predicate.check(aep.W, kernel_ctx)
        log.append(_event("CHECK", claim=cname, ok=ok, ev=ev_check))
        if not ok:
            resolved, ev_resolve = predicate.resolve(aep.W, kernel_ctx)
            log.append(_event("RESOLVE", claim=cname, ok=resolved, ev=ev_resolve))
            if not resolved:
                evidence = {"check": ev_check, "resolve": ev_resolve}
                return Decision(
                    "FAULT",
                    predicate.code,
                    f"predicate {cname} failed and unresolved",
                    evidence,
                    log,
                )

    return Decision("PASS", 0, "all predicates satisfied or resolved", {}, log)


class UnityNeutral:
    name = "unity_neutral"
    code = 2001

    def check(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        theta = ctx.get("theta", {})
        quantum = _quantum(theta)
        if "delta_R" in W:
            delta = _to_int_vec(list(W["delta_R"]), quantum)
            l1 = sum(abs(x) for x in delta)
            ok = all(x == 0 for x in delta)
            return ok, {"delta_R_L1_scaled": int(l1), "Q": quantum}
        if "R_pre" in W and "R_post" in W:
            pre = _to_int_vec(list(W["R_pre"]), quantum)
            post = _to_int_vec(list(W["R_post"]), quantum)
            length = min(len(pre), len(post))
            diff = [post[i] - pre[i] for i in range(length)]
            l1 = sum(abs(x) for x in diff)
            ok = all(x == 0 for x in diff)
            return ok, {
                "delta_R_L1_scaled": int(l1),
                "len_pre": len(pre),
                "len_post": len(post),
                "Q": quantum,
            }
        return False, {"reason": "missing resonance fields"}

    def resolve(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        return False, {"reason": "unresolvable at launch"}


class MirrorSafe:
    name = "mirror_safe"
    code = 2002

    def check(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        ok = bool(W.get("mirror_equal", False))
        return ok, {"mirror_equal": ok}

    def resolve(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        return False, {"reason": "unresolvable at launch"}


class BoundaryWindow:
    name = "boundary_window"
    code = 2003

    def check(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        ok = bool(W.get("boundary_ok", False))
        return ok, {"boundary_ok": ok}

    def resolve(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        return False, {"reason": "unresolvable at launch"}


class PhaseWindow:
    name = "phase_window"
    code = 2004

    def check(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        ok = bool(W.get("phase_ok", False))
        return ok, {"phase_ok": ok}

    def resolve(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        return False, {"reason": "unresolvable at launch"}


class ClassesMask:
    name = "classes_mask"
    code = 2005

    def check(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        ok = bool(W.get("classes_ok", False))
        return ok, {"classes_ok": ok}

    def resolve(self, W: Dict[str, Any], ctx: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
        return False, {"reason": "unresolvable at launch"}


DEFAULT_PREDICATES: Dict[str, Predicate] = {
    "unity_neutral": UnityNeutral(),
    "mirror_safe": MirrorSafe(),
    "boundary_window": BoundaryWindow(),
    "phase_window": PhaseWindow(),
    "classes_mask": ClassesMask(),
}
