from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Dict, List, Tuple, Optional
from decimal import Decimal, ROUND_HALF_EVEN
import tomllib

ALLOWED_CLAIMS = [
    "mirror_safe", "unity_neutral", "boundary_window", "phase_window", "classes_mask"
]

@dataclass(frozen=True)
class BoundaryWindow:
    shape: str                  # e.g., "rect", "cube"
    limits: List[int]           # integer bounds: rect -> [xmin,xmax,ymin,ymax]

@dataclass(frozen=True)
class PhaseWindow:
    phi0: str                   # decimal-as-string, e.g., "0" or "1.57079632679"
    span: str                   # decimal-as-string

@dataclass(frozen=True)
class AEPAttrs:
    claims: List[str]
    boundary_window: Optional[BoundaryWindow]
    phase_window: Optional[PhaseWindow]
    classes_mask: Optional[List[int]]

# ---------- parsing / validation ----------
def load_aep_toml(path: str) -> AEPAttrs:
    with open(path, "rb") as f:
        data = tomllib.load(f)
    claims = list(map(str, data.get("claims", [])))
    for c in claims:
        if c not in ALLOWED_CLAIMS:
            raise ValueError(f"unknown claim: {c}")
    bw = None
    if "boundary_window" in data:
        bw_raw = data["boundary_window"]
        shape = str(bw_raw.get("shape", ""))
        limits = list(map(int, bw_raw.get("limits", [])))
        if not shape or not limits:
            raise ValueError("boundary_window requires shape and limits")
        bw = BoundaryWindow(shape=shape, limits=limits)
    pw = None
    if "phase_window" in data:
        pw_raw = data["phase_window"]
        phi0 = str(pw_raw.get("phi0", "0"))
        span = str(pw_raw.get("span", "0"))
        pw = PhaseWindow(phi0=phi0, span=span)
    cm = None
    if "classes_mask" in data:
        cm = list(map(int, data.get("classes_mask", [])))
    return AEPAttrs(claims=claims, boundary_window=bw, phase_window=pw, classes_mask=cm)

def kernel_attrs_from_attrs(attrs: AEPAttrs) -> Dict[str, Any]:
    out: Dict[str, Any] = {"claims": attrs.claims}
    if attrs.boundary_window:
        out["boundary_window"] = {
            "shape": attrs.boundary_window.shape,
            "limits": attrs.boundary_window.limits,
        }
    if attrs.phase_window:
        out["phase_window"] = {
            "phi0": attrs.phase_window.phi0,
            "span": attrs.phase_window.span,
        }
    if attrs.classes_mask is not None:
        out["classes_mask"] = attrs.classes_mask
    return out

# ---------- fixed-point helpers (no-float) ----------
def _Q(theta: Dict[str, Any]) -> int:
    q = int(theta.get("Q", 1000000))
    return q if q > 0 else 1000000

def _to_scaled_ints(vals: List[Any], Q: int) -> List[int]:
    out: List[int] = []
    for v in vals:
        d = (Decimal(str(v)) * Decimal(Q)).to_integral_value(rounding=ROUND_HALF_EVEN)
        out.append(int(d))
    return out

def _dec_str_to_int(s: str, Q: int) -> int:
    return int((Decimal(s) * Decimal(Q)).to_integral_value(rounding=ROUND_HALF_EVEN))

# ---------- witness normalization and canonical checks ----------
def normalize_witness(W: Dict[str, Any], theta: Dict[str, Any]) -> Dict[str, Any]:
    """Ensure canonical fields exist and are integer-scaled."""
    Q = _Q(theta)
    out = dict(W)
    # delta_R
    if "delta_R" not in out and ("R_pre" in out and "R_post" in out):
        pre = _to_scaled_ints(list(out["R_pre"]), Q)
        post = _to_scaled_ints(list(out["R_post"]), Q)
        n = min(len(pre), len(post))
        out["delta_R"] = [post[i] - pre[i] for i in range(n)]
    # optional scaling for probes if present
    if "B_probes" in out and isinstance(out["B_probes"], list):
        # leave as provided; boundary check consumes integer limits
        pass
    if "P_probes" in out and isinstance(out["P_probes"], list):
        # if probes contain "phi" as string, scale and stash as "phi_Q"
        scaled = []
        for p in out["P_probes"]:
            if isinstance(p, dict) and "phi" in p:
                scaled.append({**p, "phi_Q": _dec_str_to_int(str(p["phi"]), Q)})
            else:
                scaled.append(p)
        out["P_probes"] = scaled
    out["Q"] = Q
    return out

def canonical_unity_neutral(W: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
    if "delta_R" not in W:
        return False, {"reason": "missing delta_R"}
    s = sum(abs(int(v)) for v in W["delta_R"])
    return s == 0, {"delta_R_L1_scaled": int(s), "Q": int(W.get("Q", 0))}

def canonical_boundary_window(W: Dict[str, Any], attrs: AEPAttrs) -> Tuple[bool, Dict[str, Any]]:
    if not attrs.boundary_window:
        return True, {"skipped": True}
    limits = attrs.boundary_window.limits
    # Expect optional W["footprint"] as [xmin,xmax,ymin,ymax] or a list of integer boxes
    fp = W.get("footprint", None)
    if fp is None:
        return False, {"reason": "missing footprint"}
    def inside(box: List[int]) -> bool:
        if len(limits) != 4 or len(box) != 4:
            return False
        xmin,xmax,ymin,ymax = box
        Lxmin,Lxmax,Lymin,Lymax = limits
        return (Lxmin <= xmin <= Lxmax) and (Lxmin <= xmax <= Lxmax) and (Lymin <= ymin <= Lymax) and (Lymin <= ymax <= Lymax)
    if isinstance(fp, list) and all(isinstance(v, int) for v in fp):
        ok = inside(fp)
        return ok, {"footprint": fp, "limits": limits}
    if isinstance(fp, list) and all(isinstance(v, list) for v in fp):
        oks = [inside(b) for b in fp]
        ok = all(oks)
        return ok, {"count": len(fp), "violations": int(len([z for z in oks if not z]))}
    return False, {"reason": "unsupported footprint type"}

def canonical_phase_window(W: Dict[str, Any], attrs: AEPAttrs, theta: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
    if not attrs.phase_window:
        return True, {"skipped": True}
    Q = _Q(theta)
    phi0_Q = _dec_str_to_int(attrs.phase_window.phi0, Q)
    span_Q = _dec_str_to_int(attrs.phase_window.span, Q)
    lo, hi = phi0_Q, phi0_Q + span_Q
    # Expect either W["phase_values"] as list of str/int or P_probes with phi_Q
    vals: List[int] = []
    if "phase_values" in W:
        vals = _to_scaled_ints(list(W["phase_values"]), Q)
    elif "P_probes" in W:
        for p in W["P_probes"]:
            if isinstance(p, dict) and "phi_Q" in p:
                vals.append(int(p["phi_Q"]))
    else:
        return False, {"reason": "missing phase probes"}
    ok = all(lo <= v <= hi for v in vals)
    return ok, {"lo_Q": lo, "hi_Q": hi, "count": len(vals)}

def canonical_mirror_safe(W: Dict[str, Any]) -> Tuple[bool, Dict[str, Any]]:
    ok = bool(W.get("mirror_equal", False))
    return ok, {"mirror_equal": ok}

def canonical_classes_mask(W: Dict[str, Any], attrs: AEPAttrs) -> Tuple[bool, Dict[str, Any]]:
    if attrs.classes_mask is None:
        return True, {"skipped": True}
    ok = bool(W.get("classes_ok", False))
    return ok, {"classes_ok": ok}

def prepare_claims_attrs_witness(aep_toml_path: str, W_in: Dict[str, Any], theta: Dict[str, Any]) -> Tuple[Dict[str, Any], Dict[str, Any], Dict[str, Any]]:
    """
    Returns: (attrs_dict_for_ASSERT, kernel_attrs_dict, W_normalized_with_booleans)
    Sets boundary_ok and phase_ok if claims include them.
    """
    attrs = load_aep_toml(aep_toml_path)
    attrs_dict = kernel_attrs_from_attrs(attrs)
    W = normalize_witness(W_in, theta)
    # populate canonical booleans when claimed
    if "unity_neutral" in attrs.claims:
        ok, ev = canonical_unity_neutral(W); W["unity_ok"] = ok; W["unity_ev"] = ev
    if "mirror_safe" in attrs.claims:
        ok, ev = canonical_mirror_safe(W); W["mirror_equal"] = ok; W["mirror_ev"] = ev
    if "boundary_window" in attrs.claims:
        ok, ev = canonical_boundary_window(W, attrs); W["boundary_ok"] = ok; W["boundary_ev"] = ev
    if "phase_window" in attrs.claims:
        ok, ev = canonical_phase_window(W, attrs, theta); W["phase_ok"] = ok; W["phase_ev"] = ev
    if "classes_mask" in attrs.claims:
        ok, ev = canonical_classes_mask(W, attrs); W["classes_ok"] = ok; W["classes_ev"] = ev
    return attrs_dict, attrs_dict, W
