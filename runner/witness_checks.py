from __future__ import annotations

import math
from collections.abc import Sequence


def _to_vector(values: Sequence[float]) -> list[float]:
    return [float(v) for v in values]


def _norm(values: Sequence[float]) -> float:
    return math.sqrt(sum(float(v) ** 2 for v in values))


def check_unity_neutral(R_pre=None, R_post=None, delta_R=None, tol=1e-12):
    if delta_R is None:
        if R_pre is None or R_post is None:
            return False, {"reason": "missing resonance"}
        delta = [float(b) - float(a) for a, b in zip(R_pre, R_post)]
    else:
        delta = _to_vector(delta_R)
    ok = all(abs(v) <= tol for v in delta)
    return ok, {"delta_R_norm": float(_norm(delta))}


def check_mirror_safe(kernel_eval, conjugator, probes, tol=1e-12):
    y = _to_vector(kernel_eval(probes))
    ym = _to_vector(conjugator(lambda u: kernel_eval(conjugator(u)), probes))
    diff = [a - b for a, b in zip(y, ym)]
    ok = all(abs(v) <= tol for v in diff)
    return ok, {"diff_norm": float(_norm(diff))}


def check_boundaries(footprint_pts, window_pred):
    ok = bool(window_pred(footprint_pts))
    return ok, {"count": len(footprint_pts)}


def check_phase(series, phi0, span):
    seq = _to_vector(series)
    mod = [((value - phi0) % (2 * math.pi)) for value in seq]
    ok = all(0.0 <= value <= span for value in mod)
    return ok, {"count": len(seq)}
