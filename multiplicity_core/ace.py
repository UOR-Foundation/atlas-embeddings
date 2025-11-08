from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, Tuple

@dataclass
class ACEParams:
    X_t: float  # measured magnitude or telemetry bound
    eps_t: float  # gap parameter in (0,1)
    def radius(self) -> float:
        R = 1.0 - float(self.eps_t) - float(self.X_t)
        if R < 0:
            # No feasible point except the origin; clamp to zero radius
            return 0.0
        return R

class ACEProjector:
    """Weighted ℓ1 projection onto S_t = {w : Σ b_p |w_p| ≤ R_t}.

    Implements Euclidean projection via soft‑threshold with a scalar λ.
    Input/outputs are dicts keyed by channel id p.
    """

    @staticmethod
    def project_weighted_l1(w_hat: Dict[int, float], b: Dict[int, float], R: float) -> Tuple[Dict[int, float], float]:
        # Map to y_i = b_i * w_i and project onto ℓ1-ball of radius R, then divide by b_i
        keys = list(w_hat.keys())
        y = [abs(b[k]) * float(w_hat[k]) for k in keys]
        sgn = [1.0 if y[i] >= 0 else -1.0 for i in range(len(keys))]
        abs_y = [abs(v) for v in y]
        L1 = sum(abs_y)
        if R >= L1:
            # Already feasible
            return dict((k, w_hat[k]) for k in keys), max(0.0, R - L1)
        if R <= 0 or not keys:
            return dict((k, 0.0) for k in keys), 0.0
        # Duchi et al. projection onto ℓ1 ball
        # Sort abs_y descending
        pairs = sorted(((abs_y[i], i) for i in range(len(keys))), reverse=True)
        cumsum = 0.0
        tau = 0.0
        rho = -1
        for j, (u, idx) in enumerate(pairs, start=1):
            cumsum += u
            t = (cumsum - R) / j
            if u > t:
                rho = j
                tau = t
        if rho <= 0:
            # Pathological; project to zero
            y_proj = [0.0 for _ in keys]
        else:
            # Threshold
            tau = (sum(pairs[i][0] for i in range(rho)) - R) / rho
            y_proj = [max(v - tau, 0.0) * (1.0 if w_hat[k] >= 0 else -1.0) for v, k in zip(abs_y, keys)]
        # Map back: w_i' = y_i' / b_i
        w = {}
        for (k, vproj) in zip(keys, y_proj):
            bi = abs(b[k])
            if bi <= 0:
                raise ValueError(f"Nonpositive bound b[{k}]={b[k]}")
            w[k] = vproj / bi
        gapLB = R - sum(abs(b[k]) * abs(w[k]) for k in keys)
        return w, gapLB
