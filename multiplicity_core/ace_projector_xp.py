"""
ACE Projector (XP backend): weighted ℓ1 prox + spectral-norm projection using numpy or cupy.
Same interface as cpu version.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Tuple

from multiplicity_core.ace_backend import select_xp


@dataclass
class KKTCertificate:
    """KKT certificate for ℓ1 proximal operator."""
    residual: float
    max_stationarity: float
    max_comp_slack: float
    active_frac: float


def _norm(xp, A):
    """Compute Frobenius norm."""
    return float(xp.linalg.norm(A))


def soft_threshold_l1w(y, lam: float, w, *, backend: str | None = None):
    """Weighted soft-threshold (ℓ1 prox).
    
    Args:
        y: Input array
        lam: Regularization parameter
        w: Weight array (same shape as y)
        backend: "numpy" or "cupy" (optional)
    
    Returns:
        Tuple of (z, cert) where z is the proximal output and cert is KKT certificate
    """
    xp, np, is_gpu = select_xp(backend)
    y = xp.asarray(y)
    w = xp.asarray(w)
    assert y.shape == w.shape
    ay = xp.abs(y)
    thr = lam * w
    z = xp.sign(y) * xp.maximum(ay - thr, 0.0)

    # KKT
    J = (z != 0)
    stat = xp.zeros_like(z, dtype=float)
    slack = xp.zeros_like(z, dtype=float)
    stat[J] = xp.abs(ay[J] - xp.abs(z[J]) - thr[J])
    slack[~J] = xp.maximum(ay[~J] - thr[~J], 0.0)
    res = float(max(stat.max().item() if stat.size else 0.0,
                    slack.max().item() if slack.size else 0.0))
    cert = KKTCertificate(
        residual=res,
        max_stationarity=float(stat.max().item() if stat.size else 0.0),
        max_comp_slack=float(slack.max().item() if slack.size else 0.0),
        active_frac=float((J.sum() / z.size).item()),
    )
    return z, cert


def kkt_residual_l1w(y, z, lam: float, w, *, backend: str | None = None) -> float:
    """Compute KKT residual for weighted ℓ1 prox.
    
    Args:
        y: Original input
        z: Proximal output
        lam: Regularization parameter
        w: Weight array
        backend: "numpy" or "cupy" (optional)
    
    Returns:
        Maximum KKT residual
    """
    xp, np, _ = select_xp(backend)
    y = xp.asarray(y)
    z = xp.asarray(z)
    w = xp.asarray(w)
    ay = xp.abs(y)
    thr = lam * w
    J = (z != 0)
    r_active = xp.abs(ay[J] - xp.abs(z[J]) - thr[J]) if J.any() else xp.asarray([0.0])
    r_inactive = xp.maximum(ay[~J] - thr[~J], 0.0) if (~J).any() else xp.asarray([0.0])
    return float(max(r_active.max().item(), r_inactive.max().item()))


def project_spectral_ball(K, radius: float, *, backend: str | None = None):
    """Project matrix K onto spectral ball of given radius.
    
    Args:
        K: Input matrix
        radius: Spectral radius constraint
        backend: "numpy" or "cupy" (optional)
    
    Returns:
        Tuple of (K_proj, scale, sigma_max) where:
        - K_proj is the projected matrix
        - scale is the scaling factor applied
        - sigma_max is the original largest singular value
    """
    xp, np, _ = select_xp(backend)
    K = xp.asarray(K)
    assert radius >= 0.0
    if K.size == 0:
        return K, 1.0, 0.0
    # Try SVD, fall back to power iteration if not available/performance constrained
    try:
        s = xp.linalg.svd(K, compute_uv=False)
        sigma_max = float(s[0].item())
    except Exception:
        # Power iteration on K^T K
        v = xp.random.randn(K.shape[1])
        v /= xp.linalg.norm(v) + 1e-12
        for _ in range(50):
            v = K.T @ (K @ v)
            v /= xp.linalg.norm(v) + 1e-12
        sigma_max = float(xp.sqrt(v @ (K.T @ (K @ v))).item())

    if sigma_max <= radius + 1e-15:
        return K, 1.0, sigma_max
    scale = radius / (sigma_max + 1e-30)
    return K * scale, float(scale), sigma_max
