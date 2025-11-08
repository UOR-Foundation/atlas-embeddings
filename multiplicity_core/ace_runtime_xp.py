"""
ACE Runtime (XP backend): Adaptive Constraint Enforcement with GPU/CPU support.
Integrates with ledger and supports return_numpy mode for host compatibility.
"""
from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Any, Dict, Optional

from multiplicity_core.ace_backend import select_xp
from multiplicity_core.ace_projector_xp import (
    KKTCertificate,
    project_spectral_ball,
    soft_threshold_l1w,
)
from multiplicity_core.ledger import Ledger


class FailClosed(Exception):
    """Exception raised when ACE step is rejected."""
    pass


@dataclass
class ACEConfigXP:
    """Configuration for ACE runtime."""
    lam_l1: float = 0.1  # ℓ1 regularization parameter
    l1_weight_floor: float = 1e-6  # Minimum weight for ℓ1
    kkt_tol: float = 1e-6  # KKT tolerance for convergence
    cauchy_tolerance: float = 1e-15  # Cauchy decrease tolerance


class ACERuntimeXP:
    """ACE Runtime with XP backend support.
    
    Args:
        ledger: Ledger instance for recording steps
        cfg: ACE configuration
        backend: "numpy" or "cupy" (defaults to ACE_BACKEND env)
        return_numpy: If True, return host (numpy) arrays
    """

    def __init__(
        self,
        ledger: Ledger,
        cfg: Optional[ACEConfigXP] = None,
        backend: str | None = None,
        return_numpy: bool = True,
    ):
        self.ledger = ledger
        self.cfg = cfg or ACEConfigXP()
        self.backend = backend
        self.return_numpy = return_numpy
        self.xp, self.np, self.is_gpu = select_xp(backend)
        self._t = 0
        self._last_err: Optional[float] = None

    def _to_host(self, arr):
        """Convert array to host (numpy) if return_numpy is True."""
        if self.return_numpy and self.is_gpu:
            return self.np.asarray(arr.get())
        return self.np.asarray(arr)

    def ace_step(
        self,
        T_t,
        F,
        K_prop,
        w_l1,
        eps_t: float,
        actor_id: str = "default",
        context: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        """Execute one ACE step with KKT and Cauchy checks.
        
        Args:
            T_t: Current state vector
            F: Feedback term
            K_prop: Proposed kernel matrix
            w_l1: ℓ1 weights
            eps_t: Gap parameter
            actor_id: Identifier for the actor
            context: Additional context for logging
        
        Returns:
            Dictionary with T_next, K_proj, ledger_entry_id, and metrics
        
        Raises:
            FailClosed: If ACE step is rejected
        """
        # Compute radius
        radius = 1.0 - eps_t

        # Project kernel to spectral ball
        K_proj, scale, sigma_max = project_spectral_ball(
            K_prop, radius, backend=self.backend
        )

        # Compute candidate
        T_t = self.xp.asarray(T_t)
        F = self.xp.asarray(F)
        T_cand = F + K_proj @ T_t

        # Weighted ℓ1 projection
        w = self.xp.maximum(self.xp.asarray(w_l1, dtype=float), self.cfg.l1_weight_floor)
        z, cert = soft_threshold_l1w(T_cand, self.cfg.lam_l1, w, backend=self.backend)

        # Check Cauchy decrease
        err = float(self.xp.linalg.norm(z - T_t))
        if self._last_err is None:
            self._last_err = err
        cauchy_ok = (err <= self._last_err + 1e-15)

        # Accept if KKT and Cauchy are satisfied
        ok = (cert.residual <= self.cfg.kkt_tol) and cauchy_ok

        # Log to ledger
        entry = {
            "kind": "ace_step",
            "t": self._t,
            "actor_id": actor_id,
            "ts_ms": int(time.time() * 1000),
            "eps_t": float(eps_t),
            "radius": float(radius),
            "sigma_max_before": float(sigma_max),
            "scale_applied": float(scale),
            "kkt_residual": float(cert.residual),
            "kkt_max_stationarity": float(cert.max_stationarity),
            "kkt_max_comp_slack": float(cert.max_comp_slack),
            "active_frac": float(cert.active_frac),
            "cauchy_ok": bool(cauchy_ok),
            "ok": bool(ok),
            "backend": "cupy" if self.is_gpu else "numpy",
            "context": context or {},
        }

        if not ok:
            entry["status"] = "fail_closed"
            eid = self.ledger.append(entry)
            self.ledger.broadcast(eid)
            raise FailClosed(
                f"ACE step rejected: kkt={cert.residual:.2e}, cauchy_ok={cauchy_ok}"
            )

        self._t += 1
        self._last_err = err
        entry["status"] = "committed"
        eid = self.ledger.append(entry)
        self.ledger.broadcast(eid)

        # Return to host if requested
        T_next = self._to_host(z)
        K_out = self._to_host(K_proj)

        return {
            "T_next": T_next,
            "K_proj": K_out,
            "ledger_entry_id": eid,
            "metrics": {
                k: entry[k]
                for k in (
                    "sigma_max_before",
                    "scale_applied",
                    "kkt_residual",
                    "kkt_max_stationarity",
                    "kkt_max_comp_slack",
                    "active_frac",
                    "cauchy_ok",
                    "eps_t",
                    "backend",
                )
            },
        }
