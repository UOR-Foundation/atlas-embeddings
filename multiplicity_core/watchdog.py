"""
Atlas ⨯ MTPI — Watchdog

Runtime enforcement of sovereignty and ethics constraints.
Lockdown→Rollback→Broadcast on violation.
"""
from __future__ import annotations

import json
import time
from typing import Any, Callable, Dict, List, Optional, Union

# We accept numpy arrays but work with lists internally to avoid the stub numpy issue
ArrayLike = Union[List[float], Any]  # Any for numpy.ndarray compatibility

from .ledger import Ledger
from .proofs import ProofManager, Proof


def _now_epoch_ms() -> int:
    return int(time.time() * 1000)


class WatchdogViolation(Exception):
    """Raised when a sovereignty or ethics constraint is violated."""
    pass


def _to_list(arr: ArrayLike) -> List[float]:
    """Convert array-like to list."""
    if hasattr(arr, 'tolist'):
        return arr.tolist()
    elif isinstance(arr, list):
        # Handle nested lists (matrices)
        if arr and isinstance(arr[0], (list, tuple)) or hasattr(arr[0], 'tolist'):
            return [_to_list(row) for row in arr]
        return list(arr)
    else:
        return list(arr)


def _allclose(a: List[float], b: List[float], atol: float = 1e-8) -> bool:
    """Check if two arrays are element-wise equal within a tolerance."""
    if len(a) != len(b):
        return False
    return all(abs(x - y) <= atol for x, y in zip(a, b))


def _matmul(M: List[List[float]], v: List[float]) -> List[float]:
    """Matrix-vector multiplication."""
    result = []
    for row in M:
        result.append(sum(m * x for m, x in zip(row, v)))
    return result


def _subtract(a: List[float], b: List[float]) -> List[float]:
    """Element-wise subtraction."""
    return [x - y for x, y in zip(a, b)]


def _lstsq(A: List[List[float]], b: List[float], atol: float = 1e-12) -> tuple[List[float], List[float]]:
    """
    Simplified least squares solver for A @ x = b.
    Returns (x, residual) where residual is the vector A @ x - b.
    This is a simplified implementation that assumes A is invertible or over-determined.
    """
    # For diagonal matrices (common case), we can solve directly
    m = len(A)
    n = len(A[0]) if A else 0
    
    if m == n:
        # Square matrix - try direct solve
        # For diagonal matrices, this is trivial
        x = []
        for i in range(n):
            if abs(A[i][i]) > atol:
                x.append(b[i] / A[i][i])
            else:
                # Column is zero or near-zero, can't solve
                x.append(0.0)
        
        # Compute residual
        residual = _subtract(_matmul(A, x), b)
        return x, residual
    else:
        # Over-determined or under-determined system
        # For our use case, we'll use a simple pseudo-inverse approach
        # This is a placeholder - in practice, you'd use a proper numerical library
        x = [0.0] * n
        residual = b[:]
        return x, residual


class StateStore:
    """
    Mutable state container with rollback capability.
    """

    def __init__(self, initial_state: ArrayLike):
        self._current = _to_list(initial_state)
        self._history = [_to_list(initial_state)]

    @property
    def current(self) -> List[float]:
        return self._current[:]

    def update(self, new_state: ArrayLike) -> None:
        new_list = _to_list(new_state)
        self._history.append(new_list[:])
        self._current = new_list[:]

    def rollback(self) -> None:
        if len(self._history) > 1:
            self._history.pop()
            self._current = self._history[-1][:]


class Watchdog:
    """
    Sovereignty + Ethics enforcement layer.

    Validates that:
      1. Sovereignty: actor_id can only touch dimensions where sigma(actor_id, t) = 1.
      2. Ethics: M @ x_prev + E_alpha @ u = x_next must hold within tolerance.
    """

    def __init__(
        self,
        sigma: Callable[[str, int], int],
        ledger: Ledger,
        proofs: ProofManager,
        atol: float = 1e-12,
    ):
        self.sigma = sigma
        self.ledger = ledger
        self.proofs = proofs
        self.atol = atol
        self.locked = False

    def lockdown(self, val: bool) -> None:
        """Lock or unlock the watchdog."""
        self.locked = val

    def enforce(
        self,
        store: StateStore,
        next_state: ArrayLike,
        *,
        actor_id: str,
        M: ArrayLike,
        E_alpha: ArrayLike,
        now_ms: Optional[int] = None,
    ) -> Dict[str, Any]:
        """
        Enforces sovereignty and ethics, then commits next_state to store.

        Returns ledger entry dict on success.
        Raises WatchdogViolation on failure (after lockdown→rollback→broadcast).
        """
        t_ms = now_ms if now_ms is not None else _now_epoch_ms()
        x_prev = store.current
        x_next = _to_list(next_state)
        M_list = _to_list(M)
        E_list = _to_list(E_alpha)

        # 1. Sovereignty check
        sigma_val = self.sigma(actor_id, t_ms)
        if sigma_val != 1:
            # Actor is not authorized at this time
            self._handle_violation(
                store,
                f"Sovereignty violation: actor={actor_id}, sigma={sigma_val}, t_ms={t_ms}",
                actor_id,
                t_ms,
            )

        # 2. Ethics check: verify M @ x_prev + E_alpha @ u = x_next
        # We'll assume u is implicitly encoded via the difference:
        # u = E_alpha^{-1} @ (x_next - M @ x_prev)
        # For simplicity, we just check if x_next is close to M @ x_prev + E_alpha @ (something)
        # or more directly: x_next ≈ M @ x_prev + E_alpha @ u for some u.
        # A more robust check would solve for u and verify it's valid.
        
        # Simplified ethics check: verify that the transition is plausible
        # by checking if (x_next - M @ x_prev) is in the column space of E_alpha
        predicted = _matmul(M_list, x_prev)
        residual = _subtract(x_next, predicted)
        
        # Check if residual is approximately in column space of E_alpha
        # This is a simplified check - a more rigorous version would use pseudoinverse
        try:
            # Try to solve E_alpha @ u = residual
            u, error = _lstsq(E_list, residual, self.atol)
            # Check that the reconstruction is close enough
            E_u = _matmul(E_list, u)
            reconstructed = [p + e for p, e in zip(predicted, E_u)]
            if not _allclose(x_next, reconstructed, atol=self.atol):
                self._handle_violation(
                    store,
                    f"Ethics violation: state transition not valid for actor={actor_id}",
                    actor_id,
                    t_ms,
                )
        except Exception as e:
            self._handle_violation(
                store,
                f"Ethics violation: cannot verify transition for actor={actor_id}: {e}",
                actor_id,
                t_ms,
            )

        # 3. Generate proofs
        payload = {
            "actor_id": actor_id,
            "t_ms": t_ms,
            "x_prev": x_prev,
            "x_next": x_next,
        }
        sov_proof = self.proofs.generate("sovereignty_gate", payload)
        eth_proof = self.proofs.generate("ethics_commutation", payload)

        # 4. Commit to store
        store.update(x_next)

        # 5. Append to ledger
        entry = {
            "actor_id": actor_id,
            "t_ms": t_ms,
            "x_prev": x_prev,
            "x_next": x_next,
            "M": M_list,
            "E_alpha": E_list,
            "proofs": [sov_proof.proof_id, eth_proof.proof_id],
        }
        entry_id = self.ledger.append(entry)

        # 6. Broadcast
        self.ledger.broadcast(entry_id)

        return entry

    def _handle_violation(
        self, store: StateStore, reason: str, actor_id: str, t_ms: int
    ) -> None:
        """
        Violation path: Lockdown → Rollback → Broadcast → Raise
        """
        # 1. Lockdown
        self.lockdown(True)

        # 2. Rollback
        store.rollback()

        # 3. Broadcast violation
        violation_entry = {
            "type": "violation",
            "reason": reason,
            "actor_id": actor_id,
            "t_ms": t_ms,
        }
        entry_id = self.ledger.append(violation_entry)
        self.ledger.broadcast(entry_id)

        # 4. Raise exception
        raise WatchdogViolation(reason)


class CommitWrapper:
    """
    Convenience wrapper for StateStore + Watchdog.

    Usage:
        wrapper = CommitWrapper(store, watchdog)
        wrapper.commit(next_state, actor_id="alice", M=M, E_alpha=E)
    """

    def __init__(self, store: StateStore, watchdog: Watchdog):
        self.store = store
        self.watchdog = watchdog

    def commit(
        self,
        next_state: ArrayLike,
        *,
        actor_id: str,
        M: ArrayLike,
        E_alpha: ArrayLike,
        now_ms: Optional[int] = None,
    ) -> Dict[str, Any]:
        return self.watchdog.enforce(
            self.store, next_state, actor_id=actor_id, M=M, E_alpha=E_alpha, now_ms=now_ms
        )


# ============ Example harness ============


def _demo_sigma(actor_id: str, t_ms: int) -> int:
    return 1 if actor_id == "alice" else 0


def _example():
    # Try to import numpy, fall back to local stub
    try:
        import sys
        sys.path.insert(0, "/home/runner/.local/lib/python3.12/site-packages")
        import numpy as np
    except:
        # Fall back to stub or lists
        class np:  # type: ignore
            @staticmethod
            def array(x):
                return list(x) if not isinstance(x, list) else x
            
            @staticmethod
            def diag(x):
                n = len(x)
                return [[x[i] if i == j else 0.0 for j in range(n)] for i in range(n)]
    
    print("-- Atlas ⨯ MTPI watchdog demo --")

    init = np.array([1.0, 2.0])
    store = StateStore(init)

    ledger = Ledger()
    proofs = ProofManager()
    wd = Watchdog(_demo_sigma, ledger, proofs, atol=1e-12)
    wrapper = CommitWrapper(store, wd)

    M = np.diag([2.0, 3.0])
    E = np.diag([5.0, 7.0])

    next_state = np.array([1.5, 1.5])
    ok_entry = wrapper.commit(next_state, actor_id="alice", M=M, E_alpha=E)
    print("commit ok:", json.dumps(ok_entry, indent=2))

    M2 = [[0.0, 1.0], [0.0, 0.0]]
    E2 = [[0.0, 0.0], [1.0, 0.0]]

    try:
        wrapper.commit([9.0, 9.0], actor_id="mallory", M=M2, E_alpha=E2)
    except WatchdogViolation as e:
        print("violation:", str(e))
        print("lockdown:", wd.locked)

    wd.lockdown(False)

    print("ledger entries:")
    for ent in ledger.entries:
        print(json.dumps(ent, indent=2))


if __name__ == "__main__":
    _example()
