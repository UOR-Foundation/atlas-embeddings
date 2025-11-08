"""
Test suite for Atlas ⨯ MTPI watchdog system.
"""
import pytest
import sys
import os

# Add parent directory for module imports
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from multiplicity_core.watchdog import (
    Watchdog,
    CommitWrapper,
    StateStore,
    WatchdogViolation,
    _allclose,
)
from multiplicity_core.ledger import Ledger
from multiplicity_core.proofs import ProofManager


# Minimal numpy-compatible helpers for tests
def array(x):
    return list(x) if not isinstance(x, list) else x


def diag(x):
    n = len(x)
    return [[x[i] if i == j else 0.0 for j in range(n)] for i in range(n)]


def _demo_sigma(actor_id: str, t_ms: int) -> int:
    """Demo sovereignty function: only alice is authorized."""
    return 1 if actor_id == "alice" else 0


def test_state_store_basic():
    """Test StateStore initialization and update."""
    init = array([1.0, 2.0])
    store = StateStore(init)
    
    assert _allclose(store.current, init)
    
    next_state = array([3.0, 4.0])
    store.update(next_state)
    assert _allclose(store.current, next_state)


def test_state_store_rollback():
    """Test StateStore rollback functionality."""
    init = array([1.0, 2.0])
    store = StateStore(init)
    
    store.update(array([3.0, 4.0]))
    store.update(array([5.0, 6.0]))
    
    store.rollback()
    assert _allclose(store.current, array([3.0, 4.0]))
    
    store.rollback()
    assert _allclose(store.current, init)


def test_ledger_basic():
    """Test Ledger append and entry retrieval."""
    ledger = Ledger()
    
    entry1 = {"op": "test", "value": 42}
    entry_id = ledger.append(entry1)
    
    assert isinstance(entry_id, str)
    assert len(ledger.entries) == 1
    assert ledger.entries[0]["op"] == "test"
    assert ledger.entries[0]["value"] == 42
    assert "entry_ms" in ledger.entries[0]
    assert "entry_id" in ledger.entries[0]


def test_proof_manager_basic():
    """Test ProofManager generation and verification."""
    proofs = ProofManager()
    
    payload = {"actor": "alice", "action": "commit"}
    proof = proofs.generate("sovereignty_gate", payload)
    
    assert proof.kind == "sovereignty_gate"
    assert isinstance(proof.proof_id, str)
    assert isinstance(proof.payload_hash, str)
    assert proof.created_ms > 0
    
    # Verify the proof
    assert proofs.verify(proof, payload)
    
    # Wrong payload should fail verification
    wrong_payload = {"actor": "bob", "action": "commit"}
    assert not proofs.verify(proof, wrong_payload)


def test_watchdog_successful_commit():
    """Test successful commit through watchdog."""
    init = array([1.0, 2.0])
    store = StateStore(init)
    
    ledger = Ledger()
    proofs = ProofManager()
    wd = Watchdog(_demo_sigma, ledger, proofs, atol=1e-12)
    wrapper = CommitWrapper(store, wd)
    
    M = diag([2.0, 3.0])
    E = diag([5.0, 7.0])
    
    # Next state should satisfy: M @ x_prev + E @ u = x_next
    # x_prev = [1, 2], M @ x_prev = [2, 6]
    # If x_next = [7, 13], then E @ u = [5, 7], so u = [1, 1]
    next_state = array([7.0, 13.0])
    
    entry = wrapper.commit(next_state, actor_id="alice", M=M, E_alpha=E)
    
    assert entry["actor_id"] == "alice"
    assert _allclose(store.current, next_state)
    assert len(ledger.entries) == 1


def test_watchdog_sovereignty_violation():
    """Test sovereignty violation (unauthorized actor)."""
    init = array([1.0, 2.0])
    store = StateStore(init)
    
    ledger = Ledger()
    proofs = ProofManager()
    wd = Watchdog(_demo_sigma, ledger, proofs, atol=1e-12)
    wrapper = CommitWrapper(store, wd)
    
    M = diag([2.0, 3.0])
    E = diag([5.0, 7.0])
    
    next_state = array([3.0, 4.0])
    
    with pytest.raises(WatchdogViolation) as exc_info:
        wrapper.commit(next_state, actor_id="mallory", M=M, E_alpha=E)
    
    assert "Sovereignty violation" in str(exc_info.value)
    assert wd.locked
    # State should be rolled back to initial
    assert _allclose(store.current, init)


def test_watchdog_lockdown():
    """Test watchdog lockdown functionality."""
    ledger = Ledger()
    proofs = ProofManager()
    wd = Watchdog(_demo_sigma, ledger, proofs, atol=1e-12)
    
    assert not wd.locked
    
    wd.lockdown(True)
    assert wd.locked
    
    wd.lockdown(False)
    assert not wd.locked


def test_commit_wrapper_integration():
    """Test full integration of CommitWrapper with valid transitions."""
    init = array([1.0, 2.0])
    store = StateStore(init)
    
    ledger = Ledger()
    proofs = ProofManager()
    wd = Watchdog(_demo_sigma, ledger, proofs, atol=1e-12)
    wrapper = CommitWrapper(store, wd)
    
    M = diag([2.0, 3.0])
    E = diag([5.0, 7.0])
    
    # First commit
    next_state1 = array([7.0, 13.0])  # M @ [1,2] + E @ [1,1] = [2,6] + [5,7] = [7,13]
    entry1 = wrapper.commit(next_state1, actor_id="alice", M=M, E_alpha=E)
    
    assert _allclose(store.current, next_state1)
    assert len(ledger.entries) == 1
    assert "proofs" in entry1
    assert len(entry1["proofs"]) == 2
    
    # Second commit from new state
    next_state2 = array([19.0, 46.0])  # M @ [7,13] + E @ [1,1] = [14,39] + [5,7] = [19,46]
    entry2 = wrapper.commit(next_state2, actor_id="alice", M=M, E_alpha=E)
    
    assert _allclose(store.current, next_state2)
    assert len(ledger.entries) == 2


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
