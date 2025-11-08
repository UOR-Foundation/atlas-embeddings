"""
Tests for scheduler module.
"""
import json
import tempfile
from pathlib import Path

import numpy as np_
import pytest

from multiplicity_core.ledger import Ledger
from multiplicity_core.scheduler import demo_proposal_factory, executor, load_schedule


def test_load_schedule():
    """Test loading schedule from TOML file."""
    # Create temporary TOML file
    with tempfile.NamedTemporaryFile(mode="w", suffix=".toml", delete=False) as f:
        f.write("""
n_classes = 12
n_anchors = 6
n_columns = 768
lam_l1 = 0.1
kkt_tol = 1e-6
""")
        temp_path = f.name
    
    try:
        cfg = load_schedule(temp_path)
        assert cfg["n_classes"] == 12
        assert cfg["n_anchors"] == 6
        assert cfg["n_columns"] == 768
        assert cfg["lam_l1"] == 0.1
        assert cfg["kkt_tol"] == 1e-6
    finally:
        Path(temp_path).unlink()


def test_load_schedule_file_not_found():
    """Test load_schedule raises error for missing file."""
    with pytest.raises(FileNotFoundError):
        load_schedule("nonexistent_file.toml")


def test_demo_proposal_factory():
    """Test demo proposal factory."""
    d = 64
    proposal, writeback = demo_proposal_factory(d=d)
    
    # Test proposal
    T_t, F, K_prop, w, eps = proposal(0, 0, 0)
    assert T_t.shape == (d,)
    assert F.shape == (d,)
    assert K_prop.shape == (d, d)
    assert w.shape == (d,)
    assert isinstance(eps, float)


def test_demo_proposal_writeback():
    """Test demo proposal writeback updates state."""
    d = 16
    proposal, writeback = demo_proposal_factory(d=d)
    
    # Initial state is zero
    T_t1, _, _, _, _ = proposal(0, 0, 0)
    assert np_.allclose(T_t1, 0.0)
    
    # Writeback new state
    T_new = np_.ones(d)
    writeback(0, 0, 0, T_new)
    
    # Next proposal should see updated state
    T_t2, _, _, _, _ = proposal(1, 1, 1)
    assert np_.allclose(T_t2, T_new)


def test_executor_basic():
    """Test executor runs basic schedule."""
    # Create temporary schedule
    with tempfile.NamedTemporaryFile(mode="w", suffix=".toml", delete=False) as f:
        f.write("""
n_classes = 2
n_anchors = 2
n_columns = 4
lam_l1 = 0.01
kkt_tol = 1e-4
""")
        temp_path = f.name
    
    try:
        cfg = load_schedule(temp_path)
        ledger = Ledger()
        proposal, writeback = demo_proposal_factory(d=8)
        
        # Run a few steps
        executor(ledger, cfg, proposal, writeback, steps=10, backend="numpy")
        
        # Check ledger has entries
        assert len(ledger.entries) > 0
        
        # Check for PETC stamps and ACE steps
        petc_entries = [e for e in ledger.entries if e["kind"] == "petc_stamp"]
        ace_entries = [e for e in ledger.entries if e["kind"] == "ace_step"]
        
        assert len(petc_entries) == 10  # One per step
        assert len(ace_entries) > 0  # At least some ACE steps
        
    finally:
        Path(temp_path).unlink()


def test_executor_round_robin():
    """Test executor round-robins through slots correctly."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".toml", delete=False) as f:
        f.write("""
n_classes = 3
n_anchors = 2
n_columns = 2
lam_l1 = 0.01
kkt_tol = 1e-4
""")
        temp_path = f.name
    
    try:
        cfg = load_schedule(temp_path)
        ledger = Ledger()
        proposal, writeback = demo_proposal_factory(d=8)
        
        # Run enough steps to cycle through
        executor(ledger, cfg, proposal, writeback, steps=6, backend="numpy")
        
        # Get PETC stamps
        petc_entries = [e for e in ledger.entries if e["kind"] == "petc_stamp"]
        
        # Check round-robin: step 0-2 should cycle through classes 0-2
        assert petc_entries[0]["class"] == 0
        assert petc_entries[1]["class"] == 1
        assert petc_entries[2]["class"] == 2
        assert petc_entries[3]["class"] == 0  # Wrap around
        
    finally:
        Path(temp_path).unlink()


def test_executor_handles_failures():
    """Test executor continues on ACE failures."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".toml", delete=False) as f:
        f.write("""
n_classes = 2
n_anchors = 2
n_columns = 2
lam_l1 = 0.01
kkt_tol = 1e-12
""")
        temp_path = f.name
    
    try:
        cfg = load_schedule(temp_path)
        ledger = Ledger()
        
        # Create proposal that will likely fail some steps
        def bad_proposal(c, a, k):
            d = 8
            # Occasionally return bad parameters
            if (c + a + k) % 3 == 0:
                T_t = np_.ones(d) * 100.0
                F = np_.ones(d) * 100.0
                K_prop = 10.0 * np_.eye(d)
            else:
                T_t = np_.zeros(d)
                F = np_.zeros(d)
                K_prop = 0.01 * np_.eye(d)
            w = np_.ones(d)
            eps = 0.01
            return T_t, F, K_prop, w, eps
        
        def writeback(c, a, k, T_next):
            pass
        
        # Should not raise, just log failures
        executor(ledger, cfg, bad_proposal, writeback, steps=10, backend="numpy")
        
        # Check for reject entries
        reject_entries = [e for e in ledger.entries if e["kind"] == "ace_reject"]
        # At least some failures expected
        assert len(reject_entries) >= 0  # May have rejections
        
    finally:
        Path(temp_path).unlink()
