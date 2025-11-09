"""
Tests for audit_runner module.
"""
import pytest
import json
from pathlib import Path
from multiplicity_core.audit_runner import audit, load_toml, load_ledger


def create_test_ledger(steps: int = 768) -> list:
    """Create a test ledger with fair distribution."""
    ledger = []
    for i in range(steps):
        c = i % 96
        a = i % 6  # Fair distribution across 6 anchors
        ledger.append({
            "kind": "ace_step",
            "status": "committed",
            "entry_id": f"ace_{i}",
            "context": {"class": c, "anchor": a, "step": i},
            "t": i
        })
        # Add corresponding PETC
        ledger.append({
            "kind": "petc",
            "context": {"ace": f"ace_{i}"},
            "t": i
        })
    
    # Add audit entry at step 768
    if steps >= 768:
        ledger.append({
            "kind": "audit",
            "t": 768
        })
    
    return ledger


def test_audit_basic():
    """Test basic audit functionality."""
    ledger = create_test_ledger(768)
    schedule = {"n_classes": 96, "n_anchors": 6}
    bundle = {
        "policy": {"class_skew_tolerance": 1, "anchor_skew_tolerance": 1},
        "intervals": {"audit_every": 768},
        "indexing": {"classes": 96, "anchors": 6}
    }
    
    report = audit(ledger, schedule, bundle)
    
    assert report["total_steps"] == 768
    assert report["fair_classes_ok"] is True
    assert report["fair_anchors_ok"] is True
    assert len(report["missing_petc"]) == 0
    assert report["audit_ok"] is True


def test_audit_class_distribution():
    """Test class distribution checking."""
    ledger = create_test_ledger(96)  # Exactly one per class
    schedule = {"n_classes": 96, "n_anchors": 6}
    bundle = {
        "policy": {"class_skew_tolerance": 0, "anchor_skew_tolerance": 10},
        "intervals": {"audit_every": 768},
        "indexing": {"classes": 96, "anchors": 6}
    }
    
    report = audit(ledger, schedule, bundle)
    
    # Should be exactly fair (1 per class)
    assert report["total_steps"] == 96
    assert report["fair_classes_ok"] is True
    assert all(count == 1 for count in report["by_class"].values())


def test_audit_anchor_distribution():
    """Test anchor distribution checking."""
    ledger = create_test_ledger(600)  # 100 per anchor
    schedule = {"n_classes": 96, "n_anchors": 6}
    bundle = {
        "policy": {"class_skew_tolerance": 10, "anchor_skew_tolerance": 1},
        "intervals": {"audit_every": 768},
        "indexing": {"classes": 96, "anchors": 6}
    }
    
    report = audit(ledger, schedule, bundle)
    
    # Should be exactly fair (100 per anchor)
    assert report["total_steps"] == 600
    assert report["fair_anchors_ok"] is True
    assert all(count == 100 for count in report["by_anchor"].values())


def test_audit_missing_petc():
    """Test detection of missing PETC entries."""
    ledger = []
    # Add ace_steps without corresponding PETC
    for i in range(10):
        ledger.append({
            "kind": "ace_step",
            "status": "committed",
            "entry_id": f"ace_{i}",
            "context": {"class": i % 96, "anchor": i % 6},
            "t": i
        })
    
    schedule = {"n_classes": 96, "n_anchors": 6}
    bundle = {
        "policy": {"class_skew_tolerance": 10, "anchor_skew_tolerance": 10},
        "intervals": {"audit_every": 768},
        "indexing": {"classes": 96, "anchors": 6}
    }
    
    report = audit(ledger, schedule, bundle)
    
    # All 10 ace_steps should be missing PETC
    assert len(report["missing_petc"]) == 10


def test_audit_with_partial_petc():
    """Test with some PETC entries present."""
    ledger = []
    for i in range(10):
        ledger.append({
            "kind": "ace_step",
            "status": "committed",
            "entry_id": f"ace_{i}",
            "context": {"class": i % 96, "anchor": i % 6},
            "t": i
        })
        # Add PETC only for even indices
        if i % 2 == 0:
            ledger.append({
                "kind": "petc",
                "context": {"ace": f"ace_{i}"},
                "t": i
            })
    
    schedule = {"n_classes": 96, "n_anchors": 6}
    bundle = {
        "policy": {"class_skew_tolerance": 10, "anchor_skew_tolerance": 10},
        "intervals": {"audit_every": 768},
        "indexing": {"classes": 96, "anchors": 6}
    }
    
    report = audit(ledger, schedule, bundle)
    
    # 5 odd-indexed ace_steps should be missing PETC
    assert len(report["missing_petc"]) == 5


def test_audit_interval_compliance():
    """Test audit interval compliance checking."""
    ledger = create_test_ledger(2304)  # 3 * 768
    # Remove the default audit entry
    ledger = [e for e in ledger if e.get("kind") != "audit"]
    
    # Add audit entries at correct intervals
    ledger.append({"kind": "audit", "t": 768})
    ledger.append({"kind": "audit", "t": 1536})
    ledger.append({"kind": "audit", "t": 2304})
    
    schedule = {"n_classes": 96, "n_anchors": 6}
    bundle = {
        "policy": {"class_skew_tolerance": 10, "anchor_skew_tolerance": 10},
        "intervals": {"audit_every": 768},
        "indexing": {"classes": 96, "anchors": 6}
    }
    
    report = audit(ledger, schedule, bundle)
    
    assert report["audit_ok"] is True
    assert report["audit_entries"] == 3


def test_audit_missing_interval():
    """Test detection of missing audit intervals."""
    ledger = create_test_ledger(1536)  # 2 * 768
    # Remove all audit entries
    ledger = [e for e in ledger if e.get("kind") != "audit"]
    # Add only one audit entry (missing the second)
    ledger.append({"kind": "audit", "t": 768})
    
    schedule = {"n_classes": 96, "n_anchors": 6}
    bundle = {
        "policy": {"class_skew_tolerance": 10, "anchor_skew_tolerance": 10},
        "intervals": {"audit_every": 768},
        "indexing": {"classes": 96, "anchors": 6}
    }
    
    report = audit(ledger, schedule, bundle)
    
    assert report["audit_ok"] is False
    assert report["audit_entries"] == 1


def test_audit_empty_ledger():
    """Test audit with empty ledger."""
    ledger = []
    schedule = {"n_classes": 96, "n_anchors": 6}
    bundle = {
        "policy": {"class_skew_tolerance": 1, "anchor_skew_tolerance": 1},
        "intervals": {"audit_every": 768},
        "indexing": {"classes": 96, "anchors": 6}
    }
    
    report = audit(ledger, schedule, bundle)
    
    assert report["total_steps"] == 0
    assert "error" in report


def test_load_ledger_list_format():
    """Test loading ledger in list format."""
    ledger_data = [{"kind": "ace_step", "entry_id": "1"}]
    
    with open("test_ledger_list.json", "w") as f:
        json.dump(ledger_data, f)
    
    loaded = load_ledger("test_ledger_list.json")
    assert loaded == ledger_data
    
    # Cleanup
    Path("test_ledger_list.json").unlink()


def test_load_ledger_dict_format():
    """Test loading ledger in dict format with entries key."""
    ledger_data = {"entries": [{"kind": "ace_step", "entry_id": "1"}]}
    
    with open("test_ledger_dict.json", "w") as f:
        json.dump(ledger_data, f)
    
    loaded = load_ledger("test_ledger_dict.json")
    assert loaded == ledger_data["entries"]
    
    # Cleanup
    Path("test_ledger_dict.json").unlink()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
