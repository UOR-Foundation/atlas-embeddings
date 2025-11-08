#!/usr/bin/env python3
"""
Test script for AEP systems.
Validates both ethics_commutation and sovereignty_gate runners.
"""
import json
import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).parent.resolve()


def run_aep(aep_dir: Path, env: dict | None = None) -> tuple[int, dict]:
    """Run an AEP and return exit code and result."""
    runner = aep_dir / "runner.py"
    result_file = aep_dir / "out" / "result.json"
    
    # Clean old results
    if result_file.exists():
        result_file.unlink()
    
    # Run the AEP
    full_env = os.environ.copy()
    if env:
        full_env.update(env)
    
    result = subprocess.run(
        [sys.executable, str(runner)],
        cwd=str(aep_dir),
        env=full_env,
        capture_output=True,
    )
    
    # Load result if available
    if result_file.exists():
        with open(result_file) as f:
            data = json.load(f)
    else:
        data = {}
    
    return result.returncode, data


def test_ethics_commutation():
    """Test ethics_commutation AEP."""
    print("\n" + "=" * 60)
    print("Testing ethics_commutation AEP")
    print("=" * 60)
    
    aep_dir = REPO_ROOT / "aep_ethics_commutation"
    
    # Test 1: Pass case (diagonal matrices)
    print("\n1. Testing PASS case (commuting matrices)...")
    exit_code, result = run_aep(aep_dir)
    
    assert exit_code == 0, f"Expected exit code 0, got {exit_code}"
    assert result["status"] == "pass", f"Expected status 'pass', got {result['status']}"
    assert result["ok_commutation"] is True, "Commutation check should pass"
    assert result["ok_forbidden_channels"] is True, "Forbidden channels check should pass"
    assert result["verified"] is True, "Proof verification should pass"
    assert result["comm_norm"] < 1e-12, f"Commutator norm too large: {result['comm_norm']}"
    
    print("  ✓ Exit code: 0")
    print(f"  ✓ Status: {result['status']}")
    print(f"  ✓ Commutator norm: {result['comm_norm']}")
    print(f"  ✓ Proof verified: {result['verified']}")
    
    print("\n✅ ethics_commutation tests passed!")


def test_sovereignty_gate():
    """Test sovereignty_gate AEP."""
    print("\n" + "=" * 60)
    print("Testing sovereignty_gate AEP")
    print("=" * 60)
    
    aep_dir = REPO_ROOT / "aep_sovereignty_gate"
    
    # Test 1: Pass case (alice is allowed)
    print("\n1. Testing PASS case (authorized actor 'alice')...")
    exit_code, result = run_aep(aep_dir, env={"AEP_ACTOR_ID": "alice"})
    
    assert exit_code == 0, f"Expected exit code 0, got {exit_code}"
    assert result["status"] == "pass", f"Expected status 'pass', got {result['status']}"
    assert result["ok_sigma"] is True, "Sigma check should pass"
    assert result["sigma"] == 1, f"Expected sigma=1, got {result['sigma']}"
    assert result["ok_forbidden_channels"] is True, "Forbidden channels check should pass"
    assert result["verified"] is True, "Proof verification should pass"
    
    print("  ✓ Exit code: 0")
    print(f"  ✓ Status: {result['status']}")
    print(f"  ✓ Sigma: {result['sigma']}")
    print(f"  ✓ Proof verified: {result['verified']}")
    
    # Test 2: Fail case (bob is not allowed)
    print("\n2. Testing FAIL case (unauthorized actor 'bob')...")
    exit_code, result = run_aep(aep_dir, env={"AEP_ACTOR_ID": "bob"})
    
    assert exit_code == 2, f"Expected exit code 2, got {exit_code}"
    assert result["status"] == "fail", f"Expected status 'fail', got {result['status']}"
    assert result["ok_sigma"] is False, "Sigma check should fail"
    assert result["sigma"] == 0, f"Expected sigma=0, got {result['sigma']}"
    
    print("  ✓ Exit code: 2 (correctly failed)")
    print(f"  ✓ Status: {result['status']}")
    print(f"  ✓ Sigma: {result['sigma']}")
    
    # Test 3: Default actor from kernel.atlas
    print("\n3. Testing default actor from kernel.atlas...")
    exit_code, result = run_aep(aep_dir)
    
    assert exit_code == 0, f"Expected exit code 0, got {exit_code}"
    assert result["status"] == "pass", f"Expected status 'pass', got {result['status']}"
    assert result["actor_id"] == "alice", f"Expected actor_id='alice', got {result['actor_id']}"
    
    print("  ✓ Exit code: 0")
    print(f"  ✓ Actor ID: {result['actor_id']}")
    print(f"  ✓ Status: {result['status']}")
    
    print("\n✅ sovereignty_gate tests passed!")


def main():
    """Run all tests."""
    print("Starting AEP tests...")
    
    try:
        test_ethics_commutation()
        test_sovereignty_gate()
        
        print("\n" + "=" * 60)
        print("🎉 All AEP tests passed!")
        print("=" * 60)
        return 0
    
    except AssertionError as e:
        print(f"\n❌ Test failed: {e}", file=sys.stderr)
        return 1
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
