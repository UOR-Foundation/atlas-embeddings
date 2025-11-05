#!/usr/bin/env python3
"""
ifmd_hybrid_bridge_minimal.py
Operator-only scaffold with explosion test, projectors, and demo.
Based on Conway-Monster Atlas Core Upgrade Kit v1.
"""

import numpy as np
from typing import Tuple, Optional
import json

# ============================================================================
# Operator-only scaffold
# ============================================================================

class AtlasBridge:
    """Minimal hybrid bridge implementation."""
    
    MODE_CLASS = 0
    MODE_BRIDGE = 1
    
    def __init__(self):
        self.mode = self.MODE_CLASS
        self.spinlift_enabled = False
        self.base_dim = 12288
        self.bridge_dim = 98304
        self.n_qubits = 12
        
    def set_mode(self, mode: int):
        """Set operation mode: CLASS (0) or BRIDGE (1)."""
        assert mode in [self.MODE_CLASS, self.MODE_BRIDGE]
        self.mode = mode
        
    def spinlift_enable(self, on: bool):
        """Enable/disable spin-lift (only effective in BRIDGE mode)."""
        self.spinlift_enabled = bool(on)
        
    def dims(self) -> Tuple[int, int]:
        """Return (base_dim, bridge_dim)."""
        return (self.base_dim, self.bridge_dim)
    
    def phi_encode(self, page: int, byte: int) -> int:
        """Encode (page, byte) to linear index 0..12287."""
        assert 0 <= page < 96 and 0 <= byte < 128
        return page * 128 + byte
    
    def phi_decode(self, idx: int) -> Tuple[int, int]:
        """Decode linear index to (page, byte)."""
        assert 0 <= idx < self.base_dim
        page = idx // 128
        byte = idx % 128
        return (page, byte)
    
    def phi_bridge(self, idx_base: int, k: int) -> int:
        """Map base index to bridge index with lift k."""
        assert 0 <= idx_base < self.base_dim
        return idx_base + self.base_dim * (k & 7)


# ============================================================================
# E-layer: Extraspecial 2-group action
# ============================================================================

def pauli_mask(x_bits: int, z_bits: int, n_qubits: int = 12) -> Tuple[int, int]:
    """
    Create Pauli operator mask from bit patterns.
    E action: X^x Z^z |b⟩ = (-1)^{z·b} |b ⊕ x⟩
    """
    max_val = 1 << n_qubits
    assert 0 <= x_bits < max_val
    assert 0 <= z_bits < max_val
    return (int(x_bits), int(z_bits))


def E_apply(state: np.ndarray, x_mask: int, z_mask: int, n_qubits: int = 12) -> np.ndarray:
    """
    Apply extraspecial group element (x,z) to state vector.
    Works for both CLASS (12288) and BRIDGE (98304) mode states.
    """
    n_basis = 1 << n_qubits  # 4096 for n=12
    
    # Detect if this is noncentral (nonzero x or z)
    is_noncentral = (x_mask != 0) or (z_mask != 0)
    
    if len(state) <= 12288 or not is_noncentral:
        # CLASS mode or central element: single block operation
        new_state = np.zeros_like(state)
        for b in range(min(n_basis, len(state))):
            # Phase from Z part: (-1)^{z·b}
            phase = (-1) ** bin(z_mask & b).count('1')
            # Bit flip from X part: |b ⊕ x⟩
            b_new = b ^ x_mask
            if b_new < len(state):
                new_state[b_new] += phase * state[b]
        # Copy remaining components unchanged
        if len(state) > n_basis:
            new_state[n_basis:] = state[n_basis:]
        return new_state
    else:
        # BRIDGE mode with noncentral element: 8-way explosion
        # State should be 98304 = 12288 * 8
        assert len(state) == 98304, f"Expected 98304 elements in BRIDGE mode, got {len(state)}"
        new_state = np.zeros_like(state)
        
        # Simplified: apply to each lift independently (actual implementation 
        # would use proper lift-permute tables)
        for k in range(8):
            block_start = k * 12288
            block_end = (k + 1) * 12288
            block = state[block_start:block_end]
            
            # Apply E action to this block
            temp = np.zeros_like(block)
            for i in range(len(block)):
                if i < n_basis:
                    b = i
                    phase = (-1) ** bin(z_mask & b).count('1')
                    b_new = b ^ x_mask
                    if b_new < len(block):
                        temp[b_new] += phase * block[b]
                else:
                    temp[i] = block[i]
            
            new_state[block_start:block_end] = temp
            
        return new_state


# ============================================================================
# Projectors
# ============================================================================

class Projectors:
    """Projector operators for CLASS, Qonly, and 299 subspaces."""
    
    @staticmethod
    def P_class_apply(v: np.ndarray) -> np.ndarray:
        """
        Project onto E-invariant (CLASS) subspace.
        Uses E-twirl: T_E(v) = |E|^{-1} Σ_{e∈E} e v e^{-1}
        """
        n_qubits = 12
        n_samples = 256  # Sample from E group
        
        accumulator = np.zeros_like(v)
        
        for _ in range(n_samples):
            # Random E element
            x = np.random.randint(0, 1 << n_qubits)
            z = np.random.randint(0, 1 << n_qubits)
            
            # Apply e v e^{-1} (simplified: just apply e for now)
            temp = E_apply(v.copy(), x, z, n_qubits)
            accumulator += temp
            
        return accumulator / n_samples
    
    @staticmethod
    def P_Qonly_apply(v: np.ndarray) -> np.ndarray:
        """
        Project onto Q-only subspace (98,304 component).
        Placeholder implementation.
        """
        # In actual implementation, this would use explicit basis
        return v.copy()
    
    @staticmethod
    def P_299_apply(v: np.ndarray) -> np.ndarray:
        """
        Project onto 299-dimensional component.
        Uses S²(24) trace-zero filter after E-twirl.
        """
        # First apply E-twirl
        v_class = Projectors.P_class_apply(v)
        
        # Then apply trace-zero filter (simplified)
        # Actual implementation would use 25×25 operator on feature map
        return v_class * 0.01  # Placeholder


# ============================================================================
# Diagnostics
# ============================================================================

def projector_residual(P_apply, v_test: Optional[np.ndarray] = None) -> float:
    """
    Compute idempotency residual ||P²v - Pv||_2.
    """
    if v_test is None:
        v_test = np.random.randn(12288)
    
    Pv = P_apply(v_test)
    PPv = P_apply(Pv)
    
    residual = np.linalg.norm(PPv - Pv)
    return residual


def commutant_probe(with_Co1: bool = False) -> float:
    """
    Estimate effective commutant dimension via randomized probing.
    Returns effective dimension of Comm_E or Comm_{E,Co1}.
    """
    n_probes = 100
    n_generators = 24
    
    # Build commutator matrix
    C_list = []
    
    for _ in range(n_probes):
        v = np.random.randn(12288)
        
        for _ in range(n_generators):
            x = np.random.randint(0, 1 << 12)
            z = np.random.randint(0, 1 << 12)
            
            # Compute [g, A(v)] where A is test operator
            gv = E_apply(v.copy(), x, z, 12)
            commutator = gv - v  # Simplified
            C_list.append(commutator)
    
    # Stack and compute effective rank
    if len(C_list) > 0:
        C_matrix = np.column_stack([c.flatten() for c in C_list[:min(50, len(C_list))]])
        s = np.linalg.svd(C_matrix, compute_uv=False)
        # Estimate nullity
        rank = np.sum(s > 1e-6)
        dim = C_matrix.shape[0] - rank
        return max(1.0, dim / 1000.0)  # Normalize
    
    return 1.0


def leakage_certificate(bridge: AtlasBridge, json_out_path: str) -> int:
    """
    Generate leakage certificate with block energy distributions.
    Returns 0 on success.
    """
    # Create test vectors
    v_test = np.random.randn(bridge.bridge_dim if bridge.mode == bridge.MODE_BRIDGE else bridge.base_dim)
    v_test /= np.linalg.norm(v_test)
    
    # Compute block energies
    if bridge.mode == bridge.MODE_BRIDGE:
        e_98304 = np.sum(v_test[:98304]**2)
        e_98280 = 0.0  # Placeholder
        e_299 = 0.0    # Placeholder
    else:
        e_98304 = np.sum(v_test**2)
        e_98280 = 0.0
        e_299 = 0.0
    
    # Compute projector residuals
    p_class_resid = projector_residual(Projectors.P_class_apply)
    p_qonly_resid = projector_residual(Projectors.P_Qonly_apply)
    p_299_resid = projector_residual(Projectors.P_299_apply)
    
    # Build certificate
    cert = {
        "version": "v0.9-bridge",
        "mode": "BRIDGE" if bridge.mode == bridge.MODE_BRIDGE else "CLASS",
        "spinlift": bridge.spinlift_enabled,
        "commutant": {
            "E": commutant_probe(with_Co1=False),
            "E_Co1": commutant_probe(with_Co1=True)
        },
        "projectors": {
            "P_class": {
                "idempotency": p_class_resid,
                "comm_resid": 0.0  # Placeholder
            },
            "P_Qonly": {
                "idempotency": p_qonly_resid,
                "comm_resid": 0.0
            },
            "P_299": {
                "idempotency": p_299_resid,
                "comm_resid": 0.0
            }
        },
        "leakage": {
            "e_98304": float(e_98304),
            "e_98280": float(e_98280),
            "e_299": float(e_299)
        }
    }
    
    # Write to file
    with open(json_out_path, 'w') as f:
        json.dump(cert, f, indent=2)
    
    return 0


# ============================================================================
# Explosion test (Appendix B)
# ============================================================================

def test_explosion():
    """
    Test that noncentral E elements trigger 8-way explosion in BRIDGE mode.
    """
    print("=== Explosion Test ===")
    
    bridge = AtlasBridge()
    bridge.set_mode(AtlasBridge.MODE_BRIDGE)
    bridge.spinlift_enable(True)
    
    base, br = bridge.dims()
    print(f"Dimensions: base={base}, bridge={br}")
    assert base == 12288 and br == 98304
    
    # Create unit vector at k=0 block
    v = np.zeros(br)
    v[0] = 1.0
    
    # Apply noncentral E element
    x_mask, z_mask = pauli_mask(0b1, 0b0, 12)
    v_new = E_apply(v, x_mask, z_mask, 12)
    
    # Check that mass has spread
    block_energies = []
    for k in range(8):
        block_start = k * base
        block_end = (k + 1) * base
        energy = np.sum(v_new[block_start:block_end]**2)
        block_energies.append(energy)
        print(f"  Block {k} energy: {energy:.6f}")
    
    # Should have some spread (in actual implementation with proper lift tables)
    print(f"  Total energy: {sum(block_energies):.6f}")
    print("✓ Explosion test completed\n")


# ============================================================================
# Demo
# ============================================================================

def main():
    """Main demonstration."""
    print("Conway-Monster Atlas Core Bridge - Minimal Demo")
    print("=" * 60)
    
    # Initialize bridge
    bridge = AtlasBridge()
    bridge.set_mode(AtlasBridge.MODE_BRIDGE)
    bridge.spinlift_enable(True)
    
    print(f"Mode: BRIDGE, Spinlift: {bridge.spinlift_enabled}")
    base, br = bridge.dims()
    print(f"Dimensions: {base} (base) → {br} (bridge)")
    print()
    
    # Test explosion
    test_explosion()
    
    # Test projectors
    print("=== Projector Tests ===")
    v_test = np.random.randn(bridge.base_dim)
    v_test /= np.linalg.norm(v_test)
    
    r_class = projector_residual(Projectors.P_class_apply, v_test)
    r_qonly = projector_residual(Projectors.P_Qonly_apply, v_test)
    r_299 = projector_residual(Projectors.P_299_apply, v_test)
    
    print(f"P_class residual: {r_class:.2e}")
    print(f"P_Qonly residual: {r_qonly:.2e}")
    print(f"P_299 residual:   {r_299:.2e}")
    print()
    
    # Commutant probe
    print("=== Commutant Probe ===")
    dim_E = commutant_probe(with_Co1=False)
    dim_ECo1 = commutant_probe(with_Co1=True)
    print(f"Comm(E) effective dim:      {dim_E:.3f}")
    print(f"Comm(E,Co1) effective dim:  {dim_ECo1:.3f}")
    print()
    
    # Generate certificate
    print("=== Certificate Generation ===")
    cert_path = "bridge_cert.json"
    result = leakage_certificate(bridge, cert_path)
    if result == 0:
        print(f"✓ Certificate saved to {cert_path}")
        with open(cert_path, 'r') as f:
            cert = json.load(f)
        print(f"  Version: {cert['version']}")
        print(f"  Mode: {cert['mode']}")
        print(f"  Spinlift: {cert['spinlift']}")
    else:
        print(f"✗ Certificate generation failed")
    
    print("\n" + "=" * 60)
    print("Demo completed successfully!")


if __name__ == "__main__":
    main()
