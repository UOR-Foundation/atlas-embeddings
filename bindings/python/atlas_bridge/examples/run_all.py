#!/usr/bin/env python3
"""
bindings/python/atlas_bridge/examples/run_all.py
Conway–Monster Atlas Upgrade Kit v1.1
Run all examples demonstrating the Atlas Bridge functionality
"""

import sys
import os

# Add parent directory to path for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))

try:
    from atlas_bridge import _native as atlas
except ImportError as e:
    print(f"Error importing atlas_bridge: {e}")
    print("Please build the native library first.")
    sys.exit(1)

def example_basic_dimensions():
    """Example 1: Query basic dimensions."""
    print("=" * 60)
    print("Example 1: Basic Dimensions")
    print("=" * 60)
    
    base, bridge = atlas.get_dimensions()
    print(f"Base dimension:   {base:6d} (48 pages × 256 bytes)")
    print(f"Bridge dimension: {bridge:6d} (8-fold lift)")
    print(f"Ratio: {bridge // base}")
    print()

def example_phi_encoding():
    """Example 2: Phi encoding/decoding."""
    print("=" * 60)
    print("Example 2: Phi Encoding/Decoding")
    print("=" * 60)
    
    test_cases = [
        (0, 0),
        (10, 42),
        (47, 255),
    ]
    
    for page, byte in test_cases:
        idx = atlas.phi_encode(page, byte)
        decoded_page, decoded_byte = atlas.phi_decode(idx)
        
        print(f"Encode ({page:2d}, {byte:3d}) -> {idx:5d} -> ({decoded_page:2d}, {decoded_byte:3d})", end="")
        
        if decoded_page == page and decoded_byte == byte:
            print(" ✓")
        else:
            print(" ✗ MISMATCH")
    
    print()

def example_mode_switching():
    """Example 3: Mode switching."""
    print("=" * 60)
    print("Example 3: Mode Switching")
    print("=" * 60)
    
    print("Setting CLASS mode...")
    atlas.set_mode(atlas.ATLAS_MODE_CLASS)
    print("  Mode set to CLASS")
    
    print("Setting BRIDGE mode...")
    atlas.set_mode(atlas.ATLAS_MODE_BRIDGE)
    print("  Mode set to BRIDGE")
    
    print("Enabling spinlift...")
    atlas.enable_spinlift(True)
    print("  Spinlift enabled")
    
    print("Disabling spinlift...")
    atlas.enable_spinlift(False)
    print("  Spinlift disabled")
    
    print()

def example_e_group():
    """Example 4: E group operations."""
    print("=" * 60)
    print("Example 4: E Group Operations")
    print("=" * 60)
    
    print("Applying E group element with x_mask=0x123, z_mask=0x456...")
    atlas.apply_E_group(0x123, 0x456, n_qubits=12)
    print("  E group element applied")
    
    print("Applying identity (x=0, z=0)...")
    atlas.apply_E_group(0, 0)
    print("  Identity applied")
    
    print()

def example_co1_gates():
    """Example 5: Co1 gate operations."""
    print("=" * 60)
    print("Example 5: Co1 Gates")
    print("=" * 60)
    
    print("Applying Co1 identity gate...")
    atlas.apply_Co1_gate(0)
    print("  Identity gate applied")
    
    print("Applying Co1 gate with parameters...")
    atlas.apply_Co1_gate(1, params=[1.0, 0.5, 0.25])
    print("  Parameterized gate applied")
    
    print()

def example_projectors():
    """Example 6: Projector residuals."""
    print("=" * 60)
    print("Example 6: Projector Residuals")
    print("=" * 60)
    
    projectors = ["class", "qonly", "299"]
    
    for proj_name in projectors:
        try:
            residual = atlas.get_projector_residual(proj_name)
            print(f"Projector '{proj_name}': residual = {residual:.6e}")
        except Exception as e:
            print(f"Projector '{proj_name}': error - {e}")
    
    print()

def example_commutant():
    """Example 7: Commutant probing."""
    print("=" * 60)
    print("Example 7: Commutant Probing")
    print("=" * 60)
    
    print("Probing commutant without Co1...")
    dim_no_co1 = atlas.probe_commutant(with_co1=False)
    print(f"  Estimated dimension: {dim_no_co1:.2f}")
    
    print("Probing commutant with Co1...")
    dim_with_co1 = atlas.probe_commutant(with_co1=True)
    print(f"  Estimated dimension: {dim_with_co1:.2f}")
    
    print()

def example_leakage():
    """Example 8: Leakage certificate."""
    print("=" * 60)
    print("Example 8: Leakage Certificate")
    print("=" * 60)
    
    output_path = "/tmp/atlas_leakage_cert.json"
    
    print(f"Generating leakage certificate to {output_path}...")
    try:
        atlas.generate_leakage_certificate(output_path)
        print("  Certificate generated successfully")
        
        # Read and display
        if os.path.exists(output_path):
            with open(output_path, 'r') as f:
                content = f.read()
            print("\nCertificate content:")
            print(content)
    except Exception as e:
        print(f"  Error: {e}")
    
    print()

def main():
    """Run all examples."""
    print("\n")
    print("╔" + "═" * 58 + "╗")
    print("║" + " " * 58 + "║")
    print("║  Conway–Monster Atlas Upgrade Kit v1.1                  ║")
    print("║  Python Examples Suite                                  ║")
    print("║" + " " * 58 + "║")
    print("╚" + "═" * 58 + "╝")
    print("\n")
    
    examples = [
        example_basic_dimensions,
        example_phi_encoding,
        example_mode_switching,
        example_e_group,
        example_co1_gates,
        example_projectors,
        example_commutant,
        example_leakage,
    ]
    
    for i, example_func in enumerate(examples, 1):
        try:
            example_func()
        except Exception as e:
            print(f"\n✗ Example {i} failed: {e}\n")
            import traceback
            traceback.print_exc()
    
    print("=" * 60)
    print("All examples completed!")
    print("=" * 60)
    print()

if __name__ == "__main__":
    main()
