#!/usr/bin/env python3
"""
Example usage of Atlas Bridge Context API v0.2 Python bindings
"""

import sys
import os

# Add path to bindings
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))

try:
    from bindings.python.atlas_bridge._native_ctx import (
        AtlasBridgeContext,
        get_version,
        get_default_config,
        ATLAS_CTX_ENABLE_TWIRL,
        ATLAS_CTX_ENABLE_LIFT,
    )
except ImportError as e:
    print(f"Error importing Context API bindings: {e}")
    print("\nPlease build the library first:")
    print("  cd atlas_core")
    print("  mkdir -p lib")
    print("  gcc -c -fPIC -Iinclude src/atlas_bridge_ctx.c")
    print("  gcc -shared -o lib/libatlas_bridge_ctx.so atlas_bridge_ctx.o -lm")
    sys.exit(1)

def main():
    print("=" * 60)
    print("Atlas Bridge Context API v0.2 - Python Example")
    print("=" * 60)
    print()
    
    # Get version
    print(f"Library version: {get_version()}")
    print()
    
    # Get default config
    cfg = get_default_config()
    print("Default configuration:")
    print(f"  Block size: {cfg.block_size}")
    print(f"  Qubits: {cfg.n_qubits}")
    print(f"  Twirl generators: {cfg.twirl_gens}")
    print(f"  Epsilon: {cfg.epsilon:.2e}")
    print()
    
    # Create context
    print("Creating context with twirl and lift enabled...")
    cfg.flags = ATLAS_CTX_ENABLE_TWIRL | ATLAS_CTX_ENABLE_LIFT
    ctx = AtlasBridgeContext(cfg)
    print(f"  ✓ Context created")
    print(f"  Block size: {ctx.block_size}")
    print(f"  Qubits: {ctx.n_qubits}")
    print()
    
    # Create test state
    import random
    random.seed(42)
    state = [random.gauss(0, 1) for _ in range(ctx.block_size)]
    
    # Normalize
    import math
    norm = math.sqrt(sum(x*x for x in state))
    state = [x/norm for x in state]
    
    initial_mass = sum(abs(x) for x in state)
    print(f"Initial state L1 mass: {initial_mass:.6f}")
    print()
    
    # Apply operations
    print("Applying operations:")
    
    print("  1. Lift Lx...")
    ctx.apply_lift_x(state)
    mass = sum(abs(x) for x in state)
    print(f"     L1 mass: {mass:.6f}")
    
    print("  2. Pauli X on qubits {0,1,2}...")
    ctx.apply_pauli_x(0x07, state)
    mass = sum(abs(x) for x in state)
    print(f"     L1 mass: {mass:.6f}")
    
    print("  3. E-twirl (16 generators)...")
    ctx.apply_twirl(state)
    mass = sum(abs(x) for x in state)
    print(f"     L1 mass: {mass:.6f}")
    
    print("  4. Lift Lz...")
    ctx.apply_lift_z(state)
    final_mass = sum(abs(x) for x in state)
    print(f"     L1 mass: {final_mass:.6f}")
    print()
    
    # Check twirl idempotency
    print("Checking twirl idempotency...")
    test_state = [random.gauss(0, 1) for _ in range(ctx.block_size)]
    idempotency = ctx.check_twirl_idempotency(test_state)
    print(f"  ||T²(v) - T(v)||₂ = {idempotency:.6e}")
    if idempotency < 1e-6:
        print("  ✓ Twirl is idempotent")
    print()
    
    # Get diagnostics
    diag = ctx.get_diagnostics()
    print("Context diagnostics:")
    print(f"  Operations performed: {diag.op_count}")
    print(f"  Twirl idempotency: {diag.twirl_idempotency:.6e}")
    print()
    
    # Query generators
    print("E-twirl generators (first 5):")
    for i in range(5):
        x_mask, z_mask = ctx.get_twirl_generator(i)
        print(f"  Generator {i}: X=0x{x_mask:02X}, Z=0x{z_mask:02X}")
    print()
    
    # Validate context
    if ctx.validate():
        print("✓ Context validation passed")
    else:
        print("✗ Context validation failed")
    print()
    
    print("=" * 60)
    print("✓ Python example completed successfully!")
    print("=" * 60)

if __name__ == '__main__':
    main()
