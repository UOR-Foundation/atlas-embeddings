#!/usr/bin/env python3
"""
Phase 0 Demo Script

Demonstrates the Phase 0 implementation with examples of:
1. Index map and address computations
2. Projector admissibility checks
3. Sigmatics-to-Multiplicity bridge compilation
4. Π-first reduction
"""

print("=" * 70)
print("Phase 0 — Hard Constraints Demo")
print("=" * 70)
print()

# ============================================================================
# 1. Index Map and Addresses
# ============================================================================

print("1. INDEX MAP AND ADDRESSES")
print("-" * 70)

from multiplicity_core.phase0_index import (
    INDEX_SIZE,
    NUM_PAGES,
    BYTES_PER_PAGE,
    make_address,
    decode_address,
)

print(f"Index size n = {INDEX_SIZE:,} (fixed)")
print(f"Formula: {NUM_PAGES} pages × {BYTES_PER_PAGE} bytes/page")
print()

# Example addresses
examples = [
    (0, 0, 0, "First address"),
    (17, 0, 46, "Example from docs"),
    (47, 0, 255, "Last address"),
]

print("Example addresses:")
for page, belt, offset, desc in examples:
    addr = make_address(page, belt, offset)
    print(f"  {desc}:")
    print(f"    index({page}, {belt}, {offset}) = {addr.linear_index}")
    print()

# Inverse mapping
print("Inverse mapping:")
test_idx = 4398
addr = decode_address(test_idx)
print(f"  index {test_idx} → page={addr.page}, belt={addr.belt}, offset={addr.offset}")
print()

# ============================================================================
# 2. Projector Admissibility
# ============================================================================

print("2. PROJECTOR ADMISSIBILITY")
print("-" * 70)

from multiplicity_core.phase0_index import (
    prime_factors,
    check_projector_admissibility,
    list_admissible_projectors,
)

factors = prime_factors(INDEX_SIZE)
print(f"Prime factorization: {INDEX_SIZE:,} = ", end="")
factor_str = " × ".join(f"{p}^{e}" for p, e in sorted(factors.items()))
print(factor_str)
print()

print("Admissible projectors (p^r | n):")
projectors = list_admissible_projectors(INDEX_SIZE, max_prime=10)
for p, r in projectors[:5]:  # Show first 5
    print(f"  (p={p}, r={r}): {p}^{r} = {p**r}")
print(f"  ... ({len(projectors)} total)")
print()

print("Admissibility checks:")
test_cases = [
    (2, 8, "256 divides 12,288"),
    (3, 1, "3 divides 12,288"),
    (5, 1, "5 does NOT divide 12,288"),
]
for p, r, desc in test_cases:
    result = check_projector_admissibility(p, r)
    status = "✓ admissible" if result else "✗ NOT admissible"
    print(f"  (p={p}, r={r}): {status} ({desc})")
print()

# ============================================================================
# 3. Policies (UNPROVEN)
# ============================================================================

print("3. POLICIES (UNPROVEN)")
print("-" * 70)

from multiplicity_core.phase0_index import (
    prime_policy_default,
    level_policy_default,
    perm_policy_default,
    DEFAULT_POLICIES,
)

print("⚠️  All policies are UNPROVEN until mathematically verified.")
print()

print("Default policies:")
for d in [0, 1, 2]:
    p = prime_policy_default(d)
    r = level_policy_default(d)
    pi = perm_policy_default(d)
    print(f"  d={d}: primePolicy→{p}, levelPolicy→{r}, permPolicy→{pi}")
print()

print(f"Policy set status: {DEFAULT_POLICIES.status}")
print()

# ============================================================================
# 4. Sigmatics to Multiplicity Bridge
# ============================================================================

print("4. SIGMATICS TO MULTIPLICITY BRIDGE")
print("-" * 70)

from multiplicity_core.sigmatics_bridge import bridge_compile

# Example 1: Simple sequence
print("Example 1: Simple sequence")
sigmatics1 = ["phase[h₂=0]", "evaluate"]
result1 = bridge_compile(sigmatics1, apply_pi_first=False)

print(f"  Input:  {sigmatics1}")
print(f"  Output: {[w.opcode for w in result1.multiplicity_words]}")
print()

# Example 2: With Π-atoms (no Π-first)
print("Example 2: With Π-atoms (no Π-first reduction)")
sigmatics2 = ["phase[h₂=0]", "mark[d=0]", "evaluate", "copy[d=1]"]
result2 = bridge_compile(sigmatics2, apply_pi_first=False)

print(f"  Input:  {sigmatics2}")
print(f"  Output: {[w.opcode for w in result2.multiplicity_words]}")
print()

# Example 3: With Π-first reduction
print("Example 3: With Π-first reduction (Π-atoms first)")
result3 = bridge_compile(sigmatics2, apply_pi_first=True)

print(f"  Input:  {sigmatics2}")
print(f"  Output: {[w.opcode for w in result3.multiplicity_words]}")
print(f"  Note: MARK and COPY are now first (Π-atoms)")
print()

# ============================================================================
# 5. Detailed Compilation Example
# ============================================================================

print("5. DETAILED COMPILATION EXAMPLE")
print("-" * 70)

sigmatics_detailed = ["phase[h₂=2]", "mark[d=1]", "copy[d=0]", "evaluate"]
result_detailed = bridge_compile(sigmatics_detailed, apply_pi_first=True)

print("Sigmatics words → Multiplicity words:")
for sig_word, mult_word in zip(result_detailed.sigmatics_words, 
                                 result_detailed.multiplicity_words):
    args_str = f"({', '.join(map(str, mult_word.args))})" if mult_word.args else "()"
    print(f"  {sig_word:20s} → {mult_word.opcode}{args_str}")
print()

print(f"Π-first reduction: {'Applied' if result_detailed.pi_first_applied else 'Not applied'}")
print()

# ============================================================================
# 6. Summary
# ============================================================================

print("6. SUMMARY")
print("-" * 70)

from multiplicity_core.phase0_index import validate_phase0_constraints

validation = validate_phase0_constraints()

print("Phase 0 validation results:")
print(f"  ✓ Index size check: {validation['index_size_check']}")
print(f"  ✓ Size consistency: {validation['size_consistency']}")
print(f"  ✓ Factorization: {validation['factorization']}")
print(f"  ✓ Admissible projectors: {len(validation['admissible_projectors'])} found")
print(f"  ⚠  Policies status: {validation['policies_status']}")
print()

print("=" * 70)
print("Phase 0 implementation complete!")
print("See docs/PHASE0_IMPLEMENTATION.md for full documentation.")
print("=" * 70)
