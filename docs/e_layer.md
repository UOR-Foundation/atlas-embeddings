# E Layer Documentation

## Overview

The **E Layer** refers to the elementary abelian 2-group structure at the heart of the Conway–Monster Atlas construction. This document describes the mathematical foundations and implementation details.

## Mathematical Background

### Group Structure

The E group is an extraspecial 2-group that fits into the exact sequence:

```
1 → Z/2 → E → (Z/2)^12 → 1
```

Key properties:
- Order: 2^13 = 8192
- Exponent: 2 (every element squares to identity or central element)
- Center: {±I} (2 elements)
- Derived subgroup: Z/2 (central)

### Representation

We represent E group elements using the Pauli formalism:

```c
typedef struct {
    uint64_t x_bits;  // X-type support (12 qubits)
    uint64_t z_bits;  // Z-type support (12 qubits)
    uint8_t phase;    // Phase factor (0, 1, 2, 3 for i^phase)
} EGroupElement;
```

### Commutation Relations

For elements `a = (x_a, z_a)` and `b = (x_b, z_b)`, the commutator is determined by the symplectic form:

```
[a, b] = ω(a, b) · I
```

where `ω(a, b) = (x_a · z_b) - (z_a · x_b)` (mod 2).

## Implementation Details

### Core Functions

#### E_apply
```c
void E_apply(const uint64_t* x_mask, const uint64_t* z_mask, int n_qubits);
```

Applies the E group element specified by `(x_mask, z_mask)` to the current state.

**Parameters:**
- `x_mask`: Bit pattern for X-type Pauli operators (12 qubits)
- `z_mask`: Bit pattern for Z-type Pauli operators (12 qubits)
- `n_qubits`: Number of qubits (should be 12)

**Implementation Notes:**
- The center element -I is enforced (phase = 2)
- Commutation relations follow symplectic structure
- Efficient bit manipulation for operator application

### Usage Examples

```c
// Apply identity (trivial element)
uint64_t x = 0, z = 0;
E_apply(&x, &z, 12);

// Apply X on qubit 0
uint64_t x = 0x001, z = 0;
E_apply(&x, &z, 12);

// Apply Z on qubit 1
uint64_t x = 0, z = 0x002;
E_apply(&x, &z, 12);

// Apply Y on qubit 2 (Y = iXZ)
uint64_t x = 0x004, z = 0x004;
E_apply(&x, &z, 12);
```

## Relationship to Atlas

The E group acts on the 12288-dimensional base space (48 pages × 256 bytes):

1. **Page Structure**: 48 pages correspond to elements of (Z/2)^6 (modulo certain equivalences)
2. **Byte Structure**: 256 bytes form the computational basis
3. **Action**: E elements permute and phase the basis states

### Spinlift Extension

In BRIDGE mode, the E action extends to the 98304-dimensional space via spinlift:

```
Bridge Index = Base Index + 12288 × k,  k ∈ {0,1,...,7}
```

The spinlift accounts for the double-valued nature of spinor representations.

## Advanced Topics

### Clifford Group Connection

The E group generates (part of) the 12-qubit Clifford group:
- Pauli group: E itself
- Hadamard gates: Conjugate E elements
- Phase gates: Diagonal operations

### Monster Connection

The E group structure is intimately related to:
- Binary Golay code (24-bit words)
- Leech lattice (24-dimensional)
- Conway group Co₁ (automorphisms)
- Monster group (via moonshine)

## TODO Items

- [ ] Implement efficient sparse matrix representation for large-scale operations
- [ ] Add support for Clifford gate compilation
- [ ] Optimize commutator calculations for dense operations
- [ ] Implement character table for E group
- [ ] Add visualization tools for orbit structures

## References

1. Conway, J.H. & Sloane, N.J.A. "Sphere Packings, Lattices and Groups"
2. Griess, R.L. "Twelve Sporadic Groups"
3. Wilson, R.A. "The Finite Simple Groups"

## See Also

- [Projectors Documentation](projectors.md)
- [Diagnostics Documentation](diagnostics.md)
- [API Reference](api_reference.md)
