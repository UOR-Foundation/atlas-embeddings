# Projectors Documentation

## Overview

This document describes the projector operators implemented in the Conway–Monster Atlas Upgrade Kit. Projectors are used to isolate specific subspaces of interest within the full 12288 or 98304-dimensional Hilbert space.

## Mathematical Background

A **projector** P is a linear operator satisfying:
1. **Idempotency**: P² = P
2. **Hermiticity**: P† = P (for quantum projectors)

These properties ensure that P projects vectors onto a subspace and that repeated application has no additional effect.

## Implemented Projectors

### P_class: Class Projector

Projects onto the 96-dimensional resonance class subspace.

```c
void P_class_apply(double* v);
```

**Properties:**
- Target dimension: 96
- Physical interpretation: Extracts the resonance class structure from the full 48-page × 256-byte space
- Group invariance: Commutes with certain symmetries

**Mathematical Definition:**
```
P_class = Σ_{i=1}^{96} |c_i⟩⟨c_i|
```
where {|c_i⟩} is the orthonormal basis of resonance classes.

### P_Qonly: Quaternionic Projector

Projects onto the quaternionic subspace (64-dimensional).

```c
void P_Qonly_apply(double* v);
```

**Properties:**
- Target dimension: 64
- Physical interpretation: Isolates the quaternionic structure (related to division algebras)
- Useful for studying octonionic and exceptional structures

**Usage:**
```c
double* state = allocate_state(12288);
initialize_random(state, 12288);
P_Qonly_apply(state);
// state now lives in quaternionic subspace
```

### P_299: Monster Projector

Projects onto the 299-dimensional Monster-related subspace.

```c
void P_299_apply(double* v);
```

**Properties:**
- Target dimension: 299
- Physical interpretation: Related to Monster moonshine and the j-function
- Connection: The Monster group has a 196884-dimensional representation; 299 is related to early coefficient

**Monster Moonshine Connection:**
The j-function expansion begins:
```
j(τ) = q^(-1) + 744 + 196884q + 21493760q² + ...
```
where 196884 = 196883 + 1 = dim(V₁) + dim(V₀).

## Implementation Details

### Data Structures

Projectors are implemented via basis vector representations:

```c
typedef struct {
    double* basis;      // Orthonormal basis vectors
    size_t dim;         // Ambient dimension
    size_t rank;        // Subspace dimension
} ProjectorBasis;
```

### Application Algorithm

1. **Projection formula**: For state |ψ⟩ and orthonormal basis {|v_i⟩}:
   ```
   P|ψ⟩ = Σ_i |v_i⟩⟨v_i|ψ⟩
   ```

2. **In-place operation**:
   ```c
   for each basis vector v_i:
       coeff = dot_product(v_i, state)
       accumulate v_i with weight coeff
   replace state with accumulated result
   ```

### Verification

The `projector_residual` function verifies the idempotency property:

```c
double projector_residual(const char* pname);
```

**Algorithm:**
1. Create random test vector v
2. Compute Pv and P²v
3. Return ||P²v - Pv||₂

**Expected result**: Should be ≈ 0 (within numerical precision ~10⁻¹⁰)

## Projector Algebra

### Composition

Projectors can be composed:
```c
P₁ ∘ P₂ ∘ v
```

**Properties:**
- If P₁ and P₂ commute and are orthogonal: P₁P₂ = 0
- If subspaces are nested: P₁P₂ = P₂ (or P₁, depending on order)

### Orthogonality

Two projectors P₁ and P₂ are orthogonal if:
```
P₁P₂ = 0
```

This means their target subspaces have trivial intersection.

## Group Invariance

### Commutation with E Group

Key property: P_class should commute with E group elements:
```
[P_class, g] = 0  for all g ∈ E
```

This ensures the resonance class subspace is E-invariant.

### Commutation with Co1

The Monster projector P_299 has special transformation properties under Co1:
```
g P_299 g⁻¹ = P_299  for g ∈ Co1
```

## Usage Patterns

### Basic Projection

```c
// Allocate state
uint32_t dim;
atlas_dims(&dim, NULL);
double* state = malloc(dim * sizeof(double));

// Initialize with some data
random_vector(state, dim);

// Project onto resonance classes
P_class_apply(state);

// Verify idempotency
double residual = projector_residual("class");
printf("Residual: %e\n", residual);
```

### Subspace Analysis

```c
// Test if vector is in subspace
double* v = ...;
double* v_copy = copy_vector(v, dim);

P_class_apply(v_copy);

double distance = vector_diff_norm(v, v_copy, dim);
if (distance < 1e-10) {
    printf("Vector is in class subspace\n");
}
```

### Sequential Projection

```c
// Extract intersection of subspaces
P_class_apply(state);
P_Qonly_apply(state);
// state now in class ∩ quaternionic subspace
```

## Performance Considerations

### Computational Complexity
- Time: O(rank × dim) for dense implementation
- Space: O(rank × dim) to store basis vectors
- Optimization: Use sparse representations when rank << dim

### Memory Layout
- Basis vectors stored contiguously for cache efficiency
- SIMD vectorization opportunities in inner products

## TODO Items

- [ ] Implement sparse matrix representations for large-scale problems
- [ ] Add GPU acceleration for high-dimensional projections
- [ ] Optimize for repeated application (cache computed projections)
- [ ] Implement incremental projection updates
- [ ] Add support for approximate projectors (thresholding)

## References

1. Horn, R.A. & Johnson, C.R. "Matrix Analysis"
2. Halmos, P.R. "Finite-Dimensional Vector Spaces"
3. Griess, R.L. "The Friendly Giant" (Monster group)

## See Also

- [E Layer Documentation](e_layer.md)
- [Diagnostics Documentation](diagnostics.md)
- [API Reference](api_reference.md)
