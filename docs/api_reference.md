# Atlas Bridge API Reference

## Overview

This document provides a complete API reference for the Conway–Monster Atlas Upgrade Kit v1.1. The API is implemented in C with Python bindings available.

## Table of Contents

1. [Configuration and Setup](#configuration-and-setup)
2. [Indexing and Encoding](#indexing-and-encoding)
3. [Group Actions](#group-actions)
4. [Projectors](#projectors)
5. [Diagnostics](#diagnostics)
6. [Python Bindings](#python-bindings)

---

## Configuration and Setup

### atlas_dims

```c
int atlas_dims(uint32_t* base, uint32_t* bridge);
```

Query the dimensions of the Atlas spaces.

**Parameters:**
- `base`: Pointer to store base dimension (12288)
- `bridge`: Pointer to store bridge dimension (98304)

**Returns:**
- 0 on success
- Non-zero on error

**Example:**
```c
uint32_t base_dim, bridge_dim;
atlas_dims(&base_dim, &bridge_dim);
printf("Base: %u, Bridge: %u\n", base_dim, bridge_dim);
```

### atlas_set_mode

```c
void atlas_set_mode(int mode);
```

Set the operating mode for Atlas operations.

**Parameters:**
- `mode`: Either `ATLAS_MODE_CLASS` (0) or `ATLAS_MODE_BRIDGE` (1)

**Modes:**
- `ATLAS_MODE_CLASS`: 96 resonance classes, 12288-dimensional
- `ATLAS_MODE_BRIDGE`: 8-fold spinlift, 98304-dimensional

**Example:**
```c
atlas_set_mode(ATLAS_MODE_BRIDGE);
atlas_spinlift_enable(1);
```

### atlas_spinlift_enable

```c
void atlas_spinlift_enable(int on);
```

Enable or disable spinlift (only effective in BRIDGE mode).

**Parameters:**
- `on`: 1 to enable, 0 to disable

**Effect:**
- Enables double-valued spinor representations
- Accounts for 2π vs 4π rotation properties

---

## Indexing and Encoding

### phi_encode

```c
uint32_t phi_encode(uint8_t page, uint8_t byte);
```

Encode (page, byte) pair into linear index.

**Parameters:**
- `page`: Page number (0-47)
- `byte`: Byte value (0-255)

**Returns:**
- Linear index in range [0, 12287]

**Formula:**
```
index = page × 256 + byte
```

**Example:**
```c
uint32_t idx = phi_encode(10, 42);  // Returns 2602
```

### phi_decode

```c
int phi_decode(uint32_t idx, uint8_t* page, uint8_t* byte);
```

Decode linear index back to (page, byte) pair.

**Parameters:**
- `idx`: Linear index (0-12287)
- `page`: Pointer to store page number
- `byte`: Pointer to store byte value

**Returns:**
- 0 on success
- -1 if index out of range

**Example:**
```c
uint8_t page, byte;
if (phi_decode(2602, &page, &byte) == 0) {
    printf("Page: %u, Byte: %u\n", page, byte);
}
```

### phi_bridge (inline)

```c
static inline uint32_t phi_bridge(uint32_t idx_base, uint8_t k);
```

Compute bridge index from base index and lift level.

**Parameters:**
- `idx_base`: Base index (0-12287)
- `k`: Lift level (0-7)

**Returns:**
- Bridge index in range [0, 98303]

**Formula:**
```
bridge_index = base_index + 12288 × (k & 7)
```

**Example:**
```c
uint32_t base_idx = 1000;
uint32_t bridge_idx = phi_bridge(base_idx, 3);  // Returns 37864
```

---

## Group Actions

### E_apply

```c
void E_apply(const uint64_t* x_mask, const uint64_t* z_mask, int n_qubits);
```

Apply elementary abelian 2-group (E) action.

**Parameters:**
- `x_mask`: X-type Pauli operator mask (24 bits packed in uint64_t)
- `z_mask`: Z-type Pauli operator mask (24 bits packed in uint64_t)
- `n_qubits`: Number of qubits (should be 12)

**Group Structure:**
E ≅ 2^{12} × 2^{12} (extraspecial 2-group)

**Representation:**
Elements represented as (x, z) pairs where:
- x specifies X-type operators
- z specifies Z-type operators
- Central element: -I (all zeros with phase π)

**Example:**
```c
// Apply X on qubit 0
uint64_t x = 0x001, z = 0x000;
E_apply(&x, &z, 12);

// Apply Z on qubit 1
uint64_t x = 0x000, z = 0x002;
E_apply(&x, &z, 12);

// Apply Y on qubit 2 (Y = iXZ)
uint64_t x = 0x004, z = 0x004;
E_apply(&x, &z, 12);
```

### Co1_apply

```c
void Co1_apply(uint32_t gate_id, const double* params, int n_params);
```

Apply Conway group Co₁ gate.

**Parameters:**
- `gate_id`: Gate identifier (see gate catalog)
- `params`: Array of parameters (may be NULL)
- `n_params`: Number of parameters

**Gate IDs:**
- `0`: Identity
- `1`: M24 simple element
- `2`: Leech lattice rotation
- `3`: Golay code permutation
- `4`: Octad-based flip

**Conway Group Properties:**
- Order: |Co₁| = 4157776806543360000
- Related to Leech lattice automorphisms
- Contains M24 (Mathieu group)

**Example:**
```c
// Apply identity
Co1_apply(0, NULL, 0);

// Apply parameterized M24 element
double params[] = {1.0, 0.5, 0.25};
Co1_apply(1, params, 3);
```

---

## Projectors

### P_class_apply

```c
void P_class_apply(double* v);
```

Apply class projector (96-dimensional subspace).

**Parameters:**
- `v`: State vector (modified in-place)

**Effect:**
Projects onto resonance class subspace.

**Properties:**
- Idempotent: P² = P
- Hermitian: P† = P
- Rank: 96

### P_Qonly_apply

```c
void P_Qonly_apply(double* v);
```

Apply quaternionic projector (64-dimensional subspace).

**Parameters:**
- `v`: State vector (modified in-place)

**Effect:**
Projects onto quaternionic subspace.

### P_299_apply

```c
void P_299_apply(double* v);
```

Apply Monster projector (299-dimensional subspace).

**Parameters:**
- `v`: State vector (modified in-place)

**Effect:**
Projects onto Monster-related subspace.

**Monster Connection:**
Related to the j-function coefficient 196884 = 196883 + 1.

---

## Diagnostics

### projector_residual

```c
double projector_residual(const char* pname);
```

Compute projector idempotency residual ||P² - P||₂.

**Parameters:**
- `pname`: Projector name ("class", "qonly", or "299")

**Returns:**
- Residual norm (should be ≈ 0)
- Negative on error

**Interpretation:**
- < 10⁻¹⁰: Excellent
- < 10⁻⁶: Good
- > 10⁻³: Warning

### commutant_probe

```c
double commutant_probe(int with_Co1);
```

Estimate commutant dimension via randomized probing.

**Parameters:**
- `with_Co1`: Include Co1 constraints if non-zero

**Returns:**
- Estimated dimension
- Negative on error

**Theory:**
- Commutant of E only: larger dimension
- Commutant of E ∪ Co1: smaller dimension
- Monster commutant: dimension 1 (scalars only)

### leakage_certificate

```c
int leakage_certificate(const char* json_out_path);
```

Generate leakage certificate as JSON.

**Parameters:**
- `json_out_path`: Output file path

**Returns:**
- 0 on success
- Non-zero on error

**Output Format:**
```json
{
  "timestamp": 1699123456,
  "dimension": 12288,
  "projectors": [
    {
      "name": "class",
      "absolute_leakage": 1.23e-12,
      "relative_leakage": 5.67e-13,
      "status": "good"
    }
  ],
  "status": "completed"
}
```

---

## Python Bindings

### Installation

```python
import sys
sys.path.insert(0, 'bindings/python')
from atlas_bridge import _native as atlas
```

### Constants

```python
atlas.ATLAS_MODE_CLASS   # = 0
atlas.ATLAS_MODE_BRIDGE  # = 1
```

### Functions

#### get_dimensions()

```python
base, bridge = atlas.get_dimensions()
```

Returns tuple of (base_dim, bridge_dim).

#### set_mode(mode)

```python
atlas.set_mode(atlas.ATLAS_MODE_BRIDGE)
```

Set operating mode.

#### enable_spinlift(enabled)

```python
atlas.enable_spinlift(True)
```

Enable/disable spinlift.

#### phi_encode(page, byte)

```python
idx = atlas.phi_encode(10, 42)
```

Encode to linear index.

#### phi_decode(idx)

```python
page, byte = atlas.phi_decode(2602)
```

Decode from linear index. Raises `ValueError` if out of range.

#### apply_E_group(x_mask, z_mask, n_qubits=12)

```python
atlas.apply_E_group(0x123, 0x456)
```

Apply E group element.

#### apply_Co1_gate(gate_id, params=None)

```python
atlas.apply_Co1_gate(1, params=[1.0, 0.5])
```

Apply Co1 gate.

#### get_projector_residual(name)

```python
residual = atlas.get_projector_residual("class")
```

Get projector residual.

#### probe_commutant(with_co1=False)

```python
dim = atlas.probe_commutant(with_co1=True)
```

Probe commutant dimension.

#### generate_leakage_certificate(output_path)

```python
atlas.generate_leakage_certificate("/tmp/cert.json")
```

Generate certificate. Raises `RuntimeError` on failure.

---

## Error Handling

### C API

Most functions return:
- `0` or positive values on success
- Negative values on error
- Check return codes explicitly

### Python API

Functions raise exceptions:
- `ValueError`: Invalid parameters
- `RuntimeError`: Internal errors
- `OSError`: File I/O errors

---

## Thread Safety

⚠️ **Current implementation is NOT thread-safe.**

For concurrent usage:
1. Use separate processes
2. Add external synchronization
3. Future: Thread-local storage

---

## Performance Notes

- Projector application: O(rank × dim)
- E group action: O(n_qubits × dim)
- Co1 gates: O(complexity varies by gate)

Optimize by:
- Reusing allocated buffers
- Batch operations when possible
- Use BRIDGE mode only when needed

---

## See Also

- [E Layer Documentation](e_layer.md)
- [Projectors Documentation](projectors.md)
- [Diagnostics Documentation](diagnostics.md)
