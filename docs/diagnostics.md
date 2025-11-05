# Diagnostics Documentation

## Overview

The diagnostics module provides tools for verifying the correctness and performance of the Atlas Bridge implementation. This includes mathematical property checks, numerical stability analysis, and certification generation.

## Core Diagnostic Functions

### Projector Residual

```c
double projector_residual(const char* pname);
```

Computes the residual ||P² - P||₂ to verify the idempotency property of projectors.

**Parameters:**
- `pname`: Projector name ("class", "qonly", or "299")

**Returns:**
- Residual norm (should be ≈ 0 for valid projector)
- Negative value on error

**Mathematical Basis:**

A valid projector P must satisfy P² = P. The residual measures deviation:
```
residual = ||P²v - Pv||₂
```

For an orthogonal projector onto subspace S with orthonormal basis {v₁, ..., vₙ}:
```
P = Σᵢ |vᵢ⟩⟨vᵢ|
P² = (Σᵢ |vᵢ⟩⟨vᵢ|)(Σⱼ |vⱼ⟩⟨vⱼ|) = Σᵢ |vᵢ⟩⟨vᵢ| = P
```

**Usage Example:**
```c
double residual = projector_residual("class");
if (residual < 1e-10) {
    printf("Projector is valid\n");
} else {
    printf("Warning: Projector residual = %e\n", residual);
}
```

**Expected Values:**
- Perfect implementation: < 10⁻¹⁴ (machine epsilon for doubles)
- Good implementation: < 10⁻¹⁰
- Warning threshold: > 10⁻⁶

### Commutant Probe

```c
double commutant_probe(int with_Co1);
```

Estimates the dimension of the commutant using randomized linear algebra.

**Parameters:**
- `with_Co1`: Include Co1 constraints if non-zero

**Returns:**
- Estimated commutant dimension
- Negative value on error

**Mathematical Background:**

The commutant of a set of operators {Gᵢ} is:
```
Comm({Gᵢ}) = {A : [A, Gᵢ] = 0 for all i}
```

For our case:
- Without Co1: Operators commuting with E group
- With Co1: Operators commuting with both E and Co1

**Algorithm:**
1. Generate random matrix A
2. Compute commutators [A, gᵢ] for generators gᵢ
3. Measure rank deficiency of commutator matrix
4. Estimate dimension via matrix rank

**Interpretation:**
- Larger commutant → more symmetry
- Expected: dim(Comm(E)) > dim(Comm(E ∪ Co1))
- Monster connection: Monster commutant is 1-dimensional (scalars only)

### Leakage Certificate

```c
int leakage_certificate(const char* json_out_path);
```

Generates a JSON certificate documenting round-trip leakage from subspaces.

**Parameters:**
- `json_out_path`: Path to write JSON output

**Returns:**
- 0 on success
- Non-zero on error

**Certificate Structure:**
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
    },
    ...
  ],
  "status": "completed"
}
```

**Leakage Definition:**

For projector P and state |ψ⟩:
1. Project: |φ⟩ = P|ψ⟩
2. Apply operations: |φ'⟩ = g|φ⟩ for g ∈ Group
3. Re-project: |φ''⟩ = P|φ'⟩
4. Leakage: ||φ'' - φ||

Ideally: If P commutes with g, then |φ''⟩ = |φ⟩ (no leakage).

**Thresholds:**
- `absolute_leakage < 1e-10`: Good
- `absolute_leakage < 1e-6`: Acceptable
- `absolute_leakage > 1e-3`: Warning (possible implementation issue)

## Extended Diagnostics

### Full Diagnostic Suite

```c
int run_full_diagnostics(const char* output_dir);
```

Runs comprehensive diagnostics and writes multiple output files.

**Generated Files:**
- `projector_residuals.json`: All projector residuals
- `commutant_dims.json`: Commutant dimension estimates
- `leakage.json`: Leakage certificate

**Usage:**
```c
run_full_diagnostics("/tmp/atlas_diagnostics");
```

## Diagnostic Workflows

### Basic Verification

Minimum checks before using the library:
```c
// 1. Check projector validity
assert(projector_residual("class") < 1e-10);
assert(projector_residual("qonly") < 1e-10);
assert(projector_residual("299") < 1e-10);

// 2. Verify commutant structure
double dim_e = commutant_probe(0);
double dim_e_co1 = commutant_probe(1);
assert(dim_e > dim_e_co1);  // More constraints → smaller commutant

// 3. Generate leakage report
leakage_certificate("/tmp/leakage.json");
```

### Continuous Integration

For CI/CD pipelines:
```bash
# Build and run diagnostics
make build
./run_diagnostics --output-dir ./test_results

# Check exit code
if [ $? -ne 0 ]; then
    echo "Diagnostics failed"
    exit 1
fi

# Parse JSON results
python3 check_diagnostics.py ./test_results/*.json
```

### Performance Benchmarking

Monitor computational efficiency:
```c
#include <time.h>

clock_t start = clock();
P_class_apply(large_state);
clock_t end = clock();

double elapsed = (double)(end - start) / CLOCKS_PER_SEC;
printf("Projection time: %.3f ms\n", elapsed * 1000);
```

## Numerical Stability

### Error Sources

1. **Floating-point roundoff**: Accumulates in matrix operations
2. **Condition number**: Poorly conditioned matrices amplify errors
3. **Cancellation**: Subtracting nearly equal numbers loses precision

### Mitigation Strategies

1. **Use higher precision**: Switch to `long double` for critical calculations
2. **Kahan summation**: Compensated summation for long accumulations
3. **Preconditioning**: Scale matrices to improve condition numbers
4. **Iterative refinement**: Improve solutions via iteration

### Monitoring

```c
// Check condition number (simplified)
double cond = estimate_condition_number(projector_matrix);
if (cond > 1e12) {
    fprintf(stderr, "Warning: Ill-conditioned projector\n");
}
```

## Certification and Validation

### Mathematical Certification

Required properties for certification:
- [ ] All projectors idempotent (residual < 10⁻¹⁰)
- [ ] Commutant dimensions match theory
- [ ] Leakage below threshold (< 10⁻⁶)
- [ ] Group actions preserve norms
- [ ] Subspace dimensions correct

### Reproducibility

For reproducible diagnostics:
1. Fix random seeds: `srand(42)`
2. Use deterministic algorithms
3. Document numerical parameters
4. Archive test vectors

### Regression Testing

```c
// Compare against golden reference
double current = projector_residual("class");
double reference = 2.34e-13;  // From validated run

assert(fabs(current - reference) < 1e-12);
```

## Troubleshooting

### High Residuals

**Symptom**: `projector_residual > 1e-6`

**Possible Causes:**
- Basis vectors not orthonormal
- Numerical instability in Gram-Schmidt
- Memory corruption

**Solutions:**
1. Re-orthogonalize basis
2. Use higher precision
3. Check for buffer overflows

### Unexpected Commutant Dimension

**Symptom**: `commutant_probe` returns unexpected value

**Possible Causes:**
- Insufficient sampling
- Generator set incomplete
- Numerical rank estimation error

**Solutions:**
1. Increase number of probes
2. Verify generator completeness
3. Use SVD for robust rank estimation

### Leakage Warnings

**Symptom**: `leakage_certificate` reports high leakage

**Possible Causes:**
- Projectors don't commute with group
- Implementation bug in group actions
- Numerical precision issues

**Solutions:**
1. Verify commutation mathematically
2. Test group action independently
3. Increase precision in critical paths

## TODO Items

- [ ] Add support for custom diagnostic tests
- [ ] Implement automated regression detection
- [ ] Create HTML dashboard for diagnostic results
- [ ] Add statistical analysis of Monte Carlo estimates
- [ ] Implement parallel diagnostics for large-scale testing

## References

1. Higham, N.J. "Accuracy and Stability of Numerical Algorithms"
2. Golub, G.H. & Van Loan, C.F. "Matrix Computations"
3. Trefethen, L.N. & Bau, D. "Numerical Linear Algebra"

## See Also

- [E Layer Documentation](e_layer.md)
- [Projectors Documentation](projectors.md)
- [API Reference](api_reference.md)
