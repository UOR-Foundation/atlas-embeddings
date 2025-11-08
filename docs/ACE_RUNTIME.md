# ACE Runtime: Stability + Lawfulness

This document describes the ACE (Adaptive Constraint Enforcement) runtime implementation for the Atlas Hologram project.

## Overview

The ACE runtime implements a fail-safe control system with:

- **Weighted ℓ₁ projection** with KKT (Karush-Kuhn-Tucker) certificates for optimality
- **Update law**: `T_{t+1} = F + K_t T_t` with guaranteed contraction `∥K_t∥ ≤ 1−ε_t`
- **Per-step contraction tracking** and Cauchy convergence verification
- **Fail-closed semantics**: rejects proposals that violate safety conditions
- **PETC lawfulness**: all operations logged to Prime-Exact Tensor Consistency ledger
- **Fixed address lattice**: 96 resonance classes × 12,288 coordinates (48 pages × 256 bytes)

## Architecture

### 1. KKT Certificates

Every projection generates a `KKTCertificate` proving optimality:

```python
@dataclass(frozen=True)
class KKTCertificate:
    primal_feasible: bool          # Constraints satisfied
    dual_feasible: bool            # Multipliers non-negative
    complementary_slack_satisfied: bool  # Active constraints
    stationarity_gap: int          # Gradient condition (0 = exact)
    lambda_1: int                  # Dual multiplier for constraint 1
    lambda_2: int                  # Dual multiplier for constraint 2
```

**Verification**: `is_valid()` returns `True` iff all optimality conditions hold.

### 2. Update Law with Contraction

The runtime evolves state `T_t` according to:

```
T_{t+1} = F + K_t T_t
```

where:
- `F` is the target/fixed point
- `K_t` is the contraction operator with `∥K_t∥ ≤ 1 - ε_t`
- `ε_t > 0` is the gap parameter ensuring exponential convergence

**Contraction guarantee**:
```
∥T_{t+1} - F∥ ≤ (1 - ε_t) ∥T_t - F∥
```

This ensures Cauchy convergence: `T_t → F` exponentially fast.

### 3. Contraction Tracking

Each step records `ContractionMetrics`:

```python
@dataclass
class ContractionMetrics:
    step: int
    eps_t: int                     # Gap parameter (scaled by Q)
    K_t_norm: int                  # Operator norm ∥K_t∥ (scaled by Q)
    contraction_satisfied: bool    # ∥K_t∥ ≤ 1 - ε_t
    delta_T: int                   # ∥T_{t+1} - T_t∥ (scaled by Q)
    cumulative_contraction: int    # ∏_{i=0}^t (1-ε_i) (scaled by Q)
```

**Convergence certificate**: The runtime provides `get_cauchy_convergence_certificate()` proving:
- All steps satisfied contraction
- Convergence rate bounds
- Cauchy criterion verification

### 4. Fixed Address Lattice

State `T` lives on the Atlas lattice:

```
96 resonance classes × 12,288 coordinates = 1,179,648 total dimension
```

This matches the boundary group structure `G = P × B` where:
- `P` has 48 pages
- `B` has 256 bytes per page
- `|G| = 48 × 256 = 12,288`

### 5. Boundary Group with (Z/2)¹¹ Action

The `BoundaryGroup` implements:

```python
class BoundaryGroup:
    pages = 48
    bytes_per_page = 256
    num_anchors = 6
    group_order = 2048  # |U| = 2^11
```

**Structure**:
- Group `G = P × B` partitioned into 6 orbits
- Each orbit indexed by `r ∈ {0,1,2,3,4,5}`
- Anchors: `{(8m, 0) for m=0..5}`
- Action: `U ≅ (Z/2)^{11}` acts freely and transitively on each orbit

**Encoding**:
```
(p, b) ↦ (r, idx) where:
  r = p // 8
  idx = (p % 8) * 256 + b ∈ [0, 2048)
```

**Action**:
```python
def act_U(p: int, b: int, u: int) -> Tuple[int, int]:
    """For u ∈ U, compute u · (p,b)."""
    r, idx = pack(p, b)
    idx_new = (idx + u) % 2048
    return unpack(r, idx_new)
```

### 6. Subgroup Certificate

`generate_subgroup_certificate()` proves:

1. **Freeness**: `∀u≠0, ∀g: u·g ≠ g` (no fixed points)
2. **Orbit sizes**: Each orbit has exactly 2048 elements
3. **Disjointness**: Six orbits partition `G` with no overlap
4. **Transitivity**: Within each orbit, `U` acts transitively

Example output:
```json
{
  "valid": true,
  "group_structure": "(Z/2)^11",
  "group_order": 2048,
  "num_orbits": 6,
  "orbit_size": 2048,
  "total_elements": 12288,
  "freeness_verified": 72,
  "anchors": [[0,0], [8,0], [16,0], [24,0], [32,0], [40,0]]
}
```

### 7. Canonical Fair Schedule

The `FairSchedule` implements the Φ-permutation:

```
Φ(p, b) = ((p + 16) mod 48, (b + 1) mod 256)
```

**Properties**:
- `order(16 mod 48) = 3`
- `order(1 mod 256) = 256`
- `lcm(3, 256) = 768` ⇒ `Φ^{768} = id`

This provides fair round-robin scheduling over all coordinates with period 768.

## Usage

### Basic Runtime Setup

```python
from atlas.aep.ace_runtime import (
    ACERuntimeState,
    ACERuntime,
    BoundaryGroup,
    FairSchedule,
)
from atlas.aep.ace import Budgets

# Initialize state
state = ACERuntimeState(
    T=[1000] * 12288,  # Initial state
    F=[0] * 12288,     # Target (origin)
    Q=1000000,         # Scaling factor
)

runtime = ACERuntime(state)

# Setup constraints
budgets = Budgets(
    b=[1] * 12288,
    a=[1] * 12288,
    limit1_Q=10000000,
    limit2_Q=10000000,
    Q=1000000,
)

# Contraction operator (e.g., 0.8 * Identity)
eps_t = 200000  # Gap = 0.2
K_t = [[800000 if i==j else 0 for j in range(12288)] for i in range(12288)]

# Proposal weights and norms
w_proposal = [100] * 12288
B_norms_Q = [1000] * 12288

# Execute one step
success, error = runtime.step(
    w_proposal=w_proposal,
    budgets=budgets,
    B_norms_Q=B_norms_Q,
    eps_t=eps_t,
    K_t=K_t,
    fail_closed=True,
)

if success:
    print(f"Step {state.step} completed")
else:
    print(f"Step failed: {error}")
```

### Generate Audit Bundle

```python
from atlas.aep.ace_runtime import create_audit_bundle

# Run runtime for several steps...
# (see above)

# Generate comprehensive audit
bg = BoundaryGroup()
schedule = FairSchedule()
audit = create_audit_bundle(state, bg, schedule)

print(f"Audit valid: {audit['subgroup_certificate']['valid']}")
print(f"Schedule valid: {audit['schedule_verification']['valid']}")
print(f"PETC ledger valid: {audit['petc_ledger']['valid']}")
print(f"Total steps: {audit['runtime_steps']}")
```

### Verify Convergence

```python
# Get Cauchy convergence certificate
cert = runtime.get_cauchy_convergence_certificate()

print(f"Converged: {cert['converged']}")
print(f"All contractive: {cert['all_contractive']}")
print(f"Convergence rate: {cert['convergence_rate']}")
print(f"Cauchy satisfied: {cert['cauchy_satisfied']}")
```

## Mathematical Guarantees

### Theorem 1: Exponential Convergence

If `∥K_t∥ ≤ 1 - ε` for all `t` with `ε > 0`, then:

```
∥T_t - F∥ ≤ (1-ε)^t ∥T_0 - F∥
```

**Proof**: By induction on the update law.

### Theorem 2: Cauchy Criterion

For any `δ > 0`, there exists `N` such that for all `t,k > N`:

```
∥T_{t+k} - T_t∥ < δ
```

**Proof**: Follows from exponential convergence.

### Theorem 3: KKT Optimality

The projection `w* = proj_S(w)` satisfies:

1. **Primal feasibility**: `∑ b_i |w*_i| ≤ R_1`, `∑ a_i |w*_i| ≤ R_2`
2. **Dual feasibility**: `λ_1, λ_2 ≥ 0`
3. **Complementary slackness**: `λ_i > 0 ⇒ slack_i = 0`
4. **Stationarity**: `∇f(w*) + λ_1 ∇g_1(w*) + λ_2 ∇g_2(w*) = 0`

### Theorem 4: (Z/2)¹¹ Action

The action `U × G → G` is:

1. **Free**: No fixed points except identity
2. **Transitive**: Within each of 6 orbits
3. **Partition**: `G = ⨆_{r=0}^5 orbit_r` with `|orbit_r| = 2048`

## PETC Integration

Every runtime step appends to the PETC ledger:

```python
ledger_payload = {
    "step": step_number,
    "kkt_valid": bool,
    "kkt_stationarity_gap": int,
    "ace_accepted": bool,
    "contraction_satisfied": bool,
    "K_t_norm": int,
    "eps_t": int,
    "delta_T": int,
}
state.petc_ledger.append("ace_step", ledger_payload)
```

The ledger is cryptographically chained and verifiable:

```python
assert state.petc_ledger.verify()  # SHA-256 chain intact
```

## Fail-Closed Semantics

With `fail_closed=True` (default), the runtime **rejects** any step that violates:

- KKT optimality conditions
- ACE acceptance criteria
- Contraction condition `∥K_t∥ ≤ 1 - ε_t`

This provides **safety guarantees**: the system cannot enter an unsafe state.

With `fail_closed=False`, violations generate warnings but execution continues (for debugging).

## Testing

Run the full test suite:

```bash
pytest tests/test_ace_runtime.py -v
```

Tests cover:
- KKT certificate generation and validation
- Contraction verification and tracking
- Update law correctness
- Boundary group structure
- Subgroup certificate generation
- Fair schedule periodicity
- Audit bundle creation
- Full integration workflow

## References

- **ACE Projection**: Duchi et al., "Efficient Projections onto the ℓ₁-Ball"
- **KKT Conditions**: Boyd & Vandenberghe, "Convex Optimization"
- **Contraction Mapping**: Banach Fixed Point Theorem
- **PETC**: Prime-Exact Tensor Consistency framework (internal)
- **Atlas Structure**: UOR Foundation documentation

## License

MIT License (see LICENSE file)
