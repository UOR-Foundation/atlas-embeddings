# ACE Runtime XP - GPU/CPU Backend Support

This directory contains the ACE (Adaptive Constraint Enforcement) runtime with flexible backend support for both CPU (NumPy) and GPU (CuPy) execution.

## Components

### ace_backend.py
Backend selector that chooses between NumPy and CuPy based on environment variables or explicit parameters.

**Usage:**
```python
from multiplicity_core.ace_backend import select_xp

# Get NumPy backend (default)
xp, np, is_gpu = select_xp()

# Explicitly request CuPy (falls back to NumPy if unavailable)
xp, np, is_gpu = select_xp(backend="cupy")

# Via environment variable
# export ACE_BACKEND=cupy
xp, np, is_gpu = select_xp()
```

### ace_projector_xp.py
Implements weighted ℓ1 proximal operator and spectral norm projection using the XP backend.

**Key Functions:**
- `soft_threshold_l1w(y, lam, w)` - Weighted soft-threshold operator with KKT certificate
- `kkt_residual_l1w(y, z, lam, w)` - Compute KKT residual
- `project_spectral_ball(K, radius)` - Project matrix onto spectral ball

### ace_runtime_xp.py
Full ACE runtime with ledger integration, KKT checks, and Cauchy decrease validation.

**Usage:**
```python
from multiplicity_core.ace_runtime_xp import ACERuntimeXP, ACEConfigXP
from multiplicity_core.ledger import Ledger

# Initialize
ledger = Ledger()
cfg = ACEConfigXP(lam_l1=0.1, kkt_tol=1e-6)
ace = ACERuntimeXP(ledger, cfg=cfg, backend="numpy", return_numpy=True)

# Execute ACE step
result = ace.ace_step(
    T_t=state_vector,
    F=feedback_term,
    K_prop=kernel_matrix,
    w_l1=weights,
    eps_t=gap_parameter,
    actor_id="actor_1",
)

# Result contains T_next, K_proj, ledger_entry_id, and metrics
```

### scheduler.py
Schedule executor that reads TOML configuration and executes ACE steps in a round-robin pattern across classes, anchors, and columns.

**Usage:**
```bash
# CPU execution
python multiplicity_core/scheduler.py --steps 1024 --backend numpy

# GPU execution (requires CuPy)
ACE_BACKEND=cupy python multiplicity_core/scheduler.py --steps 1024 --backend cupy

# Custom schedule file
python multiplicity_core/scheduler.py --schedule my_schedule.toml --steps 512
```

**Contract:**
The scheduler requires two functions:
1. `proposal(c, a, k) -> (T_t, F, K_prop, w, eps)` - Generate proposal for slot (class, anchor, column)
2. `writeback(c, a, k, T_next)` - Update state after successful ACE step

## Configuration

### atlas_schedule.toml
```toml
# Number of classes, anchors, and columns
n_classes = 12
n_anchors = 6
n_columns = 768

# ACE parameters
lam_l1 = 0.1              # ℓ1 regularization
l1_weight_floor = 1e-6     # Minimum ℓ1 weight
kkt_tol = 1e-6             # KKT tolerance
```

## Features

### GPU Support
- Automatic backend selection (NumPy/CuPy)
- Graceful fallback to NumPy when CuPy is unavailable
- Environment variable configuration (`ACE_BACKEND`)

### Ledger Integration
- All ACE steps logged to ledger with metrics
- PETC stamps for each scheduled slot
- Fail-closed behavior with rejection logging

### Numerical Stability
- KKT certificate for optimality verification
- Cauchy decrease checking
- Spectral norm projection with SVD or power iteration fallback

### Testing
Comprehensive test suite covering:
- Backend selection and fallback
- Soft-threshold operator correctness
- Spectral projection accuracy
- ACE runtime behavior
- Scheduler round-robin logic
- Failure handling

## Requirements

**Mandatory:**
- numpy >= 1.26.4
- tomli (Python < 3.11) or tomllib (Python >= 3.11)

**Optional:**
- cupy (for GPU execution)

## Limits

1. **GPU Requirement:** CuPy must be installed for GPU execution. Without it, code falls back to NumPy.

2. **SVD Performance:** SVD on large matrices can be expensive. Power iteration fallback is implemented but provides approximate results.

3. **Demo Proposal:** The built-in demo proposal treats state as a single vector. Replace with domain-specific proposal/writeback for production use.

## Implementation Notes

### Numpy Import Handling
The repository contains a local `numpy` stub that conflicts with the real numpy package. The ACE modules use careful import patterns to ensure the real numpy is loaded:

- `ace_backend.py` uses path filtering to get real numpy
- `tests/conftest.py` pre-loads real numpy for pytest
- Direct execution of modules works correctly with PYTHONPATH set

### Design Principles
1. **Minimal Surface:** Simple, focused API for backend selection and ACE execution
2. **Fail-Closed:** Violations of KKT or Cauchy conditions raise `FailClosed` exception
3. **Observable:** All operations logged to ledger with full metrics
4. **Composable:** Backend, projector, runtime, and scheduler are independent components
