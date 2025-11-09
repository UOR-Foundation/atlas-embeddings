# Sovereignty Gate AEP

Atlas-Embedding Proof system that validates identity sovereignty and access control.

## Overview

The `sovereignty_gate` AEP verifies two critical invariants:

1. **Sovereignty**: Σ_i(t) = 1 for the acting identity (determined via plugin or allowlist)
2. **Forbidden Channels**: All Δ-channels matching forbidden patterns have magnitude ≤ `atol`

## Quick Start

### Prerequisites

- Python 3.10+

### Running

```bash
cd aep_sovereignty_gate
export AEP_ACTOR_ID=alice
python3 runner.py
```

Exit codes:
- `0`: All invariants satisfied (PASS)
- `2`: Invariant violation (FAIL - sigma ≠ 1 or forbidden channel violation)
- `3`: Missing actor_id
- `4`: Sigma plugin error

Results are written to `out/result.json`.

## Configuration

### aep.toml

Main configuration file defining:
- **claim**: AEP metadata (id, kind, description)
- **policy**: Sigma plugin path and allowed identity list
- **evidence**: Path to delta_channels.json
- **forbidden**: Patterns for forbidden Δ-channels

### kernel.atlas

Kernel configuration defining:
- **context**: Default actor_id (overridden by `AEP_ACTOR_ID` env var)
- **probes**: Forbidden channel patterns

## File Structure

```
aep_sovereignty_gate/
├── aep.toml              # Main configuration
├── kernel.atlas          # Kernel configuration
├── runner.py             # Main runner script
├── sigma_plugin.py       # Example sovereignty policy plugin
├── evidence/            # Evidence files
│   └── delta_channels.json  # Δ-channel measurements
└── out/                 # Output directory
    └── result.json      # Execution results
```

## Actor Identity

The actor identity is determined in this order:
1. `AEP_ACTOR_ID` environment variable
2. `kernel.atlas` `[context]` `actor_id` field

At least one must be set, or the runner will exit with code 3.

## Sovereignty Policy

### Using the Allowlist

By default, identities in `aep.toml` `[policy]` `allowed_ids` are granted sovereignty (Σ=1):

```toml
[policy]
allowed_ids = ["alice", "charlie"]
```

### Using a Plugin

For custom sovereignty logic, create a `sigma_plugin.py` file:

```python
def sigma(actor_id: str, t_ms: int) -> int:
    """
    Determine sovereignty for an identity.
    
    Args:
        actor_id: The identity requesting access
        t_ms: Current timestamp in milliseconds
        
    Returns:
        1 if sovereign, 0 otherwise
    """
    # Custom logic here
    if actor_id == "alice":
        return 1
    return 0
```

Reference it in `aep.toml`:
```toml
[policy]
sigma_plugin = "sigma_plugin.py"
```

The plugin takes precedence over the allowlist.

## Evidence Format

### delta_channels.json

Dictionary mapping channel names to values:

```json
{
  "channel_a": 0.0,
  "Δ/forbidden_1": 0.0,
  "forbidden/test": 0.0,
  "allowed/channel": 1e-15
}
```

## Output Format

```json
{
  "status": "pass",
  "ok_sigma": true,
  "ok_forbidden_channels": true,
  "sigma": 1,
  "actor_id": "alice",
  "delta_violations": [],
  "proof_id": "4d6e299f...",
  "verified": true
}
```

Fields:
- `status`: Overall status ("pass" or "fail")
- `ok_sigma`: Whether Σ = 1
- `ok_forbidden_channels`: Whether forbidden channels are zero
- `sigma`: Computed sigma value (0 or 1)
- `actor_id`: The identity that was checked
- `delta_violations`: List of channel violations (empty if pass)
- `proof_id`: Deterministic proof identifier
- `verified`: Whether proof verification succeeded

## Examples

### Pass Case: Authorized Actor

```bash
export AEP_ACTOR_ID=alice
python3 runner.py
# Exit code: 0
```

### Fail Case: Unauthorized Actor

```bash
export AEP_ACTOR_ID=bob
python3 runner.py
# Exit code: 2
```

### Using Default Actor

```bash
# Uses actor_id from kernel.atlas (default: "alice")
python3 runner.py
# Exit code: 0
```

### Custom Plugin

Create `my_policy.py`:
```python
def sigma(actor_id: str, t_ms: int) -> int:
    # Time-based access: only allow during business hours
    import time
    hour = time.localtime(t_ms // 1000).tm_hour
    if 9 <= hour < 17:
        return 1 if actor_id in ["alice", "bob"] else 0
    return 0
```

Update `aep.toml`:
```toml
[policy]
sigma_plugin = "my_policy.py"
```

## Integration

The runner uses `ProofManager` from `multiplicity_core` for deterministic proof generation and verification. Proofs are local hashes and not cryptographically secure by default.

To integrate with blockchain or external verifiers, replace the `ProofManager.submit_on_chain()` stub with your submission logic.

## Forbidden Patterns

Patterns use glob-style matching:
- `Δ/*`: Matches all channels starting with "Δ/"
- `forbidden/*`: Matches all channels starting with "forbidden/"
- `*_restricted`: Matches all channels ending with "_restricted"

Configure in `aep.toml` under `[forbidden]` or `kernel.atlas` under `[probes]`.
