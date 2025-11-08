# Multiplicity Core Architecture

This module implements the core architectural primitives:

- **Lane layout**: one lane per integer index `n`, with per-class buffers `c_n(g)`.
- **Toggle streams** `E: N -> B*`: boolean schedules gating per-lane updates.
- **Quantizer** `q: R* -> Z_96`: real to ring quantization; provides batch ops.
- **ACE safety**: projection onto weighted L1 ball `S_t` for per-step contraction.
- **PETC ledger**: per-op signature chain for lawfulness and reproducibility.
- **Runtime**: multi-class switching, ingest + quantize + write, ACE projection hook.

## Quickstart

```bash
python -m pip install -e .
pytest -q tests/test_ace.py tests/test_quantizer.py tests/test_petc_ledger.py tests/test_lanes.py tests/test_runtime_switching.py
```

## Notes

* Hecke/replicability and Π-kernel adapters are intentionally out of scope here. This is the minimal core.
* Z_96 is implemented as a ring quantizer with configurable scale/bias.
* ACE uses a weighted \ell_1 projection with a sort-based soft-threshold.
