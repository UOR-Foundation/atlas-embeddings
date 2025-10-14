# AEP Runner

This directory hosts the dynamic execution lane for the AEP integration
pipeline. Utilities include:

- `metrics.py` for spectral radius and Neumann tail bounds
- `monitors.py` for contract monitoring hooks
- `witness_checks.py` for witness validations
- `main.py` orchestrating projections, operators, and witness evidence

These modules are intentionally lightweight so they can be reused inside the
CPU simulation lane and mirrored onto hardware backends.
