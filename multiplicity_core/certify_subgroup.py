"""
Generate and persist the (Z/2)^11 subgroup certificate for the Atlas boundary lattice.
Writes: subgroup_certificate.json
"""
from __future__ import annotations

from multiplicity_core.boundary_lattice import save_certificate


if __name__ == "__main__":
    save_certificate("subgroup_certificate.json")
    print("wrote subgroup_certificate.json")
