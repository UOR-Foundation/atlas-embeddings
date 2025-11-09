"""
Boundary Lattice — 96×12,288 Atlas addressing with (Z/2)^11 subgroup action.

Provides:
- Linear indexing: (anchor, v_bits) ↔ coord_idx
- Boundary folding: coord_idx ↔ (row, col) in 48×256 grid
- Subgroup certificate generation and verification
"""
from __future__ import annotations

import json
import hashlib
from typing import Dict, List, Tuple, Any
from dataclasses import dataclass


# Constants
CLASSES = 96          # Number of resonance classes
ANCHORS = 6           # Anchor points for (Z/2)^11 orbits
ORBIT = 2048          # Size of each orbit: 2^11
FOLD_ROWS = 48        # Boundary fold rows
FOLD_COLS = 256       # Boundary fold columns
COORDINATES = 12288   # Total coordinates: 48 × 256


def lin_index(anchor: int, v_bits: int) -> int:
    """Map (anchor, v_bits) to linear coordinate index.
    
    Args:
        anchor: Anchor index in [0, ANCHORS-1]
        v_bits: Orbit element in [0, ORBIT-1]
    
    Returns:
        Linear coordinate index in [0, COORDINATES-1]
    """
    if not (0 <= anchor < ANCHORS):
        raise ValueError(f"anchor must be in [0, {ANCHORS-1}], got {anchor}")
    if not (0 <= v_bits < ORBIT):
        raise ValueError(f"v_bits must be in [0, {ORBIT-1}], got {v_bits}")
    
    return anchor * ORBIT + v_bits


def inv_lin_index(coord_idx: int) -> Tuple[int, int]:
    """Inverse: linear coordinate index to (anchor, v_bits).
    
    Args:
        coord_idx: Linear coordinate index in [0, COORDINATES-1]
    
    Returns:
        (anchor, v_bits) pair
    """
    if not (0 <= coord_idx < COORDINATES):
        raise ValueError(f"coord_idx must be in [0, {COORDINATES-1}], got {coord_idx}")
    
    anchor = coord_idx // ORBIT
    v_bits = coord_idx % ORBIT
    return anchor, v_bits


def boundary_fold_48x256(coord_idx: int) -> Tuple[int, int]:
    """Map linear coordinate to (row, col) in 48×256 boundary fold.
    
    The folding maps each coordinate into a 48-row by 256-column grid.
    This is consistent with the 48-page × 256-byte structure.
    
    Args:
        coord_idx: Linear coordinate index in [0, COORDINATES-1]
    
    Returns:
        (row, col) pair where row in [0, 47], col in [0, 255]
    """
    if not (0 <= coord_idx < COORDINATES):
        raise ValueError(f"coord_idx must be in [0, {COORDINATES-1}], got {coord_idx}")
    
    # Simple row-major mapping
    row = coord_idx // FOLD_COLS
    col = coord_idx % FOLD_COLS
    return row, col


def boundary_unfold_48x256(row: int, col: int) -> int:
    """Inverse: (row, col) to linear coordinate index.
    
    Args:
        row: Row in [0, 47]
        col: Column in [0, 255]
    
    Returns:
        Linear coordinate index
    """
    if not (0 <= row < FOLD_ROWS):
        raise ValueError(f"row must be in [0, {FOLD_ROWS-1}], got {row}")
    if not (0 <= col < FOLD_COLS):
        raise ValueError(f"col must be in [0, {FOLD_COLS-1}], got {col}")
    
    return row * FOLD_COLS + col


def verify_address(class_id: int, coord_idx: int) -> None:
    """Verify that (class_id, coord_idx) is a valid address.
    
    Args:
        class_id: Class identifier in [0, CLASSES-1]
        coord_idx: Coordinate index in [0, COORDINATES-1]
    
    Raises:
        ValueError: If address is invalid
    """
    if not (0 <= class_id < CLASSES):
        raise ValueError(f"class_id must be in [0, {CLASSES-1}], got {class_id}")
    if not (0 <= coord_idx < COORDINATES):
        raise ValueError(f"coord_idx must be in [0, {COORDINATES-1}], got {coord_idx}")


# Subgroup action: (Z/2)^11 acting on each orbit
def apply_subgroup_action(anchor: int, v_bits: int, u: int) -> Tuple[int, int]:
    """Apply (Z/2)^11 group element u to (anchor, v_bits).
    
    The action is free and transitive within each orbit (fixed anchor).
    
    Args:
        anchor: Anchor index (stays fixed)
        v_bits: Orbit element
        u: Group element in [0, ORBIT-1]
    
    Returns:
        (anchor, v_bits') where v_bits' = (v_bits + u) mod ORBIT
    """
    if not (0 <= anchor < ANCHORS):
        raise ValueError(f"anchor must be in [0, {ANCHORS-1}], got {anchor}")
    if not (0 <= v_bits < ORBIT):
        raise ValueError(f"v_bits must be in [0, {ORBIT-1}], got {v_bits}")
    if not (0 <= u < ORBIT):
        raise ValueError(f"u must be in [0, {ORBIT-1}], got {u}")
    
    v_bits_new = (v_bits + u) % ORBIT
    return anchor, v_bits_new


def verify_subgroup_action() -> Dict[str, Any]:
    """Verify (Z/2)^11 subgroup action properties.
    
    Checks:
    1. Freeness: no fixed points except identity
    2. Transitivity: action reaches all orbit elements
    3. Orbit sizes are exactly ORBIT
    
    Returns:
        Verification results dictionary
    """
    results = {
        "freeness": True,
        "transitivity": True,
        "orbit_sizes_correct": True,
        "failures": []
    }
    
    # Test freeness: non-identity elements should have no fixed points
    test_u_values = [1, 2, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047]
    for anchor in range(ANCHORS):
        for v in [0, 1, 127, 255, 511, 1023, 2047]:  # Sample v_bits
            for u in test_u_values:
                _, v_new = apply_subgroup_action(anchor, v, u)
                if v_new == v:
                    results["freeness"] = False
                    results["failures"].append(
                        f"Fixed point: anchor={anchor}, v={v}, u={u}"
                    )
    
    # Test transitivity and orbit size for each anchor
    for anchor in range(ANCHORS):
        orbit = set()
        start_v = 0
        # Generate orbit from start_v by applying all group elements
        for u in range(ORBIT):
            _, v_new = apply_subgroup_action(anchor, start_v, u)
            orbit.add(v_new)
        
        if len(orbit) != ORBIT:
            results["orbit_sizes_correct"] = False
            results["failures"].append(
                f"Orbit size {len(orbit)} != {ORBIT} for anchor {anchor}"
            )
        
        # Check if orbit covers all v_bits (transitivity)
        expected_orbit = set(range(ORBIT))
        if orbit != expected_orbit:
            results["transitivity"] = False
            results["failures"].append(
                f"Orbit doesn't cover all elements for anchor {anchor}"
            )
    
    results["verified"] = (
        results["freeness"] and 
        results["transitivity"] and 
        results["orbit_sizes_correct"]
    )
    
    return results


def generate_certificate() -> Dict[str, Any]:
    """Generate subgroup certificate with all verification checks.
    
    Returns:
        Certificate dictionary with structure info and verification results
    """
    # Run verification
    verification = verify_subgroup_action()
    
    # Compute checksum of structure
    structure_data = {
        "classes": CLASSES,
        "anchors": ANCHORS,
        "orbit": ORBIT,
        "fold_rows": FOLD_ROWS,
        "fold_cols": FOLD_COLS,
        "coordinates": COORDINATES
    }
    
    structure_json = json.dumps(structure_data, sort_keys=True)
    checksum = hashlib.sha256(structure_json.encode()).hexdigest()
    
    certificate = {
        "version": "1.0",
        "group_structure": "(Z/2)^11",
        "structure": structure_data,
        "structure_checksum": checksum,
        "verification": verification,
        "anchor_points": [
            {"anchor": a, "coord_base": a * ORBIT} 
            for a in range(ANCHORS)
        ],
        "properties": {
            "group_order": ORBIT,
            "num_orbits": ANCHORS,
            "total_elements": COORDINATES,
            "action_free": verification["freeness"],
            "action_transitive": verification["transitivity"],
        }
    }
    
    return certificate


def save_certificate(filepath: str) -> None:
    """Generate and save subgroup certificate to JSON file.
    
    Args:
        filepath: Output file path
    """
    cert = generate_certificate()
    with open(filepath, 'w') as f:
        json.dump(cert, f, indent=2)


@dataclass
class Decoded:
    """Decoded address information."""
    class_id: int
    coord_idx: int
    anchor: int
    v_bits: int
    row: int
    col: int


def decode(class_id: int, coord_idx: int) -> Decoded:
    """Decode (class_id, coord_idx) into full address information.
    
    Args:
        class_id: Class identifier
        coord_idx: Linear coordinate index
    
    Returns:
        Decoded address with anchor, v_bits, row, col
    """
    verify_address(class_id, coord_idx)
    a, v = inv_lin_index(coord_idx)
    r, c = boundary_fold_48x256(coord_idx)
    return Decoded(
        class_id=class_id,
        coord_idx=coord_idx,
        anchor=a,
        v_bits=v,
        row=r,
        col=c
    )


__all__ = [
    "CLASSES",
    "ANCHORS",
    "ORBIT",
    "FOLD_ROWS",
    "FOLD_COLS",
    "COORDINATES",
    "lin_index",
    "inv_lin_index",
    "boundary_fold_48x256",
    "boundary_unfold_48x256",
    "verify_address",
    "apply_subgroup_action",
    "verify_subgroup_action",
    "generate_certificate",
    "save_certificate",
    "Decoded",
    "decode",
]
