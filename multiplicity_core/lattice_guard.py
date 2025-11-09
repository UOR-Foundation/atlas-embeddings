"""
LatticeGuard — enforce Atlas boundary substrate addressing.

Guards step contexts by validating and enriching with lattice coordinates.
Ensures all addressing respects the 96×12,288 boundary lattice structure.
"""
from __future__ import annotations

from typing import Dict, Any
from multiplicity_core.boundary_lattice import (
    CLASSES,
    ANCHORS,
    ORBIT,
    decode,
    verify_address,
    lin_index,
)


def encode(class_id: int, anchor: int, v_bits: int) -> int:
    """Encode (class_id, anchor, v_bits) to linear coordinate index.
    
    Args:
        class_id: Class identifier in [0, CLASSES-1]
        anchor: Anchor index in [0, ANCHORS-1]
        v_bits: Orbit element in [0, ORBIT-1]
    
    Returns:
        Linear coordinate index
    
    Raises:
        ValueError: If any parameter is out of bounds
    """
    if not (0 <= class_id < CLASSES):
        raise ValueError("bad class")
    if not (0 <= anchor < ANCHORS):
        raise ValueError("bad anchor")
    if not (0 <= v_bits < ORBIT):
        raise ValueError("bad v_bits")
    return lin_index(anchor, v_bits)


def guard_context(ctx: Dict[str, Any]) -> Dict[str, Any]:
    """Validate and enrich a step context with lattice coordinates.
    
    Expects ctx["class"], ctx["coord"] or ctx["anchor"], ctx["v_bits"].
    Returns enriched dict with row/col and normalized coord index.
    
    Args:
        ctx: Context dictionary with at least "class" and either "coord" 
             or both "anchor" and "v_bits"
    
    Returns:
        Enriched context with coord, anchor, v_bits, row, col
    
    Raises:
        ValueError: If required keys are missing or values are invalid
    """
    if "class" not in ctx:
        raise ValueError("missing class in context")
    
    # Handle boolean class values (convert True/False to int)
    c = int(ctx["class"]) if not isinstance(ctx["class"], bool) else int(ctx["class"])
    
    if "coord" in ctx:
        idx = int(ctx["coord"])  # linear index
    elif ("anchor" in ctx) and ("v_bits" in ctx):
        idx = encode(c, int(ctx["anchor"]), int(ctx["v_bits"]))
    else:
        raise ValueError("context must include either coord or (anchor,v_bits)")
    
    verify_address(c, idx)
    d = decode(c, idx)
    
    out = dict(ctx)
    out.update({
        "coord": d.coord_idx,
        "anchor": d.anchor,
        "v_bits": d.v_bits,
        "row": d.row,
        "col": d.col,
    })
    
    return out


__all__ = [
    "encode",
    "guard_context",
]
