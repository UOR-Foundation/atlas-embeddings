"""
Tests for boundary_lattice module.
"""
import pytest
from multiplicity_core.boundary_lattice import (
    CLASSES, ANCHORS, ORBIT, FOLD_ROWS, FOLD_COLS, COORDINATES,
    lin_index, inv_lin_index,
    boundary_fold_48x256, boundary_unfold_48x256,
    verify_address, apply_subgroup_action,
    verify_subgroup_action, generate_certificate,
    decode, Decoded
)


def test_constants():
    """Test that constants are correct."""
    assert CLASSES == 96
    assert ANCHORS == 6
    assert ORBIT == 2048
    assert FOLD_ROWS == 48
    assert FOLD_COLS == 256
    assert COORDINATES == 12288
    assert FOLD_ROWS * FOLD_COLS == COORDINATES
    assert ANCHORS * ORBIT == COORDINATES


def test_lin_index():
    """Test linear indexing."""
    # First anchor, first element
    assert lin_index(0, 0) == 0
    
    # First anchor, last element
    assert lin_index(0, 2047) == 2047
    
    # Second anchor, first element
    assert lin_index(1, 0) == 2048
    
    # Last anchor, last element
    assert lin_index(5, 2047) == 12287
    
    # Out of bounds
    with pytest.raises(ValueError):
        lin_index(6, 0)
    with pytest.raises(ValueError):
        lin_index(0, 2048)


def test_inv_lin_index():
    """Test inverse linear indexing."""
    assert inv_lin_index(0) == (0, 0)
    assert inv_lin_index(2047) == (0, 2047)
    assert inv_lin_index(2048) == (1, 0)
    assert inv_lin_index(12287) == (5, 2047)
    
    # Round-trip
    for a in range(ANCHORS):
        for v in [0, 1, 100, 1023, 2047]:
            idx = lin_index(a, v)
            a_back, v_back = inv_lin_index(idx)
            assert (a_back, v_back) == (a, v)


def test_boundary_fold():
    """Test boundary folding."""
    assert boundary_fold_48x256(0) == (0, 0)
    assert boundary_fold_48x256(255) == (0, 255)
    assert boundary_fold_48x256(256) == (1, 0)
    assert boundary_fold_48x256(12287) == (47, 255)
    
    # Round-trip
    for coord in [0, 100, 1000, 5000, 12287]:
        r, c = boundary_fold_48x256(coord)
        coord_back = boundary_unfold_48x256(r, c)
        assert coord_back == coord


def test_verify_address():
    """Test address verification."""
    # Valid addresses
    verify_address(0, 0)
    verify_address(95, 12287)
    verify_address(50, 5000)
    
    # Invalid class
    with pytest.raises(ValueError):
        verify_address(96, 0)
    
    # Invalid coord
    with pytest.raises(ValueError):
        verify_address(0, 12288)


def test_apply_subgroup_action():
    """Test (Z/2)^11 subgroup action."""
    # Identity element
    assert apply_subgroup_action(0, 0, 0) == (0, 0)
    assert apply_subgroup_action(3, 100, 0) == (3, 100)
    
    # Non-identity elements
    assert apply_subgroup_action(0, 0, 1) == (0, 1)
    assert apply_subgroup_action(0, 0, 2047) == (0, 2047)
    assert apply_subgroup_action(0, 1, 1) == (0, 2)
    
    # Wraparound
    assert apply_subgroup_action(0, 2047, 1) == (0, 0)
    
    # Anchor stays fixed
    for a in range(ANCHORS):
        for u in [0, 1, 100, 2047]:
            a_new, _ = apply_subgroup_action(a, 0, u)
            assert a_new == a


def test_verify_subgroup_action():
    """Test subgroup action verification."""
    results = verify_subgroup_action()
    
    assert results["verified"] is True
    assert results["freeness"] is True
    assert results["transitivity"] is True
    assert results["orbit_sizes_correct"] is True
    assert len(results["failures"]) == 0


def test_generate_certificate():
    """Test certificate generation."""
    cert = generate_certificate()
    
    assert cert["version"] == "1.0"
    assert cert["group_structure"] == "(Z/2)^11"
    assert cert["structure"]["classes"] == CLASSES
    assert cert["structure"]["anchors"] == ANCHORS
    assert cert["structure"]["orbit"] == ORBIT
    
    # Verification should pass
    assert cert["verification"]["verified"] is True
    
    # Properties
    assert cert["properties"]["group_order"] == ORBIT
    assert cert["properties"]["num_orbits"] == ANCHORS
    assert cert["properties"]["total_elements"] == COORDINATES


def test_decode():
    """Test address decoding."""
    # Decode class 0, coord 0
    d = decode(0, 0)
    assert d.class_id == 0
    assert d.coord_idx == 0
    assert d.anchor == 0
    assert d.v_bits == 0
    assert d.row == 0
    assert d.col == 0
    
    # Decode class 5, coord 777
    d = decode(5, 777)
    assert d.class_id == 5
    assert d.coord_idx == 777
    assert d.anchor == 0
    assert d.v_bits == 777
    assert d.row == 3
    assert d.col == 9
    
    # Decode with different anchor
    d = decode(10, 4196)  # anchor=2, v_bits=100
    assert d.class_id == 10
    assert d.coord_idx == 4196
    assert d.anchor == 2
    assert d.v_bits == 100
    assert d.row == 16
    assert d.col == 100


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
