"""
Tests for lattice_guard module.
"""
import pytest
from multiplicity_core.lattice_guard import encode, guard_context
from multiplicity_core.boundary_lattice import CLASSES, ANCHORS, ORBIT


def test_encode():
    """Test encoding function."""
    # Valid encodings
    assert encode(0, 0, 0) == 0
    assert encode(0, 1, 0) == 2048
    assert encode(0, 0, 100) == 100
    assert encode(50, 3, 500) == 6644  # anchor 3 base = 6144, + 500
    
    # Invalid class
    with pytest.raises(ValueError, match="bad class"):
        encode(96, 0, 0)
    
    # Invalid anchor
    with pytest.raises(ValueError, match="bad anchor"):
        encode(0, 6, 0)
    
    # Invalid v_bits
    with pytest.raises(ValueError, match="bad v_bits"):
        encode(0, 0, 2048)


def test_guard_context_with_coord():
    """Test guard_context with coord parameter."""
    ctx = {"class": 5, "coord": 777}
    result = guard_context(ctx)
    
    assert result["class"] == 5
    assert result["coord"] == 777
    assert result["anchor"] == 0
    assert result["v_bits"] == 777
    assert result["row"] == 3
    assert result["col"] == 9


def test_guard_context_with_anchor_vbits():
    """Test guard_context with anchor and v_bits."""
    ctx = {"class": 10, "anchor": 2, "v_bits": 100}
    result = guard_context(ctx)
    
    assert result["class"] == 10
    assert result["anchor"] == 2
    assert result["v_bits"] == 100
    assert result["coord"] == 4196  # anchor 2 base = 4096, + 100
    assert result["row"] == 16
    assert result["col"] == 100


def test_guard_context_preserves_extra_fields():
    """Test that guard_context preserves extra context fields."""
    ctx = {
        "class": 1,
        "coord": 100,
        "extra_field": "should_be_preserved",
        "another": 42
    }
    result = guard_context(ctx)
    
    assert result["extra_field"] == "should_be_preserved"
    assert result["another"] == 42


def test_guard_context_boolean_class():
    """Test guard_context handles boolean class values."""
    # Boolean True -> 1, False -> 0
    ctx_true = {"class": True, "coord": 0}
    result_true = guard_context(ctx_true)
    assert result_true["class"] == 1
    
    ctx_false = {"class": False, "coord": 0}
    result_false = guard_context(ctx_false)
    assert result_false["class"] == 0


def test_guard_context_missing_class():
    """Test guard_context raises on missing class."""
    ctx = {"coord": 100}
    with pytest.raises(ValueError, match="missing class"):
        guard_context(ctx)


def test_guard_context_missing_coord_and_anchor():
    """Test guard_context raises when neither coord nor anchor/v_bits provided."""
    ctx = {"class": 5}
    with pytest.raises(ValueError, match="context must include either coord"):
        guard_context(ctx)
    
    # Missing v_bits
    ctx = {"class": 5, "anchor": 0}
    with pytest.raises(ValueError, match="context must include either coord"):
        guard_context(ctx)


def test_guard_context_invalid_class():
    """Test guard_context raises on invalid class."""
    ctx = {"class": 96, "coord": 0}
    with pytest.raises(ValueError):
        guard_context(ctx)


def test_guard_context_invalid_coord():
    """Test guard_context raises on invalid coord."""
    ctx = {"class": 0, "coord": 12288}
    with pytest.raises(ValueError):
        guard_context(ctx)


def test_guard_context_invalid_anchor():
    """Test guard_context raises on invalid anchor."""
    ctx = {"class": 0, "anchor": 6, "v_bits": 0}
    with pytest.raises(ValueError):
        guard_context(ctx)


def test_guard_context_invalid_vbits():
    """Test guard_context raises on invalid v_bits."""
    ctx = {"class": 0, "anchor": 0, "v_bits": 2048}
    with pytest.raises(ValueError):
        guard_context(ctx)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
