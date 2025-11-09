"""
Tests for Phase 0 index map and policies.
"""

import pytest
from multiplicity_core.phase0_index import (
    INDEX_SIZE,
    NUM_PAGES,
    BYTES_PER_PAGE,
    index_map,
    inverse_index_map,
    make_address,
    decode_address,
    check_projector_admissibility,
    max_admissible_level,
    list_admissible_projectors,
    prime_factors,
    prime_policy_default,
    level_policy_default,
    perm_policy_default,
    validate_phase0_constraints,
    DEFAULT_POLICIES,
)


# ============================================================================
# Test Constants
# ============================================================================

def test_index_size():
    """Test that index size is fixed to 12,288."""
    assert INDEX_SIZE == 12288
    assert NUM_PAGES == 48
    assert BYTES_PER_PAGE == 256
    assert NUM_PAGES * BYTES_PER_PAGE == INDEX_SIZE


# ============================================================================
# Test Index Map
# ============================================================================

def test_index_map_default():
    """Test default index map: page*256 + offset."""
    # First address
    assert index_map(0, 0, 0) == 0
    
    # Last address
    assert index_map(47, 0, 255) == 12287
    
    # Middle addresses
    assert index_map(17, 0, 46) == 17 * 256 + 46
    assert index_map(17, 0, 0x2e) == 17 * 256 + 46
    
    # Belt is metadata in default mode
    assert index_map(17, 5, 46) == index_map(17, 0, 46)


def test_index_map_belt_encoding():
    """Test belt encoding mode: page*(256*B) + belt*256 + offset."""
    # With belt=0, should match default
    assert index_map(17, 0, 46, encode_belt=True) == 17 * 256 + 46
    
    # Belt encoding changes the result
    # For NUM_BELTS=1, belt must be 0
    assert index_map(0, 0, 0, encode_belt=True) == 0
    assert index_map(1, 0, 0, encode_belt=True) == 256


def test_inverse_index_map_default():
    """Test inverse index map."""
    # Boundary cases
    page, belt, offset = inverse_index_map(0)
    assert (page, belt, offset) == (0, 0, 0)
    
    page, belt, offset = inverse_index_map(12287)
    assert (page, belt, offset) == (47, 0, 255)
    
    # Middle case
    page, belt, offset = inverse_index_map(4398)
    assert (page, belt, offset) == (17, 0, 46)
    assert page * 256 + offset == 4398


def test_index_map_roundtrip():
    """Test that index_map and inverse_index_map are inverses."""
    for page in [0, 1, 17, 47]:
        for offset in [0, 1, 46, 255]:
            idx = index_map(page, 0, offset)
            p, b, o = inverse_index_map(idx)
            assert (p, b, o) == (page, 0, offset)
            assert index_map(p, b, o) == idx


def test_make_address():
    """Test address creation."""
    addr = make_address(17, 0, 46)
    assert addr.page == 17
    assert addr.belt == 0
    assert addr.offset == 46
    assert addr.linear_index == 4398


def test_decode_address():
    """Test address decoding."""
    addr = decode_address(4398)
    assert addr.page == 17
    assert addr.belt == 0
    assert addr.offset == 46
    assert addr.linear_index == 4398


def test_address_roundtrip():
    """Test address creation and decoding roundtrip."""
    addr1 = make_address(17, 0, 46)
    addr2 = decode_address(addr1.linear_index)
    assert addr1.page == addr2.page
    assert addr1.offset == addr2.offset
    assert addr1.linear_index == addr2.linear_index


# ============================================================================
# Test Projector Admissibility
# ============================================================================

def test_prime_factors():
    """Test prime factorization."""
    assert prime_factors(12288) == {2: 12, 3: 1}
    assert prime_factors(1) == {}
    assert prime_factors(2) == {2: 1}
    assert prime_factors(3) == {3: 1}
    assert prime_factors(12) == {2: 2, 3: 1}


def test_check_projector_admissibility():
    """Test projector admissibility check."""
    # 12288 = 2^12 * 3^1
    
    # Should be admissible
    assert check_projector_admissibility(2, 1, INDEX_SIZE) == True
    assert check_projector_admissibility(2, 12, INDEX_SIZE) == True
    assert check_projector_admissibility(3, 1, INDEX_SIZE) == True
    
    # Should not be admissible
    assert check_projector_admissibility(2, 13, INDEX_SIZE) == False  # 2^13 does not divide 12288
    assert check_projector_admissibility(3, 2, INDEX_SIZE) == False   # 3^2 does not divide 12288
    assert check_projector_admissibility(5, 1, INDEX_SIZE) == False   # 5 does not divide 12288


def test_max_admissible_level():
    """Test finding maximum admissible level."""
    assert max_admissible_level(2, INDEX_SIZE) == 12
    assert max_admissible_level(3, INDEX_SIZE) == 1
    assert max_admissible_level(5, INDEX_SIZE) == 0


def test_list_admissible_projectors():
    """Test listing admissible projectors."""
    projectors = list_admissible_projectors(INDEX_SIZE, max_prime=5)
    
    # Should include all (p, r) where p^r | 12288 and p <= 5
    expected = []
    for r in range(1, 13):  # 2^1 through 2^12
        expected.append((2, r))
    expected.append((3, 1))  # 3^1
    
    assert projectors == expected


# ============================================================================
# Test Policies (UNPROVEN)
# ============================================================================

def test_prime_policy_default():
    """Test default prime policy."""
    # Default: p=3 for all modalities
    assert prime_policy_default(0) == 3
    assert prime_policy_default(1) == 3
    assert prime_policy_default(2) == 3


def test_level_policy_default():
    """Test default level policy."""
    # Default: r=1 for all modalities
    assert level_policy_default(0) == 1
    assert level_policy_default(1) == 1
    assert level_policy_default(2) == 1


def test_perm_policy_default():
    """Test default permutation policy."""
    # Default: identity (empty list)
    assert perm_policy_default(0) == []
    assert perm_policy_default(1) == []
    assert perm_policy_default(2) == []


def test_default_policies_unproven():
    """Test that default policies are marked UNPROVEN."""
    assert DEFAULT_POLICIES.status == "UNPROVEN"


# ============================================================================
# Test Validation
# ============================================================================

def test_validate_phase0_constraints():
    """Test Phase 0 validation."""
    results = validate_phase0_constraints()
    
    assert results["index_size"] == 12288
    assert results["index_size_check"] == True
    assert results["pages"] == 48
    assert results["bytes_per_page"] == 256
    assert results["size_consistency"] == True
    assert results["factorization"] == {2: 12, 3: 1}
    assert results["policies_status"] == "UNPROVEN"


# ============================================================================
# Test Edge Cases
# ============================================================================

def test_index_map_bounds():
    """Test index map boundary validation."""
    # Valid boundaries
    assert index_map(0, 0, 0) == 0
    assert index_map(47, 0, 255) == 12287
    
    # Invalid page
    with pytest.raises(ValueError):
        index_map(-1, 0, 0)
    with pytest.raises(ValueError):
        index_map(48, 0, 0)
    
    # Invalid offset
    with pytest.raises(ValueError):
        index_map(0, 0, -1)
    with pytest.raises(ValueError):
        index_map(0, 0, 256)


def test_inverse_index_map_bounds():
    """Test inverse index map boundary validation."""
    # Valid boundaries
    inverse_index_map(0)
    inverse_index_map(12287)
    
    # Invalid indices
    with pytest.raises(ValueError):
        inverse_index_map(-1)
    with pytest.raises(ValueError):
        inverse_index_map(12288)


# ============================================================================
# Compatibility Tests (with existing boundary_lattice)
# ============================================================================

def test_compatibility_with_boundary_lattice():
    """Test that phase0_index is compatible with boundary_lattice."""
    from multiplicity_core.boundary_lattice import (
        COORDINATES,
        FOLD_ROWS,
        FOLD_COLS,
        boundary_fold_48x256,
        boundary_unfold_48x256,
    )
    
    # Check that constants match
    assert INDEX_SIZE == COORDINATES
    assert NUM_PAGES == FOLD_ROWS
    assert BYTES_PER_PAGE == FOLD_COLS
    
    # Check that our index_map matches boundary_fold/unfold
    for idx in [0, 4398, 12287]:
        row, col = boundary_fold_48x256(idx)
        page, belt, offset = inverse_index_map(idx)
        
        # row should match page, col should match offset
        assert row == page
        assert col == offset
        
        # Roundtrip through boundary_unfold
        idx2 = boundary_unfold_48x256(row, col)
        assert idx2 == idx
