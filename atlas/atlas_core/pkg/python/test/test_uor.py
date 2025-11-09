"""
Tests for UOR Python FFI bindings
"""

import pytest
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))

import uor

def test_constants():
    """Test that constants match expected values"""
    assert uor.pages() == 48
    assert uor.bytes_per_page() == 256
    assert uor.rclasses() == 96
    assert uor.total_elements() == 12288
    assert abs(uor.compression_ratio() - 3/8) < 0.0001

def test_r96_classifier():
    """Test R96 resonance classifier"""
    # Test specific values
    assert uor.r96_classify(0) == 0
    assert uor.r96_classify(95) == 95
    assert uor.r96_classify(96) == 0  # Periodic
    assert uor.r96_classify(255) == 63
    
    # Test range
    for i in range(256):
        cls = uor.r96_classify(i)
        assert 0 <= cls < 96, f"R96({i}) = {cls} out of range"
    
    # Test periodicity
    for i in range(96):
        assert uor.r96_classify(i) == uor.r96_classify(i + 96)
    
    # Test invalid input
    with pytest.raises(ValueError):
        uor.r96_classify(256)
    with pytest.raises(ValueError):
        uor.r96_classify(-1)

def test_phi_encoding():
    """Test Phi boundary encoding"""
    # Test round-trip
    for page in range(0, 48, 6):  # Sample pages
        for byte in range(0, 256, 17):  # Sample bytes
            code = uor.phi_encode(page, byte)
            decoded_page, decoded_byte = uor.phi_decode(code)
            assert decoded_page == page
            assert decoded_byte == byte
    
    # Test individual extractors
    code = uor.phi_encode(3, 16)
    assert uor.phi_page(code) == 3
    assert uor.phi_byte(code) == 16
    
    # Test modulo behavior
    code = uor.phi_encode(51, 100)  # 51 % 48 = 3
    assert uor.phi_page(code) == 3
    assert uor.phi_byte(code) == 100

def test_phi_coordinate():
    """Test PhiCoordinate class"""
    # Test creation and encoding
    coord = uor.PhiCoordinate(3, 16)
    assert coord.page == 3
    assert coord.byte == 16
    assert str(coord) == "Φ(3,16)"
    
    # Test encoding/decoding
    code = coord.encode()
    decoded = uor.PhiCoordinate.decode(code)
    assert coord == decoded
    
    # Test modulo behavior
    coord2 = uor.PhiCoordinate(51, 300)  # 51 % 48 = 3, 300 & 0xFF = 44
    assert coord2.page == 3
    assert coord2.byte == 44
    
    # Test equality and hashing
    coord3 = uor.PhiCoordinate(3, 16)
    assert coord == coord3
    assert hash(coord) == hash(coord3)
    assert coord != uor.PhiCoordinate(3, 17)

def test_truth_conservation():
    """Test truth/conservation functions"""
    # Test truth zero
    assert uor.truth_zero(0) == True
    assert uor.truth_zero(1) == False
    assert uor.truth_zero(100) == False
    
    # Test truth add
    assert uor.truth_add(0, 0) == True
    assert uor.truth_add(1, 0) == False
    assert uor.truth_add(5, 10) == False
    
    # Test overflow wrapping (MAX + 1 = 0)
    assert uor.truth_add(0xFFFFFFFF, 1) == True

def test_resonance_class():
    """Test ResonanceClass class"""
    # Test direct creation
    rc1 = uor.ResonanceClass(42)
    assert rc1.value == 42
    assert str(rc1) == "R96[42]"
    
    # Test classification
    rc2 = uor.ResonanceClass.classify(100)
    assert rc2.value == 4  # 100 % 96 = 4
    
    # Test auto-classification for values >= 96
    rc3 = uor.ResonanceClass(100)
    assert rc3.value == 4
    
    # Test equality and hashing
    rc4 = uor.ResonanceClass(42)
    assert rc1 == rc4
    assert hash(rc1) == hash(rc4)
    
    # Test ordering
    assert uor.ResonanceClass(10) < uor.ResonanceClass(20)
    assert not (uor.ResonanceClass(20) < uor.ResonanceClass(10))

def test_conservation_class():
    """Test Conservation class"""
    assert uor.Conservation.is_zero(0) == True
    assert uor.Conservation.is_zero(42) == False
    assert uor.Conservation.sum_is_zero(0, 0) == True
    assert uor.Conservation.sum_is_zero(1, 2) == False

def test_all_resonance_classes_produced():
    """Verify that all 96 resonance classes are produced"""
    classes = set()
    for i in range(256):
        rc = uor.ResonanceClass.classify(i)
        classes.add(rc.value)
    
    assert len(classes) == 96
    assert min(classes) == 0
    assert max(classes) == 95

if __name__ == "__main__":
    pytest.main([__file__, "-v"])