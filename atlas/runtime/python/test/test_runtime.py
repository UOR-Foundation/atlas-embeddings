#!/usr/bin/env python3
"""
Test suite for UOR Runtime Python enhanced bindings.
"""

import unittest
import sys
import os

# Add src to path for development testing
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

import uor_runtime


class TestConstants(unittest.TestCase):
    """Test module constants."""
    
    def test_pages(self):
        self.assertEqual(uor_runtime.PAGES, 48)
        self.assertEqual(uor_runtime.pages(), 48)
    
    def test_bytes(self):
        self.assertEqual(uor_runtime.BYTES, 256)
        self.assertEqual(uor_runtime.bytes(), 256)
    
    def test_rclasses(self):
        self.assertEqual(uor_runtime.RCLASSES, 96)
        self.assertEqual(uor_runtime.rclasses(), 96)


class TestPhiCoordinate(unittest.TestCase):
    """Test PhiCoordinate class."""
    
    def test_creation(self):
        coord = uor_runtime.PhiCoordinate(3, 16)
        self.assertEqual(coord.page, 3)
        self.assertEqual(coord.byte, 16)
        self.assertEqual(coord.code, (3 << 8) | 16)
    
    def test_from_code(self):
        code = (5 << 8) | 42
        coord = uor_runtime.PhiCoordinate.from_code(code)
        self.assertEqual(coord.page, 5)
        self.assertEqual(coord.byte, 42)
        self.assertEqual(coord.code, code)
    
    def test_validation(self):
        with self.assertRaises(ValueError):
            uor_runtime.PhiCoordinate(48, 0)  # Page out of range
        with self.assertRaises(ValueError):
            uor_runtime.PhiCoordinate(0, 256)  # Byte out of range
        with self.assertRaises(ValueError):
            uor_runtime.PhiCoordinate(-1, 0)  # Negative page
    
    def test_equality(self):
        coord1 = uor_runtime.PhiCoordinate(10, 20)
        coord2 = uor_runtime.PhiCoordinate(10, 20)
        coord3 = uor_runtime.PhiCoordinate(10, 21)
        
        self.assertEqual(coord1, coord2)
        self.assertNotEqual(coord1, coord3)
        self.assertEqual(hash(coord1), hash(coord2))
    
    def test_resonance_class(self):
        coord = uor_runtime.PhiCoordinate(0, 255)
        rc = coord.resonance_class
        self.assertIsInstance(rc, uor_runtime.ResonanceClass)
        self.assertEqual(rc.byte_value, 255)


class TestResonanceClass(unittest.TestCase):
    """Test ResonanceClass."""
    
    def test_creation(self):
        rc = uor_runtime.ResonanceClass(255)
        self.assertEqual(rc.byte_value, 255)
        self.assertEqual(rc.class_id, 63)  # Known value for 255
    
    def test_validation(self):
        with self.assertRaises(ValueError):
            uor_runtime.ResonanceClass(256)
        with self.assertRaises(ValueError):
            uor_runtime.ResonanceClass(-1)
    
    def test_compression_ratio(self):
        rc = uor_runtime.ResonanceClass(0)
        self.assertAlmostEqual(rc.compression_ratio, 0.375)  # 96/256 = 3/8
    
    def test_equivalent_bytes(self):
        rc = uor_runtime.ResonanceClass(0)
        equiv = rc.equivalent_bytes()
        self.assertIn(0, equiv)
        # All equivalent bytes should map to same class
        for b in equiv:
            self.assertEqual(uor_runtime.r96_classify(b), rc.class_id)
    
    def test_equality(self):
        rc1 = uor_runtime.ResonanceClass(0)
        rc2 = uor_runtime.ResonanceClass(0)
        
        self.assertEqual(rc1, rc2)
        self.assertEqual(hash(rc1), hash(rc2))


class TestPrimeStructure(unittest.TestCase):
    """Test PrimeStructure class."""
    
    def test_creation(self):
        ps = uor_runtime.PrimeStructure()
        self.assertEqual(ps.pages, 48)
        self.assertEqual(ps.bytes_per_page, 256)
        self.assertEqual(ps.size, 12288)
        self.assertEqual(len(ps), 12288)
    
    def test_coordinate_creation(self):
        ps = uor_runtime.PrimeStructure()
        coord = ps.coordinate(5, 10)
        self.assertEqual(coord.page, 5)
        self.assertEqual(coord.byte, 10)
    
    def test_iteration(self):
        ps = uor_runtime.PrimeStructure()
        coords = list(ps.all_coordinates())
        self.assertEqual(len(coords), 12288)
        self.assertEqual(coords[0].page, 0)
        self.assertEqual(coords[0].byte, 0)
        self.assertEqual(coords[-1].page, 47)
        self.assertEqual(coords[-1].byte, 255)
    
    def test_page_iteration(self):
        ps = uor_runtime.PrimeStructure()
        page_coords = list(ps.page_coordinates(5))
        self.assertEqual(len(page_coords), 256)
        for coord in page_coords:
            self.assertEqual(coord.page, 5)
    
    def test_resonance_distribution(self):
        ps = uor_runtime.PrimeStructure()
        dist = ps.resonance_distribution()
        self.assertEqual(len(dist), 96)  # Should have 96 classes
        # Total bytes should be 256
        total_bytes = sum(len(bytes_list) for bytes_list in dist.values())
        self.assertEqual(total_bytes, 256)
    
    def test_conservation(self):
        ps = uor_runtime.PrimeStructure()
        self.assertTrue(ps.check_conservation(0))
        self.assertFalse(ps.check_conservation(1))
        self.assertTrue(ps.check_additive_conservation(-5, 5))
        self.assertFalse(ps.check_additive_conservation(3, 4))


class TestModuleFunctions(unittest.TestCase):
    """Test module-level functions."""
    
    def test_r96_classify(self):
        self.assertEqual(uor_runtime.r96_classify(0), 0)
        self.assertEqual(uor_runtime.r96_classify(255), 63)
        # All values should be in range [0, 95]
        for b in range(256):
            cls = uor_runtime.r96_classify(b)
            self.assertGreaterEqual(cls, 0)
            self.assertLess(cls, 96)
    
    def test_phi_encode_decode(self):
        for page in [0, 23, 47]:
            for byte in [0, 127, 255]:
                code = uor_runtime.phi_encode(page, byte)
                decoded_page = uor_runtime.phi_page(code)
                decoded_byte = uor_runtime.phi_byte(code)
                self.assertEqual(decoded_page, page)
                self.assertEqual(decoded_byte, byte)
    
    def test_truth_functions(self):
        self.assertTrue(uor_runtime.truth_zero(0))
        self.assertFalse(uor_runtime.truth_zero(1))
        self.assertFalse(uor_runtime.truth_zero(-1))
        
        self.assertTrue(uor_runtime.truth_add(0, 0))
        self.assertTrue(uor_runtime.truth_add(5, -5))
        self.assertFalse(uor_runtime.truth_add(1, 1))


if __name__ == '__main__':
    unittest.main()