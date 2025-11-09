"""
Python bindings for the UOR Prime Structure FFI

This module provides Python bindings to the UOR Prime Structure
mathematical framework through its C FFI interface.
"""

import ctypes
import os
from pathlib import Path
from typing import Tuple

# Locate the FFI library
_ffi_dir = Path(__file__).parent.parent.parent.parent / "ffi" / "c"

# Try to load the shared library first, fall back to inline C code
try:
    # Try to load compiled shared library
    _lib_path = Path(__file__).parent.parent.parent.parent / ".lake" / "build" / "lib" / "libuor_minimal.so"
    if not _lib_path.exists():
        # Try alternative location
        _lib_path = _ffi_dir / "libuor_minimal.so"
    
    _lib = ctypes.CDLL(str(_lib_path))
except (OSError, FileNotFoundError):
    # Fall back to compiling minimal wrapper
    import tempfile
    import subprocess
    
    _wrapper_c = _ffi_dir / "minimal_wrapper.c"
    if _wrapper_c.exists():
        with tempfile.NamedTemporaryFile(suffix=".so", delete=False) as tmp:
            subprocess.run([
                "gcc", "-shared", "-fPIC", "-O2",
                "-I", str(_ffi_dir),
                "-o", tmp.name,
                str(_wrapper_c)
            ], check=True)
            _lib = ctypes.CDLL(tmp.name)
    else:
        raise ImportError("Could not find or compile UOR FFI library")

# Define function signatures using minimal wrapper names
_lib.lean_uor_pages_minimal.restype = ctypes.c_uint32
_lib.lean_uor_pages_minimal.argtypes = []

_lib.lean_uor_bytes_minimal.restype = ctypes.c_uint32
_lib.lean_uor_bytes_minimal.argtypes = []

_lib.lean_uor_rclasses_minimal.restype = ctypes.c_uint32
_lib.lean_uor_rclasses_minimal.argtypes = []

_lib.lean_uor_r96_classify_minimal.restype = ctypes.c_uint8
_lib.lean_uor_r96_classify_minimal.argtypes = [ctypes.c_uint8]

_lib.lean_uor_phi_encode_minimal.restype = ctypes.c_uint32
_lib.lean_uor_phi_encode_minimal.argtypes = [ctypes.c_uint8, ctypes.c_uint8]

_lib.lean_uor_phi_page_minimal.restype = ctypes.c_uint8
_lib.lean_uor_phi_page_minimal.argtypes = [ctypes.c_uint32]

_lib.lean_uor_phi_byte_minimal.restype = ctypes.c_uint8
_lib.lean_uor_phi_byte_minimal.argtypes = [ctypes.c_uint32]

_lib.lean_uor_truth_zero_minimal.restype = ctypes.c_uint8
_lib.lean_uor_truth_zero_minimal.argtypes = [ctypes.c_uint32]

_lib.lean_uor_truth_add_minimal.restype = ctypes.c_uint8
_lib.lean_uor_truth_add_minimal.argtypes = [ctypes.c_uint32, ctypes.c_uint32]

# Constants
PAGES = 48
BYTES = 256
RCLASSES = 96
TOTAL_ELEMENTS = PAGES * BYTES
COMPRESSION_RATIO = RCLASSES / BYTES

def pages() -> int:
    """Returns the number of pages (48)"""
    return _lib.lean_uor_pages_minimal()

def bytes_per_page() -> int:
    """Returns the number of bytes per page (256)"""
    return _lib.lean_uor_bytes_minimal()

def rclasses() -> int:
    """Returns the number of resonance classes (96)"""
    return _lib.lean_uor_rclasses_minimal()

def r96_classify(b: int) -> int:
    """
    Classifies a byte into one of 96 resonance classes
    
    Args:
        b: Byte value (0-255)
    
    Returns:
        Resonance class (0-95)
    """
    if not 0 <= b <= 255:
        raise ValueError(f"Byte value must be 0-255, got {b}")
    return _lib.lean_uor_r96_classify_minimal(b)

def phi_encode(page: int, byte: int) -> int:
    """
    Encodes page and byte coordinates into a 32-bit code
    
    Args:
        page: Page number (0-47)
        byte: Byte value (0-255)
    
    Returns:
        32-bit encoded value
    """
    if not 0 <= page <= 255:
        raise ValueError(f"Page must be 0-255, got {page}")
    if not 0 <= byte <= 255:
        raise ValueError(f"Byte must be 0-255, got {byte}")
    return _lib.lean_uor_phi_encode_minimal(page, byte)

def phi_decode(code: int) -> Tuple[int, int]:
    """
    Decodes a 32-bit code into page and byte components
    
    Args:
        code: 32-bit encoded value
    
    Returns:
        Tuple of (page, byte)
    """
    page = _lib.lean_uor_phi_page_minimal(code)
    byte = _lib.lean_uor_phi_byte_minimal(code)
    return page, byte

def phi_page(code: int) -> int:
    """Extracts the page component from a Phi code"""
    return _lib.lean_uor_phi_page_minimal(code)

def phi_byte(code: int) -> int:
    """Extracts the byte component from a Phi code"""
    return _lib.lean_uor_phi_byte_minimal(code)

def truth_zero(budget: int) -> bool:
    """
    Checks if a budget value represents truth (conservation)
    
    Args:
        budget: Value to check
    
    Returns:
        True if budget is zero (truth), False otherwise
    """
    return bool(_lib.lean_uor_truth_zero_minimal(budget))

def truth_add(a: int, b: int) -> bool:
    """
    Checks if the sum of two values represents truth
    
    Args:
        a: First value
        b: Second value
    
    Returns:
        True if sum is zero (truth), False otherwise
    """
    return bool(_lib.lean_uor_truth_add_minimal(a, b))

class PhiCoordinate:
    """A coordinate in the Phi-Atlas boundary encoding"""
    
    def __init__(self, page: int, byte: int):
        """
        Create a new PhiCoordinate
        
        Args:
            page: Page number (0-47, will be taken modulo 48)
            byte: Byte value (0-255)
        """
        self.page = page % 48
        self.byte = byte & 0xFF
    
    def encode(self) -> int:
        """Encode the coordinate to a 32-bit code"""
        return phi_encode(self.page, self.byte)
    
    @classmethod
    def decode(cls, code: int) -> 'PhiCoordinate':
        """Decode a 32-bit code to a PhiCoordinate"""
        page, byte = phi_decode(code)
        return cls(page, byte)
    
    def __repr__(self) -> str:
        return f"Φ({self.page},{self.byte})"
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, PhiCoordinate):
            return False
        return self.page == other.page and self.byte == other.byte
    
    def __hash__(self) -> int:
        return hash((self.page, self.byte))

class ResonanceClass:
    """A resonance class value"""
    
    def __init__(self, value: int):
        """
        Create a ResonanceClass from a value
        
        Args:
            value: Class value (0-95) or byte to classify (0-255)
        """
        if value < 96:
            self.value = value
        else:
            self.value = r96_classify(value)
    
    @classmethod
    def classify(cls, b: int) -> 'ResonanceClass':
        """Create a ResonanceClass by classifying a byte"""
        return cls(r96_classify(b))
    
    def __repr__(self) -> str:
        return f"R96[{self.value}]"
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, ResonanceClass):
            return False
        return self.value == other.value
    
    def __hash__(self) -> int:
        return hash(self.value)
    
    def __lt__(self, other) -> bool:
        if not isinstance(other, ResonanceClass):
            return NotImplemented
        return self.value < other.value

class Conservation:
    """Conservation checker for truth values"""
    
    @staticmethod
    def is_zero(value: int) -> bool:
        """Check if a value conserves truth (equals zero)"""
        return truth_zero(value)
    
    @staticmethod
    def sum_is_zero(a: int, b: int) -> bool:
        """Check if a sum conserves truth (equals zero)"""
        return truth_add(a, b)

def compression_ratio() -> float:
    """Returns the compression ratio (3/8)"""
    return COMPRESSION_RATIO

def total_elements() -> int:
    """Returns the total number of elements (12,288)"""
    return TOTAL_ELEMENTS