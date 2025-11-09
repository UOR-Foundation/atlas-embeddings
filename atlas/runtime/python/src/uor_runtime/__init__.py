"""
UOR Runtime Python - Enhanced bindings with rich types and comprehensive API.

This module provides high-level, Pythonic access to the UOR Prime Structure
through object-oriented interfaces and comprehensive error handling.
"""

from typing import Iterator, Tuple, List, Optional
from . import _core

__version__ = "1.0.0"
__all__ = [
    'PhiCoordinate', 'ResonanceClass', 'PrimeStructure',
    'PAGES', 'BYTES', 'RCLASSES',
    'pages', 'bytes', 'rclasses', 'r96_classify',
    'phi_encode', 'phi_page', 'phi_byte',
    'truth_zero', 'truth_add'
]

# Constants
PAGES = _core.pages()
BYTES = _core.bytes()  
RCLASSES = _core.rclasses()

# Direct function exports (for compatibility)
pages = _core.pages
bytes = _core.bytes
rclasses = _core.rclasses
r96_classify = _core.r96_classify
phi_encode = _core.phi_encode
phi_page = _core.phi_page
phi_byte = _core.phi_byte
truth_zero = _core.truth_zero
truth_add = _core.truth_add


class PhiCoordinate:
    """
    Represents a coordinate in the Φ-Atlas-12288 structure.
    Manages page/byte encoding with validation and convenience methods.
    """
    
    def __init__(self, page: int, byte: int):
        """Initialize a Phi coordinate with validation."""
        if not 0 <= page < PAGES:
            raise ValueError(f"Page must be in range [0, {PAGES-1}], got {page}")
        if not 0 <= byte < BYTES:
            raise ValueError(f"Byte must be in range [0, {BYTES-1}], got {byte}")
        
        self._page = page
        self._byte = byte
        self._code = _core.phi_encode(page, byte)
    
    @classmethod
    def from_code(cls, code: int) -> 'PhiCoordinate':
        """Create coordinate from encoded value."""
        page = _core.phi_page(code)
        byte = _core.phi_byte(code)
        return cls(page, byte)
    
    @property
    def page(self) -> int:
        """Get page component."""
        return self._page
    
    @property
    def byte(self) -> int:
        """Get byte component."""
        return self._byte
    
    @property
    def code(self) -> int:
        """Get encoded representation."""
        return self._code
    
    @property
    def resonance_class(self) -> 'ResonanceClass':
        """Get the resonance class for this coordinate's byte value."""
        return ResonanceClass(self._byte)
    
    def __repr__(self) -> str:
        return f"PhiCoordinate(page={self._page}, byte={self._byte})"
    
    def __str__(self) -> str:
        return f"Φ({self._page}, {self._byte})"
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, PhiCoordinate):
            return False
        return self._code == other._code
    
    def __hash__(self) -> int:
        return hash(self._code)


class ResonanceClass:
    """
    Represents an R96 resonance classification.
    Provides analysis and properties of resonance classes.
    """
    
    def __init__(self, byte_value: int):
        """Initialize from a byte value."""
        if not 0 <= byte_value < 256:
            raise ValueError(f"Byte value must be in range [0, 255], got {byte_value}")
        
        self._byte = byte_value
        self._class = _core.r96_classify(byte_value)
    
    @property
    def byte_value(self) -> int:
        """Original byte value."""
        return self._byte
    
    @property
    def class_id(self) -> int:
        """Resonance class ID [0, 95]."""
        return self._class
    
    @property
    def compression_ratio(self) -> float:
        """Get compression ratio (3/8 = 0.375)."""
        return RCLASSES / 256
    
    def equivalent_bytes(self) -> List[int]:
        """Find all bytes that map to the same resonance class."""
        return [b for b in range(256) if _core.r96_classify(b) == self._class]
    
    def __repr__(self) -> str:
        return f"ResonanceClass(byte={self._byte}, class={self._class})"
    
    def __str__(self) -> str:
        return f"R96[{self._class}]"
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, ResonanceClass):
            return False
        return self._class == other._class
    
    def __hash__(self) -> int:
        return hash(self._class)


class PrimeStructure:
    """
    High-level interface to the complete Prime Structure.
    Provides iteration, analysis, and conservation checking.
    """
    
    def __init__(self):
        """Initialize Prime Structure interface."""
        self._pages = PAGES
        self._bytes = BYTES
        self._size = PAGES * BYTES  # 12,288
    
    @property
    def size(self) -> int:
        """Total number of elements (12,288)."""
        return self._size
    
    @property
    def pages(self) -> int:
        """Number of pages (48)."""
        return self._pages
    
    @property
    def bytes_per_page(self) -> int:
        """Bytes per page (256)."""
        return self._bytes
    
    def coordinate(self, page: int, byte: int) -> PhiCoordinate:
        """Create a coordinate with validation."""
        return PhiCoordinate(page, byte)
    
    def all_coordinates(self) -> Iterator[PhiCoordinate]:
        """Iterate over all coordinates in the structure."""
        for page in range(self._pages):
            for byte in range(self._bytes):
                yield PhiCoordinate(page, byte)
    
    def page_coordinates(self, page: int) -> Iterator[PhiCoordinate]:
        """Iterate over all coordinates in a specific page."""
        if not 0 <= page < self._pages:
            raise ValueError(f"Page must be in range [0, {self._pages-1}]")
        for byte in range(self._bytes):
            yield PhiCoordinate(page, byte)
    
    def resonance_distribution(self) -> dict:
        """Analyze distribution of resonance classes."""
        distribution = {}
        for byte in range(256):
            rc = ResonanceClass(byte)
            class_id = rc.class_id
            if class_id not in distribution:
                distribution[class_id] = []
            distribution[class_id].append(byte)
        return distribution
    
    def check_conservation(self, budget: int) -> bool:
        """Check if budget represents truth (conservation at 0)."""
        return _core.truth_zero(budget)
    
    def check_additive_conservation(self, a: int, b: int) -> bool:
        """Check if two values sum to conservation."""
        return _core.truth_add(a, b)
    
    def __repr__(self) -> str:
        return f"PrimeStructure(pages={self._pages}, bytes={self._bytes}, size={self._size})"
    
    def __str__(self) -> str:
        return f"Φ-Atlas-12288 Prime Structure"
    
    def __len__(self) -> int:
        return self._size
    
    def __iter__(self) -> Iterator[PhiCoordinate]:
        """Iterate over all coordinates."""
        return self.all_coordinates()


# Module-level convenience instance
structure = PrimeStructure()