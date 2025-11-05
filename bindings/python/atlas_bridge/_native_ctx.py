"""
bindings/python/atlas_bridge/_native_ctx.py
Atlas Bridge Context API v0.2
Python bindings for the Context API from native C library
"""

import ctypes
import os
import platform
from typing import Optional, Tuple

# Determine library name based on platform
def _get_library_name():
    system = platform.system()
    if system == "Windows":
        return "libatlas_bridge_ctx.dll"
    elif system == "Darwin":
        return "libatlas_bridge_ctx.dylib"
    else:
        return "libatlas_bridge_ctx.so"

# Find and load the library
def _load_library():
    """Load the native atlas_bridge_ctx library."""
    lib_name = _get_library_name()
    
    # Try several locations
    search_paths = [
        # Relative to this file
        os.path.join(os.path.dirname(__file__), "..", "..", "..", "atlas_core", "lib"),
        # System paths
        "/usr/local/lib",
        "/usr/lib",
        # Development build
        os.path.join(os.path.dirname(__file__), "..", "..", "..", "build"),
    ]
    
    for path in search_paths:
        full_path = os.path.join(path, lib_name)
        if os.path.exists(full_path):
            return ctypes.CDLL(full_path)
    
    # Try to load from system path
    try:
        return ctypes.CDLL(lib_name)
    except OSError:
        raise RuntimeError(f"Could not find {lib_name}. Please build the library first.")

# Load library (may raise RuntimeError if not found)
try:
    _lib = _load_library()
except RuntimeError as e:
    # Provide helpful error message
    _lib = None
    _load_error = str(e)

def _ensure_loaded():
    """Ensure library is loaded, raise error if not."""
    if _lib is None:
        raise RuntimeError(f"Library not loaded: {_load_error}")

# ============================================================================
# Constants
# ============================================================================

ATLAS_CTX_DEFAULT = 0x00
ATLAS_CTX_ENABLE_TWIRL = 0x01
ATLAS_CTX_ENABLE_LIFT = 0x02
ATLAS_CTX_VERBOSE = 0x04

# ============================================================================
# Structures
# ============================================================================

class AtlasContextConfig(ctypes.Structure):
    """Configuration parameters for Atlas Bridge Context."""
    _fields_ = [
        ("flags", ctypes.c_uint32),
        ("block_size", ctypes.c_uint32),
        ("n_qubits", ctypes.c_uint32),
        ("twirl_gens", ctypes.c_uint32),
        ("epsilon", ctypes.c_double),
    ]

class AtlasContextDiagnostics(ctypes.Structure):
    """Diagnostics structure for Atlas Bridge Context."""
    _fields_ = [
        ("twirl_idempotency", ctypes.c_double),
        ("lift_mass", ctypes.c_double),
        ("op_count", ctypes.c_uint64),
        ("last_residual", ctypes.c_double),
    ]

# ============================================================================
# Function Signatures
# ============================================================================

if _lib:
    # Context lifecycle
    _lib.atlas_ctx_new.argtypes = [ctypes.POINTER(AtlasContextConfig)]
    _lib.atlas_ctx_new.restype = ctypes.c_void_p
    
    _lib.atlas_ctx_new_default.argtypes = []
    _lib.atlas_ctx_new_default.restype = ctypes.c_void_p
    
    _lib.atlas_ctx_clone.argtypes = [ctypes.c_void_p]
    _lib.atlas_ctx_clone.restype = ctypes.c_void_p
    
    _lib.atlas_ctx_free.argtypes = [ctypes.c_void_p]
    _lib.atlas_ctx_free.restype = None
    
    # Configuration
    _lib.atlas_ctx_get_config.argtypes = [ctypes.c_void_p, ctypes.POINTER(AtlasContextConfig)]
    _lib.atlas_ctx_get_config.restype = ctypes.c_int
    
    _lib.atlas_ctx_set_config.argtypes = [ctypes.c_void_p, ctypes.POINTER(AtlasContextConfig)]
    _lib.atlas_ctx_set_config.restype = ctypes.c_int
    
    _lib.atlas_ctx_config_default.argtypes = [ctypes.POINTER(AtlasContextConfig)]
    _lib.atlas_ctx_config_default.restype = None
    
    # Lift operations
    _lib.atlas_ctx_apply_lift_x.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_lift_x.restype = ctypes.c_int
    
    _lib.atlas_ctx_apply_lift_z.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_lift_z.restype = ctypes.c_int
    
    # Pauli operations
    _lib.atlas_ctx_apply_pauli_x.argtypes = [ctypes.c_void_p, ctypes.c_uint8, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_pauli_x.restype = ctypes.c_int
    
    _lib.atlas_ctx_apply_pauli_z.argtypes = [ctypes.c_void_p, ctypes.c_uint8, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_pauli_z.restype = ctypes.c_int
    
    _lib.atlas_ctx_apply_heisenberg.argtypes = [ctypes.c_void_p, ctypes.c_uint8, ctypes.c_uint8, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_heisenberg.restype = ctypes.c_int
    
    # Twirl operations
    _lib.atlas_ctx_apply_twirl.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_twirl.restype = ctypes.c_int
    
    _lib.atlas_ctx_check_twirl_idempotency.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_check_twirl_idempotency.restype = ctypes.c_double
    
    _lib.atlas_ctx_get_twirl_generator.argtypes = [ctypes.c_void_p, ctypes.c_uint32, 
                                                     ctypes.POINTER(ctypes.c_uint8), 
                                                     ctypes.POINTER(ctypes.c_uint8)]
    _lib.atlas_ctx_get_twirl_generator.restype = ctypes.c_int
    
    # Diagnostics
    _lib.atlas_ctx_get_diagnostics.argtypes = [ctypes.c_void_p, ctypes.POINTER(AtlasContextDiagnostics)]
    _lib.atlas_ctx_get_diagnostics.restype = ctypes.c_int
    
    _lib.atlas_ctx_reset_diagnostics.argtypes = [ctypes.c_void_p]
    _lib.atlas_ctx_reset_diagnostics.restype = None
    
    _lib.atlas_ctx_validate.argtypes = [ctypes.c_void_p]
    _lib.atlas_ctx_validate.restype = ctypes.c_int
    
    _lib.atlas_ctx_print_diagnostics.argtypes = [ctypes.c_void_p]
    _lib.atlas_ctx_print_diagnostics.restype = None
    
    # Utilities
    _lib.atlas_ctx_version.argtypes = []
    _lib.atlas_ctx_version.restype = ctypes.c_char_p
    
    _lib.atlas_ctx_get_block_size.argtypes = [ctypes.c_void_p]
    _lib.atlas_ctx_get_block_size.restype = ctypes.c_uint32
    
    _lib.atlas_ctx_get_n_qubits.argtypes = [ctypes.c_void_p]
    _lib.atlas_ctx_get_n_qubits.restype = ctypes.c_uint32

# ============================================================================
# Python API
# ============================================================================

class AtlasBridgeContext:
    """
    Python wrapper for Atlas Bridge Context API v0.2.
    
    Provides context-based operations for Atlas bridge with:
    - Homomorphic lift permutations (Lx, Lz)
    - In-block Pauli/Heisenberg operations
    - E-twirl group action with idempotency
    """
    
    def __init__(self, config: Optional[AtlasContextConfig] = None):
        """
        Create new Atlas Bridge Context.
        
        Args:
            config: Configuration parameters (None for default)
        """
        _ensure_loaded()
        
        if config is None:
            self._handle = _lib.atlas_ctx_new_default()
        else:
            self._handle = _lib.atlas_ctx_new(ctypes.byref(config))
        
        if not self._handle:
            raise RuntimeError("Failed to create Atlas Bridge Context")
    
    @classmethod
    def with_default_config(cls):
        """Create context with default configuration."""
        return cls(None)
    
    def clone(self):
        """Create a deep copy of this context."""
        _ensure_loaded()
        new_handle = _lib.atlas_ctx_clone(self._handle)
        if not new_handle:
            raise RuntimeError("Failed to clone context")
        
        new_ctx = object.__new__(AtlasBridgeContext)
        new_ctx._handle = new_handle
        return new_ctx
    
    def __del__(self):
        """Free context resources."""
        if hasattr(self, '_handle') and self._handle and _lib:
            _lib.atlas_ctx_free(self._handle)
            self._handle = None
    
    def get_config(self) -> AtlasContextConfig:
        """Get current configuration."""
        _ensure_loaded()
        config = AtlasContextConfig()
        result = _lib.atlas_ctx_get_config(self._handle, ctypes.byref(config))
        if result != 0:
            raise RuntimeError("Failed to get configuration")
        return config
    
    def set_config(self, config: AtlasContextConfig) -> None:
        """Update configuration (some parameters may not be updatable)."""
        _ensure_loaded()
        result = _lib.atlas_ctx_set_config(self._handle, ctypes.byref(config))
        if result != 0:
            raise RuntimeError("Failed to set configuration")
    
    def apply_lift_x(self, state) -> None:
        """Apply homomorphic lift Lx permutation."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_lift_x(self._handle, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply lift Lx")
        # Copy back
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def apply_lift_z(self, state) -> None:
        """Apply homomorphic lift Lz permutation."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_lift_z(self._handle, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply lift Lz")
        # Copy back
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def apply_pauli_x(self, qubit_mask: int, state) -> None:
        """Apply Pauli X on qubits specified by mask."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_pauli_x(self._handle, qubit_mask, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply Pauli X")
        # Copy back
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def apply_pauli_z(self, qubit_mask: int, state) -> None:
        """Apply Pauli Z on qubits specified by mask."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_pauli_z(self._handle, qubit_mask, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply Pauli Z")
        # Copy back
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def apply_heisenberg(self, q1: int, q2: int, state) -> None:
        """Apply Heisenberg exchange on qubit pair."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_heisenberg(self._handle, q1, q2, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply Heisenberg exchange")
        # Copy back
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def apply_twirl(self, state) -> None:
        """Apply E-twirl (averaging over group generators)."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_twirl(self._handle, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply E-twirl")
        # Copy back
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def check_twirl_idempotency(self, state) -> float:
        """Check E-twirl idempotency: ||T²(v) - T(v)||₂."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_check_twirl_idempotency(self._handle, state_arr)
        if result < 0:
            raise RuntimeError("Failed to check twirl idempotency")
        return result
    
    def get_twirl_generator(self, gen_idx: int) -> Tuple[int, int]:
        """Get E-twirl generator at index (returns x_mask, z_mask)."""
        _ensure_loaded()
        x_mask = ctypes.c_uint8()
        z_mask = ctypes.c_uint8()
        result = _lib.atlas_ctx_get_twirl_generator(self._handle, gen_idx, 
                                                      ctypes.byref(x_mask), 
                                                      ctypes.byref(z_mask))
        if result != 0:
            raise RuntimeError(f"Failed to get generator {gen_idx}")
        return (x_mask.value, z_mask.value)
    
    def get_diagnostics(self) -> AtlasContextDiagnostics:
        """Get current diagnostics."""
        _ensure_loaded()
        diag = AtlasContextDiagnostics()
        result = _lib.atlas_ctx_get_diagnostics(self._handle, ctypes.byref(diag))
        if result != 0:
            raise RuntimeError("Failed to get diagnostics")
        return diag
    
    def reset_diagnostics(self) -> None:
        """Reset diagnostics counters."""
        _ensure_loaded()
        _lib.atlas_ctx_reset_diagnostics(self._handle)
    
    def validate(self) -> bool:
        """Validate internal consistency."""
        _ensure_loaded()
        return _lib.atlas_ctx_validate(self._handle) == 0
    
    def print_diagnostics(self) -> None:
        """Print diagnostics to stdout."""
        _ensure_loaded()
        _lib.atlas_ctx_print_diagnostics(self._handle)
    
    @property
    def block_size(self) -> int:
        """Get block size."""
        _ensure_loaded()
        return _lib.atlas_ctx_get_block_size(self._handle)
    
    @property
    def n_qubits(self) -> int:
        """Get number of qubits."""
        _ensure_loaded()
        return _lib.atlas_ctx_get_n_qubits(self._handle)

# Module-level functions

def get_version() -> str:
    """Get library version string."""
    _ensure_loaded()
    return _lib.atlas_ctx_version().decode('utf-8')

def get_default_config() -> AtlasContextConfig:
    """Get default configuration."""
    _ensure_loaded()
    config = AtlasContextConfig()
    _lib.atlas_ctx_config_default(ctypes.byref(config))
    return config

# Module exports
__all__ = [
    # Constants
    'ATLAS_CTX_DEFAULT',
    'ATLAS_CTX_ENABLE_TWIRL',
    'ATLAS_CTX_ENABLE_LIFT',
    'ATLAS_CTX_VERBOSE',
    # Classes
    'AtlasContextConfig',
    'AtlasContextDiagnostics',
    'AtlasBridgeContext',
    # Functions
    'get_version',
    'get_default_config',
]
