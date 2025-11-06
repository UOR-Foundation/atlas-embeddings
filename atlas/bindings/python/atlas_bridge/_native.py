"""
bindings/python/atlas_bridge/_native.py
Conway–Monster Atlas Upgrade Kit v1.1
Python bindings for native C atlas_bridge library

⚠️  DEPRECATION WARNING (v0.5):
This module provides legacy non-context-based API which is DEPRECATED.
Please migrate to the new context-based API in _native_ctx.py

Legacy API will be removed in v0.6. Use atlas_bridge._native_ctx instead.
For migration guide, see: atlas_core/README_CONTEXT_API.md

Example migration:
  OLD: from atlas_bridge._native import lib
       lib.e_apply(state, x_mask, z_mask)
  
  NEW: from atlas_bridge._native_ctx import AtlasCtx
       ctx = AtlasCtx()
       ctx.apply_pauli_x(x_mask, state)
       ctx.apply_pauli_z(z_mask, state)
"""

import ctypes
import os
import platform
import warnings
from typing import Optional, Tuple

# Issue deprecation warning on module import
warnings.warn(
    "atlas_bridge._native is deprecated and will be removed in v0.6. "
    "Please migrate to atlas_bridge._native_ctx (context-based API). "
    "See atlas_core/README_CONTEXT_API.md for migration guide.",
    DeprecationWarning,
    stacklevel=2
)

# Determine library name based on platform
def _get_library_name():
    system = platform.system()
    if system == "Windows":
        return "atlas_bridge.dll"
    elif system == "Darwin":
        return "libatlas_bridge.dylib"
    else:
        return "libatlas_bridge.so"

# Find and load the library
def _load_library():
    """Load the native atlas_bridge library."""
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

# Constants
ATLAS_MODE_CLASS = 0
ATLAS_MODE_BRIDGE = 1

# Function signatures

# int atlas_dims(uint32_t* base, uint32_t* bridge)
_atlas_dims = None
if _lib:
    _atlas_dims = _lib.atlas_dims
    _atlas_dims.argtypes = [ctypes.POINTER(ctypes.c_uint32), ctypes.POINTER(ctypes.c_uint32)]
    _atlas_dims.restype = ctypes.c_int

# void atlas_set_mode(int mode)
_atlas_set_mode = None
if _lib:
    _atlas_set_mode = _lib.atlas_set_mode
    _atlas_set_mode.argtypes = [ctypes.c_int]
    _atlas_set_mode.restype = None

# void atlas_spinlift_enable(int on)
_atlas_spinlift_enable = None
if _lib:
    _atlas_spinlift_enable = _lib.atlas_spinlift_enable
    _atlas_spinlift_enable.argtypes = [ctypes.c_int]
    _atlas_spinlift_enable.restype = None

# uint32_t phi_encode(uint8_t page, uint8_t byte)
_phi_encode = None
if _lib:
    _phi_encode = _lib.phi_encode
    _phi_encode.argtypes = [ctypes.c_uint8, ctypes.c_uint8]
    _phi_encode.restype = ctypes.c_uint32

# int phi_decode(uint32_t idx, uint8_t* page, uint8_t* byte)
_phi_decode = None
if _lib:
    _phi_decode = _lib.phi_decode
    _phi_decode.argtypes = [ctypes.c_uint32, ctypes.POINTER(ctypes.c_uint8), ctypes.POINTER(ctypes.c_uint8)]
    _phi_decode.restype = ctypes.c_int

# void E_apply(const uint64_t* x_mask, const uint64_t* z_mask, int n_qubits)
_E_apply = None
if _lib:
    _E_apply = _lib.E_apply
    _E_apply.argtypes = [ctypes.POINTER(ctypes.c_uint64), ctypes.POINTER(ctypes.c_uint64), ctypes.c_int]
    _E_apply.restype = None

# void Co1_apply(uint32_t gate_id, const double* params, int n_params)
_Co1_apply = None
if _lib:
    _Co1_apply = _lib.Co1_apply
    _Co1_apply.argtypes = [ctypes.c_uint32, ctypes.POINTER(ctypes.c_double), ctypes.c_int]
    _Co1_apply.restype = None

# double projector_residual(const char* pname)
_projector_residual = None
if _lib:
    _projector_residual = _lib.projector_residual
    _projector_residual.argtypes = [ctypes.c_char_p]
    _projector_residual.restype = ctypes.c_double

# double commutant_probe(int with_Co1)
_commutant_probe = None
if _lib:
    _commutant_probe = _lib.commutant_probe
    _commutant_probe.argtypes = [ctypes.c_int]
    _commutant_probe.restype = ctypes.c_double

# int leakage_certificate(const char* json_out_path)
_leakage_certificate = None
if _lib:
    _leakage_certificate = _lib.leakage_certificate
    _leakage_certificate.argtypes = [ctypes.c_char_p]
    _leakage_certificate.restype = ctypes.c_int

# Python API

def get_dimensions() -> Tuple[int, int]:
    """Get base and bridge dimensions.
    
    Returns:
        Tuple of (base_dim, bridge_dim) where base_dim=12288 and bridge_dim=98304
    """
    _ensure_loaded()
    base = ctypes.c_uint32()
    bridge = ctypes.c_uint32()
    _atlas_dims(ctypes.byref(base), ctypes.byref(bridge))
    return (base.value, bridge.value)

def set_mode(mode: int) -> None:
    """Set Atlas mode.
    
    Args:
        mode: Either ATLAS_MODE_CLASS (0) or ATLAS_MODE_BRIDGE (1)
    """
    _ensure_loaded()
    _atlas_set_mode(mode)

def enable_spinlift(enabled: bool) -> None:
    """Enable or disable spinlift (only effective in BRIDGE mode).
    
    Args:
        enabled: True to enable, False to disable
    """
    _ensure_loaded()
    _atlas_spinlift_enable(1 if enabled else 0)

def phi_encode(page: int, byte: int) -> int:
    """Encode (page, byte) pair to linear index.
    
    Args:
        page: Page number (0-47)
        byte: Byte value (0-255)
        
    Returns:
        Linear index (0-12287)
    """
    _ensure_loaded()
    return _phi_encode(page, byte)

def phi_decode(idx: int) -> Tuple[int, int]:
    """Decode linear index to (page, byte) pair.
    
    Args:
        idx: Linear index (0-12287)
        
    Returns:
        Tuple of (page, byte)
        
    Raises:
        ValueError: If index is out of range
    """
    _ensure_loaded()
    page = ctypes.c_uint8()
    byte = ctypes.c_uint8()
    result = _phi_decode(idx, ctypes.byref(page), ctypes.byref(byte))
    if result != 0:
        raise ValueError(f"Invalid index: {idx}")
    return (page.value, byte.value)

def apply_E_group(x_mask: int, z_mask: int, n_qubits: int = 12) -> None:
    """Apply E group action.
    
    Args:
        x_mask: X-type operator mask (24 bits)
        z_mask: Z-type operator mask (24 bits)
        n_qubits: Number of qubits (default 12)
    """
    _ensure_loaded()
    x = ctypes.c_uint64(x_mask)
    z = ctypes.c_uint64(z_mask)
    _E_apply(ctypes.byref(x), ctypes.byref(z), n_qubits)

def apply_Co1_gate(gate_id: int, params: Optional[list] = None) -> None:
    """Apply Co1 gate.
    
    Args:
        gate_id: Gate identifier
        params: Optional list of parameters (floats)
    """
    _ensure_loaded()
    if params:
        param_array = (ctypes.c_double * len(params))(*params)
        _Co1_apply(gate_id, param_array, len(params))
    else:
        _Co1_apply(gate_id, None, 0)

def get_projector_residual(name: str) -> float:
    """Get projector residual ||P^2 - P||_2.
    
    Args:
        name: Projector name ("class", "qonly", or "299")
        
    Returns:
        Residual value (should be near 0 for valid projector)
    """
    _ensure_loaded()
    return _projector_residual(name.encode('utf-8'))

def probe_commutant(with_co1: bool = False) -> float:
    """Probe commutant dimension.
    
    Args:
        with_co1: Include Co1 constraints if True
        
    Returns:
        Estimated commutant dimension
    """
    _ensure_loaded()
    return _commutant_probe(1 if with_co1 else 0)

def generate_leakage_certificate(output_path: str) -> None:
    """Generate leakage certificate JSON.
    
    Args:
        output_path: Path to write JSON certificate
        
    Raises:
        RuntimeError: If certificate generation fails
    """
    _ensure_loaded()
    result = _leakage_certificate(output_path.encode('utf-8'))
    if result != 0:
        raise RuntimeError(f"Failed to generate certificate at {output_path}")

# Module-level convenience
__all__ = [
    'ATLAS_MODE_CLASS',
    'ATLAS_MODE_BRIDGE',
    'get_dimensions',
    'set_mode',
    'enable_spinlift',
    'phi_encode',
    'phi_decode',
    'apply_E_group',
    'apply_Co1_gate',
    'get_projector_residual',
    'probe_commutant',
    'generate_leakage_certificate',
]
