"""
bindings/python/atlas_bridge/_native_ctx.py
Atlas Bridge Context API v0.5
Python bindings for the Context API from native C library

v0.5 Updates:
- BLAS-accelerated matrix-vector operations (when available)
- Enhanced artifact loading (lift_forms.hex, P_299_matrix.bin, co1_gates.txt)
- Improved performance with optional BLAS backend
- Full backward compatibility with v0.4
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
ATLAS_CTX_ENABLE_P_CLASS = 0x08
ATLAS_CTX_ENABLE_P_299 = 0x10
ATLAS_CTX_ENABLE_CO1 = 0x20
ATLAS_CTX_USE_AVX2 = 0x40  # v0.4: Enable AVX2 SIMD acceleration
ATLAS_CTX_LIFT_8BIT = 0x80  # v0.4: Use only low 8 bits in lift forms

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
        ("n_qbits", ctypes.c_uint32),  # v0.4
    ]

class AtlasContextDiagnostics(ctypes.Structure):
    """Diagnostics structure for Atlas Bridge Context."""
    _fields_ = [
        ("twirl_idempotency", ctypes.c_double),
        ("lift_mass", ctypes.c_double),
        ("op_count", ctypes.c_uint64),
        ("last_residual", ctypes.c_double),
        ("p_class_idempotency", ctypes.c_double),  # v0.3
        ("p_299_idempotency", ctypes.c_double),    # v0.3
        ("commutant_dim", ctypes.c_double),        # v0.3
        ("avx2_available", ctypes.c_int),          # v0.4
        ("p_299_exact_loaded", ctypes.c_int),      # v0.4
        ("co1_gates_loaded", ctypes.c_int),        # v0.4
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
    
    # v0.3: Lift forms loader
    _lib.atlas_ctx_load_lift_forms.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
    _lib.atlas_ctx_load_lift_forms.restype = ctypes.c_int
    
    _lib.atlas_ctx_set_lift_forms_hex.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_size_t]
    _lib.atlas_ctx_set_lift_forms_hex.restype = ctypes.c_int
    
    _lib.atlas_ctx_get_lift_forms_hex.argtypes = [ctypes.c_void_p]
    _lib.atlas_ctx_get_lift_forms_hex.restype = ctypes.c_void_p  # char*, needs free
    
    # v0.3: Exact projectors
    _lib.atlas_ctx_apply_p_class.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_p_class.restype = ctypes.c_int
    
    _lib.atlas_ctx_apply_p_299.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_p_299.restype = ctypes.c_int
    
    _lib.atlas_ctx_check_p_class_idempotency.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_check_p_class_idempotency.restype = ctypes.c_double
    
    _lib.atlas_ctx_check_p_299_idempotency.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_check_p_299_idempotency.restype = ctypes.c_double
    
    # v0.3: Co1 mini-gates
    _lib.atlas_ctx_apply_page_rotation.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_page_rotation.restype = ctypes.c_int
    
    _lib.atlas_ctx_apply_mix_lifts.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_mix_lifts.restype = ctypes.c_int
    
    _lib.atlas_ctx_apply_page_parity_phase.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_page_parity_phase.restype = ctypes.c_int
    
    # v0.3: JSON certificates
    _lib.atlas_ctx_emit_certificate.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_char_p]
    _lib.atlas_ctx_emit_certificate.restype = ctypes.c_int
    
    _lib.atlas_ctx_probe_commutant.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_double), ctypes.c_int]
    _lib.atlas_ctx_probe_commutant.restype = ctypes.c_double
    
    # v0.4: Binary loaders
    _lib.atlas_ctx_load_p299_matrix.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
    _lib.atlas_ctx_load_p299_matrix.restype = ctypes.c_int
    
    _lib.atlas_ctx_load_co1_gates.argtypes = [ctypes.c_void_p, ctypes.c_char_p]
    _lib.atlas_ctx_load_co1_gates.restype = ctypes.c_int
    
    # v0.4: Block-sparse mixing
    _lib.atlas_ctx_apply_block_mixing.argtypes = [ctypes.c_void_p, ctypes.c_uint32, 
                                                     ctypes.POINTER(ctypes.c_double), 
                                                     ctypes.POINTER(ctypes.c_double)]
    _lib.atlas_ctx_apply_block_mixing.restype = ctypes.c_int
    
    # v0.4: AVX2 check
    _lib.atlas_ctx_is_avx2_active.argtypes = [ctypes.c_void_p]
    _lib.atlas_ctx_is_avx2_active.restype = ctypes.c_int

# ============================================================================
# Python API
# ============================================================================

class AtlasBridgeContext:
    """
    Python wrapper for Atlas Bridge Context API v0.4.
    
    Provides context-based operations for Atlas bridge with:
    - Homomorphic lift permutations (Lx, Lz) with runtime swap and 8-bit mode
    - In-block Pauli/Heisenberg operations with optional AVX2 acceleration
    - E-twirl group action with idempotency
    - Exact P_class and P_299 projectors (with binary matrix loader)
    - Co1 mini-gates (page rotation, Walsh-Hadamard mix, parity phase)
    - Block-sparse lift mixing helpers
    - JSON certificate emission
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
    
    # v0.3+ methods
    
    def load_lift_forms(self, filepath: str) -> None:
        """Load lift forms from hex file."""
        _ensure_loaded()
        result = _lib.atlas_ctx_load_lift_forms(self._handle, filepath.encode('utf-8'))
        if result != 0:
            raise RuntimeError(f"Failed to load lift forms from {filepath}")
    
    def set_lift_forms_hex(self, hex_data: str) -> None:
        """Set lift forms from hex string."""
        _ensure_loaded()
        hex_bytes = hex_data.encode('utf-8')
        result = _lib.atlas_ctx_set_lift_forms_hex(self._handle, hex_bytes, len(hex_bytes))
        if result != 0:
            raise RuntimeError("Failed to set lift forms from hex data")
    
    def get_lift_forms_hex(self) -> str:
        """
        Get current lift forms as hex string.
        
        WARNING: This method has a minor memory leak due to C memory allocation.
        Prefer using load_lift_forms() or set_lift_forms_hex() for setting.
        Only use this for debugging or infrequent reads.
        """
        _ensure_loaded()
        ptr = _lib.atlas_ctx_get_lift_forms_hex(self._handle)
        if not ptr:
            return ""
        result = ctypes.cast(ptr, ctypes.c_char_p).value.decode('utf-8')
        # TODO: Implement proper cleanup mechanism for C-allocated strings
        # Current implementation has a small memory leak - C string is not freed
        # This is acceptable for infrequent debugging use, but should be fixed
        # for production code that calls this method frequently
        return result
    
    def apply_p_class(self, state) -> None:
        """Apply P_class exact projector."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_p_class(self._handle, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply P_class")
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def apply_p_299(self, state) -> None:
        """Apply P_299 projector (exact matrix or reduced-rank fallback)."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_p_299(self._handle, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply P_299")
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def check_p_class_idempotency(self, state) -> float:
        """Check P_class idempotency: ||P²(v) - P(v)||₂."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_check_p_class_idempotency(self._handle, state_arr)
        if result < 0:
            raise RuntimeError("Failed to check P_class idempotency")
        return result
    
    def check_p_299_idempotency(self, state) -> float:
        """Check P_299 idempotency: ||P²(v) - P(v)||₂."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_check_p_299_idempotency(self._handle, state_arr)
        if result < 0:
            raise RuntimeError("Failed to check P_299 idempotency")
        return result
    
    def apply_page_rotation(self, rot: int, state) -> None:
        """Apply Co1 page rotation gate."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_page_rotation(self._handle, rot, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply page rotation")
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def apply_mix_lifts(self, state) -> None:
        """Apply Walsh-Hadamard mix on lifts."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_mix_lifts(self._handle, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply mix lifts")
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def apply_page_parity_phase(self, state) -> None:
        """Apply page parity phase gate."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_apply_page_parity_phase(self._handle, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply page parity phase")
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def emit_certificate(self, filepath: str, mode: str = "default") -> None:
        """Emit JSON certificate with diagnostics."""
        _ensure_loaded()
        result = _lib.atlas_ctx_emit_certificate(self._handle, 
                                                   filepath.encode('utf-8'), 
                                                   mode.encode('utf-8'))
        if result != 0:
            raise RuntimeError(f"Failed to emit certificate to {filepath}")
    
    def probe_commutant(self, state, with_co1: bool = False) -> float:
        """Compute commutant probe: effective dimension of Comm(E,Co1)."""
        _ensure_loaded()
        state_arr = (ctypes.c_double * len(state))(*state)
        result = _lib.atlas_ctx_probe_commutant(self._handle, state_arr, 1 if with_co1 else 0)
        if result < 0:
            raise RuntimeError("Failed to probe commutant")
        return result
    
    # v0.4 methods
    
    def load_p299_matrix(self, filepath: str) -> None:
        """Load exact P_299 matrix from binary file (v0.4)."""
        _ensure_loaded()
        result = _lib.atlas_ctx_load_p299_matrix(self._handle, filepath.encode('utf-8'))
        if result != 0:
            raise RuntimeError(f"Failed to load P_299 matrix from {filepath}")
    
    def load_co1_gates(self, filepath: str) -> None:
        """Load Co1 real generators from text file (v0.4)."""
        _ensure_loaded()
        result = _lib.atlas_ctx_load_co1_gates(self._handle, filepath.encode('utf-8'))
        if result != 0:
            raise RuntimeError(f"Failed to load Co1 gates from {filepath}")
    
    def apply_block_mixing(self, block_idx: int, mixing_matrix, state) -> None:
        """Apply 8x8 block-sparse mixing matrix (v0.4)."""
        _ensure_loaded()
        if len(mixing_matrix) != 64:
            raise ValueError("Mixing matrix must be 8x8 (64 elements)")
        state_arr = (ctypes.c_double * len(state))(*state)
        matrix_arr = (ctypes.c_double * 64)(*mixing_matrix)
        result = _lib.atlas_ctx_apply_block_mixing(self._handle, block_idx, matrix_arr, state_arr)
        if result != 0:
            raise RuntimeError("Failed to apply block mixing")
        for i in range(len(state)):
            state[i] = state_arr[i]
    
    def is_avx2_active(self) -> bool:
        """Check if AVX2 acceleration is active (v0.4)."""
        _ensure_loaded()
        return _lib.atlas_ctx_is_avx2_active(self._handle) != 0

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
    'ATLAS_CTX_ENABLE_P_CLASS',  # v0.3
    'ATLAS_CTX_ENABLE_P_299',    # v0.3
    'ATLAS_CTX_ENABLE_CO1',      # v0.3
    'ATLAS_CTX_USE_AVX2',        # v0.4
    'ATLAS_CTX_LIFT_8BIT',       # v0.4
    # Classes
    'AtlasContextConfig',
    'AtlasContextDiagnostics',
    'AtlasBridgeContext',
    # Functions
    'get_version',
    'get_default_config',
]
