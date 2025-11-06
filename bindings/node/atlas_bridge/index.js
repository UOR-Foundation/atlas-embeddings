/**
 * Atlas Bridge Context API v0.5 - Node.js Bindings
 * 
 * v0.5 Features:
 * - BLAS-accelerated matrix-vector operations
 * - Real artifact integration (lift_forms.hex, P_299_matrix.bin, co1_gates.txt)
 * - Context-based API for safe resource management
 * 
 * ⚠️ DEPRECATION WARNING:
 * Legacy non-context API has been deprecated in v0.5 and will be removed in v0.6.
 * Please migrate all code to use the context-based API.
 * 
 * @example
 * const { AtlasContext } = require('@atlas/bridge');
 * 
 * const ctx = new AtlasContext();
 * ctx.loadLiftForms('lift_forms.hex');
 * ctx.loadP299Matrix('P_299_matrix.bin'); // optional
 * ctx.loadCo1Gates('co1_gates.txt'); // optional
 * 
 * const state = new Float64Array(ctx.blockSize);
 * ctx.applyPClass(state);
 * ctx.applyP299(state);
 * ctx.emitCertificate('bridge_cert.json', 'test');
 */

const ffi = require('ffi-napi');
const ref = require('ref-napi');
const Struct = require('ref-struct-napi');
const path = require('path');
const os = require('os');

// Type definitions
const double = ref.types.double;
const uint32 = ref.types.uint32;
const int = ref.types.int;
const voidPtr = ref.refType(ref.types.void);
const doublePtr = ref.refType(double);
const charPtr = ref.refType(ref.types.char);

// AtlasContextConfig struct
const AtlasContextConfig = Struct({
  flags: uint32,
  block_size: uint32,
  n_qubits: uint32,
  twirl_gens: uint32,
  epsilon: double,
  n_qbits: uint32
});

// Determine library path
function getLibraryPath() {
  const platform = os.platform();
  const baseDir = path.join(__dirname, '..', '..', '..', 'atlas_core', 'lib');
  
  let libName;
  if (platform === 'win32') {
    libName = 'libatlas_bridge_ctx.dll';
  } else if (platform === 'darwin') {
    libName = 'libatlas_bridge_ctx.dylib';
  } else {
    libName = 'libatlas_bridge_ctx.so';
  }
  
  return path.join(baseDir, libName);
}

// Load native library
const lib = ffi.Library(getLibraryPath(), {
  'atlas_ctx_new': [voidPtr, [ref.refType(AtlasContextConfig)]],
  'atlas_ctx_new_default': [voidPtr, []],
  'atlas_ctx_free': ['void', [voidPtr]],
  'atlas_ctx_load_lift_forms': [int, [voidPtr, charPtr]],
  'atlas_ctx_load_p299_matrix': [int, [voidPtr, charPtr]],
  'atlas_ctx_load_co1_gates': [int, [voidPtr, charPtr]],
  'atlas_ctx_apply_p_class': [int, [voidPtr, doublePtr]],
  'atlas_ctx_apply_p_299': [int, [voidPtr, doublePtr]],
  'atlas_ctx_get_block_size': [uint32, [voidPtr]],
  'atlas_ctx_get_n_qubits': [uint32, [voidPtr]],
  'atlas_ctx_emit_certificate': [int, [voidPtr, charPtr, charPtr]],
  'atlas_ctx_version': [charPtr, []]
});

/**
 * Atlas Bridge Context wrapper class
 */
class AtlasContext {
  constructor(config = null) {
    if (config) {
      const cfg = new AtlasContextConfig(config);
      this._ctx = lib.atlas_ctx_new(cfg.ref());
    } else {
      this._ctx = lib.atlas_ctx_new_default();
    }
    
    if (this._ctx.isNull()) {
      throw new Error('Failed to create Atlas context');
    }
  }

  /**
   * Load lift forms from hex file
   * @param {string} filepath - Path to lift_forms.hex
   */
  loadLiftForms(filepath) {
    const result = lib.atlas_ctx_load_lift_forms(this._ctx, filepath);
    if (result !== 0) {
      throw new Error(`Failed to load lift forms from ${filepath}`);
    }
  }

  /**
   * Load P_299 matrix from binary file (optional)
   * @param {string} filepath - Path to P_299_matrix.bin
   */
  loadP299Matrix(filepath) {
    const result = lib.atlas_ctx_load_p299_matrix(this._ctx, filepath);
    if (result !== 0) {
      console.warn(`Failed to load P_299 matrix from ${filepath}, using fallback`);
    }
  }

  /**
   * Load Co1 gates from text file (optional)
   * @param {string} filepath - Path to co1_gates.txt
   */
  loadCo1Gates(filepath) {
    const result = lib.atlas_ctx_load_co1_gates(this._ctx, filepath);
    if (result !== 0) {
      throw new Error(`Failed to load Co1 gates from ${filepath}`);
    }
  }

  /**
   * Apply P_class projector to state vector
   * @param {Float64Array} state - State vector (length must be blockSize)
   */
  applyPClass(state) {
    if (!(state instanceof Float64Array)) {
      throw new TypeError('State must be a Float64Array');
    }
    if (state.length !== this.blockSize) {
      throw new Error(`State length ${state.length} does not match block size ${this.blockSize}`);
    }
    
    const result = lib.atlas_ctx_apply_p_class(this._ctx, state);
    if (result !== 0) {
      throw new Error('Failed to apply P_class');
    }
  }

  /**
   * Apply P_299 projector to state vector
   * @param {Float64Array} state - State vector (length must be blockSize)
   */
  applyP299(state) {
    if (!(state instanceof Float64Array)) {
      throw new TypeError('State must be a Float64Array');
    }
    if (state.length !== this.blockSize) {
      throw new Error(`State length ${state.length} does not match block size ${this.blockSize}`);
    }
    
    const result = lib.atlas_ctx_apply_p_299(this._ctx, state);
    if (result !== 0) {
      throw new Error('Failed to apply P_299');
    }
  }

  /**
   * Emit JSON certificate to file
   * @param {string} filepath - Path to output JSON file
   * @param {string} mode - Mode string (e.g., 'test', 'verify')
   */
  emitCertificate(filepath, mode) {
    const result = lib.atlas_ctx_emit_certificate(this._ctx, filepath, mode);
    if (result !== 0) {
      throw new Error(`Failed to emit certificate to ${filepath}`);
    }
  }

  /**
   * Get block size for this context
   * @returns {number}
   */
  get blockSize() {
    return lib.atlas_ctx_get_block_size(this._ctx);
  }

  /**
   * Get number of qubits for this context
   * @returns {number}
   */
  get nQubits() {
    return lib.atlas_ctx_get_n_qubits(this._ctx);
  }

  /**
   * Get library version
   * @returns {string}
   */
  static get version() {
    return lib.atlas_ctx_version().readCString();
  }

  /**
   * Free context resources
   */
  free() {
    if (!this._ctx.isNull()) {
      lib.atlas_ctx_free(this._ctx);
      this._ctx = ref.NULL;
    }
  }

  /**
   * Destructor - automatically called by garbage collector
   */
  [Symbol.dispose]() {
    this.free();
  }
}

module.exports = {
  AtlasContext,
  version: AtlasContext.version
};
