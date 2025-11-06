//! FFI declarations for Atlas Bridge Context API v0.5

#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

use std::os::raw::{c_char, c_double, c_int, c_uint};

/// Opaque context handle
#[repr(C)]
pub struct AtlasBridgeContext {
    _private: [u8; 0],
}

/// Context configuration
#[repr(C)]
pub struct AtlasContextConfig {
    pub flags: c_uint,
    pub block_size: c_uint,
    pub n_qubits: c_uint,
    pub twirl_gens: c_uint,
    pub epsilon: c_double,
    pub n_qbits: c_uint,
}

extern "C" {
    pub fn atlas_ctx_new(config: *const AtlasContextConfig) -> *mut AtlasBridgeContext;
    pub fn atlas_ctx_new_default() -> *mut AtlasBridgeContext;
    pub fn atlas_ctx_free(ctx: *mut AtlasBridgeContext);

    pub fn atlas_ctx_load_lift_forms(ctx: *mut AtlasBridgeContext, filepath: *const c_char)
        -> c_int;
    pub fn atlas_ctx_load_p299_matrix(ctx: *mut AtlasBridgeContext, filepath: *const c_char)
        -> c_int;
    pub fn atlas_ctx_load_co1_gates(ctx: *mut AtlasBridgeContext, filepath: *const c_char)
        -> c_int;

    pub fn atlas_ctx_apply_p_class(ctx: *mut AtlasBridgeContext, state: *mut c_double) -> c_int;
    pub fn atlas_ctx_apply_p_299(ctx: *mut AtlasBridgeContext, state: *mut c_double) -> c_int;

    pub fn atlas_ctx_get_block_size(ctx: *const AtlasBridgeContext) -> c_uint;
    pub fn atlas_ctx_get_n_qubits(ctx: *const AtlasBridgeContext) -> c_uint;

    pub fn atlas_ctx_emit_certificate(
        ctx: *const AtlasBridgeContext,
        filepath: *const c_char,
        mode: *const c_char,
    ) -> c_int;

    pub fn atlas_ctx_version() -> *const c_char;
}
