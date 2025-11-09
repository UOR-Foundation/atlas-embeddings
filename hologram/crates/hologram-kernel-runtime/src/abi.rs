/// Standard ABI for all kernels
use std::os::raw::c_char;

/// Launch configuration for kernel execution
#[repr(C)]
pub struct CLaunchConfig {
    pub grid_dim_x: u32,
    pub grid_dim_y: u32,
    pub grid_dim_z: u32,
    pub block_dim_x: u32,
    pub block_dim_y: u32,
    pub block_dim_z: u32,
}

/// Standard error codes for kernel execution
#[repr(C)]
pub enum ErrorCode {
    Success = 0,
    InvalidParams = 1,
    ExecutionFailed = 2,
}

/// Current ABI version
pub const ABI_VERSION: u32 = 1;

/// Standard kernel execute signature
///
/// All kernels must export a function matching this signature.
pub type KernelExecuteFn = unsafe extern "C" fn(
    config: *const CLaunchConfig,
    params: *const u8,
    params_len: usize,
    error_msg: *mut *mut c_char,
) -> u32;

/// Standard kernel name getter signature
pub type KernelNameFn = unsafe extern "C" fn() -> *const c_char;

/// Standard ABI version getter signature
pub type KernelAbiVersionFn = unsafe extern "C" fn() -> u32;
