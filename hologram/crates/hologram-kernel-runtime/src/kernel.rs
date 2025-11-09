/// Kernel execution helpers
///
/// These functions are re-exported by each kernel to provide the standard C ABI
/// These types are used in the macros but not directly imported in this module
/// Generate ABI version getter
#[macro_export]
macro_rules! define_kernel_abi_version {
    () => {
        #[no_mangle]
        pub unsafe extern "C" fn atlas_kernel_abi_version() -> u32 {
            hologram_kernel_runtime::ABI_VERSION
        }
    };
}

/// Generate kernel name getter
#[macro_export]
macro_rules! define_kernel_name {
    ($name:literal) => {
        #[no_mangle]
        pub unsafe extern "C" fn atlas_kernel_name() -> *const ::std::os::raw::c_char {
            ::std::ffi::CString::new($name).unwrap().as_ptr()
        }
    };
}

/// Generate kernel execute function that calls kernel_execute_internal
///
/// This macro generates the standard C ABI entry point that unpacks parameters
/// and calls the kernel-specific internal function.
#[macro_export]
macro_rules! define_kernel_execute {
    () => {
        #[no_mangle]
        pub unsafe extern "C" fn atlas_kernel_execute(
            _config: *const hologram_kernel_runtime::CLaunchConfig,
            params: *const u8,
            params_len: usize,
            _error_msg: *mut *mut ::std::os::raw::c_char,
        ) -> hologram_kernel_runtime::ErrorCode {
            if params.is_null() {
                return hologram_kernel_runtime::ErrorCode::InvalidParams;
            }

            let params_slice = ::std::slice::from_raw_parts(params, params_len);
            kernel_execute_internal(params_slice)
        }
    };
}
