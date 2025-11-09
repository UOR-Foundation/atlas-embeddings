/// Shared types used by kernels
/// Marker trait for types that are POD (Plain Old Data)
///
/// This allows safe byte manipulation and FFI transfer
///
/// # Safety
///
/// Types implementing this trait must:
/// - Have no padding bytes
/// - Be valid for any bit pattern
/// - Be safe to transmit as raw bytes across FFI boundaries
/// - Have a stable memory layout (repr(C) or primitive types)
pub unsafe trait Pod {}

// Implement Pod for all basic types
unsafe impl Pod for u8 {}
unsafe impl Pod for u16 {}
unsafe impl Pod for u32 {}
unsafe impl Pod for u64 {}
unsafe impl Pod for i8 {}
unsafe impl Pod for i16 {}
unsafe impl Pod for i32 {}
unsafe impl Pod for i64 {}
unsafe impl Pod for f32 {}
unsafe impl Pod for f64 {}
