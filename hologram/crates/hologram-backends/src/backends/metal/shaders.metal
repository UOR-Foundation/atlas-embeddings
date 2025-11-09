//! Metal Shading Language (MSL) Compute Kernels for Atlas ISA Operations
//!
//! This file contains GPU kernels for common Atlas ISA operations.
//! Each kernel is optimized for Apple Silicon's unified memory architecture.
//!
//! ## Architecture
//!
//! - Thread groups: 256 threads per group (optimal for Apple Silicon)
//! - Memory: Unified memory with zero-copy access
//! - Precision: Native float32 and int32 support
//!
//! ## Kernel Naming Convention
//!
//! - `atlas_` prefix for all kernels
//! - Operation name: `add`, `mul`, `sub`, etc.
//! - Type suffix: `_f32`, `_i32`, etc.

#include <metal_stdlib>
using namespace metal;

// ============================================================================
// Binary Element-wise Operations (Float32)
// ============================================================================

/// Vector addition: c[i] = a[i] + b[i] (f32)
kernel void atlas_add_f32(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = a[gid] + b[gid];
    }
}

/// Vector subtraction: c[i] = a[i] - b[i] (f32)
kernel void atlas_sub_f32(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = a[gid] - b[gid];
    }
}

/// Vector multiplication: c[i] = a[i] * b[i] (f32)
kernel void atlas_mul_f32(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = a[gid] * b[gid];
    }
}

/// Vector division: c[i] = a[i] / b[i] (f32)
kernel void atlas_div_f32(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = a[gid] / b[gid];
    }
}

/// Vector minimum: c[i] = min(a[i], b[i]) (f32)
kernel void atlas_min_f32(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = min(a[gid], b[gid]);
    }
}

/// Vector maximum: c[i] = max(a[i], b[i]) (f32)
kernel void atlas_max_f32(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device float* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = max(a[gid], b[gid]);
    }
}

// ============================================================================
// Unary Element-wise Operations (Float32)
// ============================================================================

/// Vector absolute value: b[i] = abs(a[i]) (f32)
kernel void atlas_abs_f32(
    device const float* a [[buffer(0)]],
    device float* b [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        b[gid] = abs(a[gid]);
    }
}

/// Vector negation: b[i] = -a[i] (f32)
kernel void atlas_neg_f32(
    device const float* a [[buffer(0)]],
    device float* b [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        b[gid] = -a[gid];
    }
}

/// ReLU activation: b[i] = max(0, a[i]) (f32)
kernel void atlas_relu_f32(
    device const float* a [[buffer(0)]],
    device float* b [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        b[gid] = max(0.0f, a[gid]);
    }
}

/// Square root: b[i] = sqrt(a[i]) (f32)
kernel void atlas_sqrt_f32(
    device const float* a [[buffer(0)]],
    device float* b [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        b[gid] = sqrt(a[gid]);
    }
}

// ============================================================================
// Activation Functions (Float32)
// ============================================================================

/// Sigmoid activation: b[i] = 1 / (1 + exp(-a[i])) (f32)
kernel void atlas_sigmoid_f32(
    device const float* a [[buffer(0)]],
    device float* b [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        b[gid] = 1.0f / (1.0f + exp(-a[gid]));
    }
}

/// Tanh activation: b[i] = tanh(a[i]) (f32)
kernel void atlas_tanh_f32(
    device const float* a [[buffer(0)]],
    device float* b [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        b[gid] = tanh(a[gid]);
    }
}

/// Exponential: b[i] = exp(a[i]) (f32)
kernel void atlas_exp_f32(
    device const float* a [[buffer(0)]],
    device float* b [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        b[gid] = exp(a[gid]);
    }
}

/// Natural logarithm: b[i] = log(a[i]) (f32)
kernel void atlas_log_f32(
    device const float* a [[buffer(0)]],
    device float* b [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        b[gid] = log(a[gid]);
    }
}

// ============================================================================
// Fused Operations (Float32)
// ============================================================================

/// Fused multiply-add: d[i] = a[i] * b[i] + c[i] (f32)
kernel void atlas_mad_f32(
    device const float* a [[buffer(0)]],
    device const float* b [[buffer(1)]],
    device const float* c [[buffer(2)]],
    device float* d [[buffer(3)]],
    constant uint& n [[buffer(4)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        d[gid] = fma(a[gid], b[gid], c[gid]);  // Use hardware FMA if available
    }
}

// ============================================================================
// Binary Element-wise Operations (Int32)
// ============================================================================

/// Vector addition: c[i] = a[i] + b[i] (i32)
kernel void atlas_add_i32(
    device const int* a [[buffer(0)]],
    device const int* b [[buffer(1)]],
    device int* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = a[gid] + b[gid];
    }
}

/// Vector subtraction: c[i] = a[i] - b[i] (i32)
kernel void atlas_sub_i32(
    device const int* a [[buffer(0)]],
    device const int* b [[buffer(1)]],
    device int* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = a[gid] - b[gid];
    }
}

/// Vector multiplication: c[i] = a[i] * b[i] (i32)
kernel void atlas_mul_i32(
    device const int* a [[buffer(0)]],
    device const int* b [[buffer(1)]],
    device int* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = a[gid] * b[gid];
    }
}

/// Vector division: c[i] = a[i] / b[i] (i32)
kernel void atlas_div_i32(
    device const int* a [[buffer(0)]],
    device const int* b [[buffer(1)]],
    device int* c [[buffer(2)]],
    constant uint& n [[buffer(3)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        c[gid] = a[gid] / b[gid];
    }
}

// ============================================================================
// Memory Copy Operations
// ============================================================================

/// Memory copy: dst[i] = src[i] (generic byte copy)
kernel void atlas_memcpy(
    device const uchar* src [[buffer(0)]],
    device uchar* dst [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        dst[gid] = src[gid];
    }
}

/// Memory fill: dst[i] = value (f32)
kernel void atlas_fill_f32(
    device float* dst [[buffer(0)]],
    constant float& value [[buffer(1)]],
    constant uint& n [[buffer(2)]],
    uint gid [[thread_position_in_grid]]
) {
    if (gid < n) {
        dst[gid] = value;
    }
}
