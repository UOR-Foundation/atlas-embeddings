/**
 * CUDA Compute Kernels for Atlas ISA Operations
 *
 * This file contains GPU kernels for common Atlas ISA operations.
 * Each kernel is optimized for NVIDIA GPU architectures.
 *
 * Architecture:
 * - Thread blocks: 256 threads per block (optimal for modern NVIDIA GPUs)
 * - Memory: Unified memory or explicit transfers
 * - Precision: Native float32 and int32 support
 *
 * Kernel Naming Convention:
 * - `atlas_` prefix for all kernels
 * - Operation name: `add`, `mul`, `sub`, etc.
 * - Type suffix: `_f32`, `_i32`, etc.
 */

extern "C" {

// ============================================================================
// Binary Element-wise Operations (Float32)
// ============================================================================

/**
 * Vector addition: c[i] = a[i] + b[i] (f32)
 */
__global__ void atlas_add_f32(const float* a, const float* b, float* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = a[gid] + b[gid];
    }
}

/**
 * Vector subtraction: c[i] = a[i] - b[i] (f32)
 */
__global__ void atlas_sub_f32(const float* a, const float* b, float* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = a[gid] - b[gid];
    }
}

/**
 * Vector multiplication: c[i] = a[i] * b[i] (f32)
 */
__global__ void atlas_mul_f32(const float* a, const float* b, float* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = a[gid] * b[gid];
    }
}

/**
 * Vector division: c[i] = a[i] / b[i] (f32)
 */
__global__ void atlas_div_f32(const float* a, const float* b, float* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = a[gid] / b[gid];
    }
}

/**
 * Vector minimum: c[i] = min(a[i], b[i]) (f32)
 */
__global__ void atlas_min_f32(const float* a, const float* b, float* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = fminf(a[gid], b[gid]);
    }
}

/**
 * Vector maximum: c[i] = max(a[i], b[i]) (f32)
 */
__global__ void atlas_max_f32(const float* a, const float* b, float* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = fmaxf(a[gid], b[gid]);
    }
}

// ============================================================================
// Unary Element-wise Operations (Float32)
// ============================================================================

/**
 * Vector absolute value: b[i] = abs(a[i]) (f32)
 */
__global__ void atlas_abs_f32(const float* a, float* b, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        b[gid] = fabsf(a[gid]);
    }
}

/**
 * Vector negation: b[i] = -a[i] (f32)
 */
__global__ void atlas_neg_f32(const float* a, float* b, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        b[gid] = -a[gid];
    }
}

/**
 * ReLU activation: b[i] = max(0, a[i]) (f32)
 */
__global__ void atlas_relu_f32(const float* a, float* b, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        b[gid] = fmaxf(0.0f, a[gid]);
    }
}

/**
 * Square root: b[i] = sqrt(a[i]) (f32)
 */
__global__ void atlas_sqrt_f32(const float* a, float* b, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        b[gid] = sqrtf(a[gid]);
    }
}

// ============================================================================
// Activation Functions (Float32)
// ============================================================================

/**
 * Sigmoid activation: b[i] = 1 / (1 + exp(-a[i])) (f32)
 */
__global__ void atlas_sigmoid_f32(const float* a, float* b, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        b[gid] = 1.0f / (1.0f + expf(-a[gid]));
    }
}

/**
 * Tanh activation: b[i] = tanh(a[i]) (f32)
 */
__global__ void atlas_tanh_f32(const float* a, float* b, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        b[gid] = tanhf(a[gid]);
    }
}

/**
 * Exponential: b[i] = exp(a[i]) (f32)
 */
__global__ void atlas_exp_f32(const float* a, float* b, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        b[gid] = expf(a[gid]);
    }
}

/**
 * Natural logarithm: b[i] = log(a[i]) (f32)
 */
__global__ void atlas_log_f32(const float* a, float* b, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        b[gid] = logf(a[gid]);
    }
}

// ============================================================================
// Fused Operations (Float32)
// ============================================================================

/**
 * Fused multiply-add: d[i] = a[i] * b[i] + c[i] (f32)
 */
__global__ void atlas_mad_f32(const float* a, const float* b, const float* c, float* d, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        d[gid] = fmaf(a[gid], b[gid], c[gid]);  // Use hardware FMA if available
    }
}

// ============================================================================
// Binary Element-wise Operations (Int32)
// ============================================================================

/**
 * Vector addition: c[i] = a[i] + b[i] (i32)
 */
__global__ void atlas_add_i32(const int* a, const int* b, int* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = a[gid] + b[gid];
    }
}

/**
 * Vector subtraction: c[i] = a[i] - b[i] (i32)
 */
__global__ void atlas_sub_i32(const int* a, const int* b, int* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = a[gid] - b[gid];
    }
}

/**
 * Vector multiplication: c[i] = a[i] * b[i] (i32)
 */
__global__ void atlas_mul_i32(const int* a, const int* b, int* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = a[gid] * b[gid];
    }
}

/**
 * Vector division: c[i] = a[i] / b[i] (i32)
 */
__global__ void atlas_div_i32(const int* a, const int* b, int* c, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        c[gid] = a[gid] / b[gid];
    }
}

// ============================================================================
// Memory Copy Operations
// ============================================================================

/**
 * Memory copy: dst[i] = src[i] (generic byte copy)
 */
__global__ void atlas_memcpy(const unsigned char* src, unsigned char* dst, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        dst[gid] = src[gid];
    }
}

/**
 * Memory fill: dst[i] = value (f32)
 */
__global__ void atlas_fill_f32(float* dst, float value, unsigned int n) {
    unsigned int gid = blockIdx.x * blockDim.x + threadIdx.x;
    if (gid < n) {
        dst[gid] = value;
    }
}

} // extern "C"
