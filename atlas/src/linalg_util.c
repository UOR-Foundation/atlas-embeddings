// atlas_core/src/linalg_util.c
// Conway–Monster Atlas Upgrade Kit v1.1
// Linear algebra utilities for vector operations

#include <stddef.h>
#include <math.h>
#include <string.h>

// Vector operations

void vec_zero(double* v, size_t n) {
    // Zero out vector
    if (!v) return;
    for (size_t i = 0; i < n; i++) {
        v[i] = 0.0;
    }
}

void vec_copy(double* dst, const double* src, size_t n) {
    // Copy vector
    if (!dst || !src) return;
    memcpy(dst, src, n * sizeof(double));
}

void vec_scale(double* v, double scalar, size_t n) {
    // Scale vector in-place
    if (!v) return;
    for (size_t i = 0; i < n; i++) {
        v[i] *= scalar;
    }
}

void vec_add(double* result, const double* a, const double* b, size_t n) {
    // result = a + b
    if (!result || !a || !b) return;
    for (size_t i = 0; i < n; i++) {
        result[i] = a[i] + b[i];
    }
}

void vec_sub(double* result, const double* a, const double* b, size_t n) {
    // result = a - b
    if (!result || !a || !b) return;
    for (size_t i = 0; i < n; i++) {
        result[i] = a[i] - b[i];
    }
}

double vec_dot(const double* a, const double* b, size_t n) {
    // Compute dot product
    if (!a || !b) return 0.0;
    double sum = 0.0;
    for (size_t i = 0; i < n; i++) {
        sum += a[i] * b[i];
    }
    return sum;
}

double vec_norm(const double* v, size_t n) {
    // Compute L2 norm
    if (!v) return 0.0;
    return sqrt(vec_dot(v, v, n));
}

double vec_dist(const double* a, const double* b, size_t n) {
    // Compute distance between vectors
    if (!a || !b || n == 0) return 0.0;
    
    double sum_sq = 0.0;
    for (size_t i = 0; i < n; i++) {
        double diff = a[i] - b[i];
        sum_sq += diff * diff;
    }
    return sqrt(sum_sq);
}

void vec_normalize(double* v, size_t n) {
    // Normalize vector in-place
    if (!v) return;
    double norm = vec_norm(v, n);
    if (norm > 1e-10) {
        vec_scale(v, 1.0 / norm, n);
    }
}

// Matrix-vector operations (stub)
void mat_vec_multiply(double* result, const double* matrix, const double* vec, size_t rows, size_t cols) {
    // result = matrix * vec
    // TODO: Implement sparse matrix operations for efficiency
    if (!result || !matrix || !vec) return;
    
    for (size_t i = 0; i < rows; i++) {
        result[i] = 0.0;
        for (size_t j = 0; j < cols; j++) {
            result[i] += matrix[i * cols + j] * vec[j];
        }
    }
}

// Gram-Schmidt orthogonalization
void gram_schmidt(double* vectors, size_t num_vectors, size_t dim) {
    // Orthogonalize vectors in-place using Gram-Schmidt
    // TODO: Implement with proper numerical stability
    if (!vectors) return;
    
    for (size_t i = 0; i < num_vectors; i++) {
        double* v_i = vectors + i * dim;
        
        // Subtract projections onto previous vectors
        for (size_t j = 0; j < i; j++) {
            double* v_j = vectors + j * dim;
            double proj = vec_dot(v_i, v_j, dim);
            for (size_t k = 0; k < dim; k++) {
                v_i[k] -= proj * v_j[k];
            }
        }
        
        // Normalize
        vec_normalize(v_i, dim);
    }
}
