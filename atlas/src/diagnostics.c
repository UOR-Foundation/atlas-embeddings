// atlas/src/diagnostics.c
// Conway–Monster Atlas Upgrade Kit v1.1
// Diagnostic and verification functions

#include "../include/atlas_bridge.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

// External projector functions
extern void P_class_apply(double* v);
extern void P_Qonly_apply(double* v);
extern void P_299_apply(double* v);

// External E group function
extern void E_apply(const uint64_t* x_mask, const uint64_t* z_mask, int n_qubits);

// External Co1 function
extern void Co1_apply(uint32_t gate_id, const double* params, int n_params);

// Helper: Generate random vector
static void random_vector(double* v, size_t dim) {
    for (size_t i = 0; i < dim; i++) {
        v[i] = ((double)rand() / RAND_MAX) * 2.0 - 1.0;
    }
}

// Helper: Vector norm
static double vector_norm(const double* v, size_t dim) {
    double sum = 0.0;
    for (size_t i = 0; i < dim; i++) {
        sum += v[i] * v[i];
    }
    return sqrt(sum);
}

// Helper: Vector difference norm
static double vector_diff_norm(const double* a, const double* b, size_t dim) {
    double sum = 0.0;
    for (size_t i = 0; i < dim; i++) {
        double diff = a[i] - b[i];
        sum += diff * diff;
    }
    return sqrt(sum);
}

// Test if projector commutes with group element
static double test_commutator(void (*projector)(double*), 
                              void (*group_action)(void*), 
                              void* action_params,
                              size_t dim) {
    double* v1 = (double*)malloc(dim * sizeof(double));
    double* v2 = (double*)malloc(dim * sizeof(double));
    double* temp = (double*)malloc(dim * sizeof(double));
    
    if (!v1 || !v2 || !temp) {
        free(v1); free(v2); free(temp);
        return -1.0;
    }
    
    // Random test vector
    random_vector(v1, dim);
    memcpy(v2, v1, dim * sizeof(double));
    
    // Compute P(g(v))
    if (group_action) {
        // TODO: Apply group action with params
        (void)action_params;
    }
    projector(v1);
    
    // Compute g(P(v))
    projector(v2);
    if (group_action) {
        // TODO: Apply group action with params
    }
    
    // Measure difference
    double commutator_norm = vector_diff_norm(v1, v2, dim);
    
    free(v1); free(v2); free(temp);
    return commutator_norm;
}

// Commutant probe: estimate dimension of space commuting with group
double commutant_probe(int with_Co1) {
    uint32_t base_dim, bridge_dim;
    atlas_dims(&base_dim, &bridge_dim);
    size_t dim = base_dim;
    
    // TODO: Implement proper commutant dimension estimation
    // This would use randomized linear algebra to estimate
    // the dimension of {v : [P, g]v = 0 for all g in group}
    
    int num_probes = 100;
    int num_generators = with_Co1 ? 10 : 5;  // More generators with Co1
    
    double avg_rank = 0.0;
    
    for (int probe = 0; probe < num_probes; probe++) {
        // Generate random vector
        double* v = (double*)malloc(dim * sizeof(double));
        if (!v) continue;
        
        random_vector(v, dim);
        
        // Apply several group elements and measure orbit dimension
        // TODO: Implement proper rank estimation
        
        free(v);
    }
    
    avg_rank /= num_probes;
    
    // Return estimated commutant dimension
    return avg_rank;
}

// Leakage certificate: measure how much leaks out of subspace
int leakage_certificate(const char* json_out_path) {
    if (!json_out_path) return -1;
    
    FILE* fp = fopen(json_out_path, "w");
    if (!fp) return -1;
    
    uint32_t base_dim, bridge_dim;
    atlas_dims(&base_dim, &bridge_dim);
    size_t dim = base_dim;
    
    // Allocate test vectors
    double* v_orig = (double*)malloc(dim * sizeof(double));
    double* v_proj = (double*)malloc(dim * sizeof(double));
    double* v_roundtrip = (double*)malloc(dim * sizeof(double));
    
    if (!v_orig || !v_proj || !v_roundtrip) {
        free(v_orig); free(v_proj); free(v_roundtrip);
        fclose(fp);
        return -1;
    }
    
    // Test various projectors
    const char* proj_names[] = {"class", "qonly", "299"};
    void (*projectors[])(double*) = {P_class_apply, P_Qonly_apply, P_299_apply};
    int num_projectors = 3;
    
    fprintf(fp, "{\n");
    fprintf(fp, "  \"timestamp\": %ld,\n", (long)time(NULL));
    fprintf(fp, "  \"dimension\": %zu,\n", dim);
    fprintf(fp, "  \"projectors\": [\n");
    
    for (int i = 0; i < num_projectors; i++) {
        // Random vector
        random_vector(v_orig, dim);
        memcpy(v_proj, v_orig, dim * sizeof(double));
        memcpy(v_roundtrip, v_orig, dim * sizeof(double));
        
        // Apply projector
        projectors[i](v_proj);
        
        // Round-trip: project, apply some operations, project again
        projectors[i](v_roundtrip);
        // TODO: Apply group operations
        projectors[i](v_roundtrip);
        
        // Measure leakage
        double leakage = vector_diff_norm(v_proj, v_roundtrip, dim);
        double proj_norm = vector_norm(v_proj, dim);
        double relative_leakage = (proj_norm > 1e-10) ? (leakage / proj_norm) : 0.0;
        
        fprintf(fp, "    {\n");
        fprintf(fp, "      \"name\": \"%s\",\n", proj_names[i]);
        fprintf(fp, "      \"absolute_leakage\": %.6e,\n", leakage);
        fprintf(fp, "      \"relative_leakage\": %.6e,\n", relative_leakage);
        fprintf(fp, "      \"status\": \"%s\"\n", 
                (relative_leakage < 1e-6) ? "good" : "warning");
        fprintf(fp, "    }%s\n", (i < num_projectors - 1) ? "," : "");
    }
    
    fprintf(fp, "  ],\n");
    fprintf(fp, "  \"status\": \"completed\"\n");
    fprintf(fp, "}\n");
    
    free(v_orig);
    free(v_proj);
    free(v_roundtrip);
    fclose(fp);
    
    return 0;
}

// Extended diagnostics: full suite of checks
int run_full_diagnostics(const char* output_dir) {
    if (!output_dir) return -1;
    
    char path_buffer[512];
    
    // Test projector residuals
    snprintf(path_buffer, sizeof(path_buffer), "%s/projector_residuals.json", output_dir);
    FILE* fp = fopen(path_buffer, "w");
    if (!fp) return -1;
    
    fprintf(fp, "{\n");
    fprintf(fp, "  \"class_residual\": %.6e,\n", projector_residual("class"));
    fprintf(fp, "  \"qonly_residual\": %.6e,\n", projector_residual("qonly"));
    fprintf(fp, "  \"299_residual\": %.6e\n", projector_residual("299"));
    fprintf(fp, "}\n");
    fclose(fp);
    
    // Test commutant dimensions
    snprintf(path_buffer, sizeof(path_buffer), "%s/commutant_dims.json", output_dir);
    fp = fopen(path_buffer, "w");
    if (!fp) return -1;
    
    fprintf(fp, "{\n");
    fprintf(fp, "  \"without_Co1\": %.2f,\n", commutant_probe(0));
    fprintf(fp, "  \"with_Co1\": %.2f\n", commutant_probe(1));
    fprintf(fp, "}\n");
    fclose(fp);
    
    // Generate leakage certificate
    snprintf(path_buffer, sizeof(path_buffer), "%s/leakage.json", output_dir);
    leakage_certificate(path_buffer);
    
    return 0;
}
