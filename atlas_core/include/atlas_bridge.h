// atlas_core/include/atlas_bridge.h
#ifndef ATLAS_BRIDGE_H
#define ATLAS_BRIDGE_H
#include <stdint.h>

#define ATLAS_MODE_CLASS  0
#define ATLAS_MODE_BRIDGE 1

#ifdef __cplusplus
extern "C" {
#endif

// Sizing
int      atlas_dims(uint32_t* base, uint32_t* bridge); // base=12288, bridge=98304
void     atlas_set_mode(int mode);
void     atlas_spinlift_enable(int on);                // 0/1, only effective in BRIDGE

// Indexing on base and lifted bridge
uint32_t phi_encode(uint8_t page, uint8_t byte);       // 0..12287
int      phi_decode(uint32_t idx, uint8_t* page, uint8_t* byte);
static inline uint32_t phi_bridge(uint32_t idx_base, uint8_t k) { return idx_base + 12288u * (k & 7u); }

// Group actions
// E action specified by (x,z) in F_2^{12}×F_2^{12} packed into 24-bit masks; center = -I enforced.
void     E_apply(const uint64_t* x_mask, const uint64_t* z_mask, int n_qubits); // n_qubits=12
// Co1 reduced-rank gate family (opaque IDs) with optional params
void     Co1_apply(uint32_t gate_id, const double* params, int n_params);

// Projectors (operate in-place on double vectors of length 12288 or 98304 depending on mode)
void     P_class_apply(double* v);
void     P_Qonly_apply(double* v);
void     P_299_apply(double* v);

// Diagnostics and certificates
// Returns ||P^2-P||_2 and max_g ||gP-Pg||_2 over a canned generator set
double   projector_residual(const char* pname);
// Effective commutant dimension estimate via randomized probing; with_Co1 toggles extra constraints
double   commutant_probe(int with_Co1);
// Round-trip leakage report (JSON dumped to path), returns 0 on success
int      leakage_certificate(const char* json_out_path);

#ifdef __cplusplus
}
#endif
#endif // ATLAS_BRIDGE_H
