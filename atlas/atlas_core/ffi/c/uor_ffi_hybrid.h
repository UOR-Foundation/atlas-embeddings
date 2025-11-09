/*
 * UOR FFI Hybrid Header
 *
 * This header provides both Lean-backed and pure C implementations.
 * Use UOR_USE_LEAN_RUNTIME to switch between them.
 */

#ifndef UOR_FFI_HYBRID_H
#define UOR_FFI_HYBRID_H

#include <stdint.h>

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

// Configuration
#ifdef UOR_USE_LEAN_RUNTIME
// Use full Lean runtime (requires linking with Lean libraries)
#define UOR_INIT(resv) lean_initialize_uor(resv)
#define UOR_FINALIZE() lean_finalize_uor()
#define UOR_PAGES() lean_uor_pages()
#define UOR_BYTES() lean_uor_bytes()
#define UOR_RCLASSES() lean_uor_rclasses()
#define UOR_R96_CLASSIFY(b) lean_uor_r96_classify(b)
#define UOR_PHI_ENCODE(p, b) lean_uor_phi_encode(p, b)
#define UOR_PHI_PAGE(c) lean_uor_phi_page(c)
#define UOR_PHI_BYTE(c) lean_uor_phi_byte(c)
#define UOR_TRUTH_ZERO(b) lean_uor_truth_zero(b)
#define UOR_TRUTH_ADD(a, b) lean_uor_truth_add(a, b)

// External Lean functions
void     lean_initialize_uor(uintptr_t resv);
void     lean_finalize_uor(void);
uint32_t lean_uor_pages(void);
uint32_t lean_uor_bytes(void);
uint32_t lean_uor_rclasses(void);
uint8_t  lean_uor_r96_classify(uint8_t b);
uint32_t lean_uor_phi_encode(uint8_t page, uint8_t byte);
uint8_t  lean_uor_phi_page(uint32_t code);
uint8_t  lean_uor_phi_byte(uint32_t code);
uint8_t  lean_uor_truth_zero(uint32_t budget);
uint8_t  lean_uor_truth_add(uint32_t a, uint32_t b);

#else
// Use pure C implementation (no Lean dependencies)
#define UOR_INIT(resv) ((void)0)
#define UOR_FINALIZE() ((void)0)
#define UOR_PAGES() (48)
#define UOR_BYTES() (256)
#define UOR_RCLASSES() (96)
#define UOR_R96_CLASSIFY(b) ((b) % 96)
#define UOR_PHI_ENCODE(p, b) ((((uint32_t)(p) % 48) << 8) | (b))
#define UOR_PHI_PAGE(c) (((c) >> 8) % 48)
#define UOR_PHI_BYTE(c) ((c) & 0xFF)
#define UOR_TRUTH_ZERO(b) ((b) == 0 ? 1 : 0)
#define UOR_TRUTH_ADD(a, b) (((a) + (b)) == 0 ? 1 : 0)
#endif

#ifdef __cplusplus
}
#endif

#endif /* UOR_FFI_HYBRID_H */