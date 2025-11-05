/*
 * Minimal C Wrapper for UOR FFI
 *
 * This approach creates a minimal wrapper that can be compiled
 * independently without the full Lean runtime.
 */

#include <stdint.h>

#include <stdlib.h>

// Constants (hardcoded from Lean implementation)
#define UOR_PAGES 48
#define UOR_BYTES 256
#define UOR_RCLASSES 96

// Minimal implementations that don't require Lean runtime
uint32_t lean_uor_pages_minimal(void) {
  return UOR_PAGES;
}

uint32_t lean_uor_bytes_minimal(void) {
  return UOR_BYTES;
}

uint32_t lean_uor_rclasses_minimal(void) {
  return UOR_RCLASSES;
}

// R96 classifier - pure C implementation
uint8_t lean_uor_r96_classify_minimal(uint8_t b) {
  return b % UOR_RCLASSES;
}

// Phi encoding - pure C implementation
uint32_t lean_uor_phi_encode_minimal(uint8_t page, uint8_t byte) {
  return ((uint32_t)(page % UOR_PAGES) << 8) | byte;
}

uint8_t lean_uor_phi_page_minimal(uint32_t code) {
  return (code >> 8) % UOR_PAGES;
}

uint8_t lean_uor_phi_byte_minimal(uint32_t code) {
  return code & 0xFF;
}

// Truth/conservation - pure C implementation
uint8_t lean_uor_truth_zero_minimal(uint32_t budget) {
  return budget == 0 ? 1 : 0;
}

uint8_t lean_uor_truth_add_minimal(uint32_t a, uint32_t b) {
  return (a + b) == 0 ? 1 : 0;
}

// Initialization (no-op for minimal version)
void lean_initialize_uor_minimal(uintptr_t resv) {
  (void)resv;  // unused
}

void lean_finalize_uor_minimal(void) {
  // no-op
}