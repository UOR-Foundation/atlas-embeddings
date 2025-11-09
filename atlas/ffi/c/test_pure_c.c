/*
 * Pure C Test for UOR FFI
 *
 * This test uses the pure C implementation without Lean dependencies.
 */

#include <stdio.h>

#include <assert.h>

// Use pure C implementation
#undef UOR_USE_LEAN_RUNTIME
#include "uor_ffi_hybrid.h"

int main(void) {
  printf("=== UOR FFI Pure C Test ===\n\n");

  // Initialize (no-op in pure C)
  UOR_INIT(0);

  // Test constants
  printf("Testing constants:\n");
  printf("  Pages: %u (expected 48)\n", UOR_PAGES());
  assert(UOR_PAGES() == 48);
  printf("  Bytes: %u (expected 256)\n", UOR_BYTES());
  assert(UOR_BYTES() == 256);
  printf("  R-classes: %u (expected 96)\n", UOR_RCLASSES());
  assert(UOR_RCLASSES() == 96);
  printf("  ✓ Constants correct\n\n");

  // Test R96 classifier
  printf("Testing R96 classifier:\n");
  assert(UOR_R96_CLASSIFY(0) == 0);
  assert(UOR_R96_CLASSIFY(95) == 95);
  assert(UOR_R96_CLASSIFY(96) == 0);
  assert(UOR_R96_CLASSIFY(255) == 63);
  printf("  ✓ R96 classifier working\n\n");

  // Test Phi encoding
  printf("Testing Phi encoding:\n");
  uint32_t code = UOR_PHI_ENCODE(3, 16);
  assert(UOR_PHI_PAGE(code) == 3);
  assert(UOR_PHI_BYTE(code) == 16);
  printf("  ✓ Phi encode/decode working\n\n");

  // Test truth/conservation
  printf("Testing truth/conservation:\n");
  assert(UOR_TRUTH_ZERO(0) == 1);
  assert(UOR_TRUTH_ZERO(1) == 0);
  assert(UOR_TRUTH_ADD(0, 0) == 1);
  assert(UOR_TRUTH_ADD(1, 0) == 0);
  printf("  ✓ Truth functions working\n\n");

  // Finalize (no-op in pure C)
  UOR_FINALIZE();

  printf("✓ ALL TESTS PASSED!\n");
  return 0;
}