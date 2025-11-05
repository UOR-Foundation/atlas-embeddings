/*
 * Simple FFI test to verify basic functionality
 */

#include "minimal_wrapper.c"
#include <stdio.h>

int main(void) {
  printf("Testing UOR FFI (minimal wrapper)...\n");

  // Initialize
  lean_initialize_uor_minimal(0);

  // Test constants
  printf("Pages: %u (expected 48)\n", lean_uor_pages_minimal());
  printf("Bytes: %u (expected 256)\n", lean_uor_bytes_minimal());
  printf("RClasses: %u (expected 96)\n", lean_uor_rclasses_minimal());

  // Test R96 classification
  printf("R96(0): %u (expected 0)\n", lean_uor_r96_classify_minimal(0));
  printf("R96(95): %u (expected 95)\n", lean_uor_r96_classify_minimal(95));
  printf("R96(96): %u (expected 0)\n", lean_uor_r96_classify_minimal(96));

  // Test Phi encoding
  uint32_t code = lean_uor_phi_encode_minimal(3, 16);
  printf("PhiEncode(3,16): %u\n", code);
  printf("PhiPage(%u): %u (expected 3)\n", code,
         lean_uor_phi_page_minimal(code));
  printf("PhiByte(%u): %u (expected 16)\n", code,
         lean_uor_phi_byte_minimal(code));

  // Test truth functions
  printf("Truth(0): %u (expected 1)\n", lean_uor_truth_zero_minimal(0));
  printf("Truth(1): %u (expected 0)\n", lean_uor_truth_zero_minimal(1));

  printf("All basic tests completed successfully!\n");
  return 0;
}