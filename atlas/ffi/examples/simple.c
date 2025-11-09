/*
 * Simple Example: Using UOR FFI in Pure C Mode
 *
 * Compile: gcc -o simple simple.c
 * Run: ./simple
 */

#include <stdio.h>

#include "../c/uor_ffi_hybrid.h"

int main(void) {
  printf("UOR Prime Structure - Simple Example\n");
  printf("=====================================\n\n");

  // Initialize (no-op in pure C mode)
  UOR_INIT(0);

  // Display constants
  printf("Structure Constants:\n");
  printf("  Pages: %u\n", UOR_PAGES());
  printf("  Bytes per page: %u\n", UOR_BYTES());
  printf("  Resonance classes: %u\n", UOR_RCLASSES());
  printf("  Total elements: %u\n", UOR_PAGES() * UOR_BYTES());
  printf("\n");

  // Demonstrate R96 classification
  printf("R96 Classification Examples:\n");
  for (int i = 0; i <= 100; i += 10) {
    printf("  R96(%3d) = %2u\n", i, UOR_R96_CLASSIFY(i));
  }
  printf("\n");

  // Demonstrate Phi encoding
  printf("Phi Encoding Examples:\n");
  for (int page = 0; page < 5; page++) {
    uint32_t code = UOR_PHI_ENCODE(page, page * 10);
    printf("  Encode(%d, %d) = 0x%04X", page, page * 10, code);
    printf(" -> Decode: page=%u, byte=%u\n", UOR_PHI_PAGE(code),
           UOR_PHI_BYTE(code));
  }
  printf("\n");

  // Demonstrate truth/conservation
  printf("Truth/Conservation:\n");
  printf("  Truth(0) = %s\n", UOR_TRUTH_ZERO(0) ? "true" : "false");
  printf("  Truth(1) = %s\n", UOR_TRUTH_ZERO(1) ? "true" : "false");
  printf("  Truth(0 + 0) = %s\n", UOR_TRUTH_ADD(0, 0) ? "true" : "false");
  printf("  Truth(5 + 10) = %s\n", UOR_TRUTH_ADD(5, 10) ? "true" : "false");

  // Finalize (no-op in pure C mode)
  UOR_FINALIZE();

  return 0;
}