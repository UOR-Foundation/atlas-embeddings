/*
 * Advanced Example: Performance Testing and Validation
 *
 * Compile: gcc -o advanced advanced.c
 * Run: ./advanced
 */

#include <stdio.h>

#include "../c/uor_ffi_hybrid.h"

#include <assert.h>
#include <time.h>

#define ITERATIONS 1000000

// Benchmark a function
double benchmark(const char *name, void (*func)(void)) {
  clock_t start = clock();
  func();
  clock_t end  = clock();
  double  time = ((double)(end - start)) / CLOCKS_PER_SEC;
  printf("  %s: %.3f seconds (%d ops/sec)\n", name, time,
         (int)(ITERATIONS / time));
  return time;
}

// Test functions for benchmarking
void test_r96_classify(void) {
  volatile uint8_t result;
  for (int i = 0; i < ITERATIONS; i++) {
    result = UOR_R96_CLASSIFY(i & 0xFF);
  }
}

void test_phi_encode(void) {
  volatile uint32_t result;
  for (int i = 0; i < ITERATIONS; i++) {
    result = UOR_PHI_ENCODE(i & 0x3F, i & 0xFF);
  }
}

void test_phi_decode(void) {
  volatile uint8_t page, byte;
  for (int i = 0; i < ITERATIONS; i++) {
    page = UOR_PHI_PAGE(i);
    byte = UOR_PHI_BYTE(i);
  }
}

void test_truth(void) {
  volatile uint8_t result;
  for (int i = 0; i < ITERATIONS; i++) {
    result = UOR_TRUTH_ZERO(i);
  }
}

// Validate mathematical properties
void validate_properties(void) {
  printf("Validating Mathematical Properties:\n");

  // 1. Compression ratio
  double ratio = (double)UOR_RCLASSES() / UOR_BYTES();
  assert(ratio == 0.375);  // 3/8
  printf("  ✓ Compression ratio: %.3f (3/8)\n", ratio);

  // 2. Total elements
  int total = UOR_PAGES() * UOR_BYTES();
  assert(total == 12288);
  assert(total == 3 * 4096);  // 3 * 2^12
  printf("  ✓ Total elements: %d (3 × 2^12)\n", total);

  // 3. R96 surjectivity
  int seen[96] = {0};
  for (int i = 0; i < 256; i++) {
    seen[UOR_R96_CLASSIFY(i)] = 1;
  }
  int all_seen = 1;
  for (int i = 0; i < 96; i++) {
    if (!seen[i])
      all_seen = 0;
  }
  assert(all_seen);
  printf("  ✓ R96 is surjective\n");

  // 4. Phi round-trip
  for (int p = 0; p < 48; p++) {
    for (int b = 0; b < 256; b += 17) {
      uint32_t code = UOR_PHI_ENCODE(p, b);
      assert(UOR_PHI_PAGE(code) == p);
      assert(UOR_PHI_BYTE(code) == b);
    }
  }
  printf("  ✓ Phi encoding is bijective\n");

  // 5. Truth conservation
  assert(UOR_TRUTH_ZERO(0) == 1);
  assert(UOR_TRUTH_ADD(0, 0) == 1);
  assert(UOR_TRUTH_ADD(1, 0) == 0);
  printf("  ✓ Truth ≙ conservation\n");
}

int main(void) {
  printf("UOR Prime Structure - Advanced Example\n");
  printf("======================================\n\n");

  UOR_INIT(0);

  // Validate properties
  validate_properties();
  printf("\n");

  // Performance benchmarks
  printf("Performance Benchmarks (%d iterations):\n", ITERATIONS);
  benchmark("R96 Classify", test_r96_classify);
  benchmark("Phi Encode  ", test_phi_encode);
  benchmark("Phi Decode  ", test_phi_decode);
  benchmark("Truth Check ", test_truth);
  printf("\n");

  // Memory footprint
  printf("Memory Footprint:\n");
  printf("  Constants: %zu bytes\n", sizeof(uint32_t) * 3);
  printf("  No heap allocation required\n");
  printf("  Stack usage: O(1)\n");

  UOR_FINALIZE();

  printf("\n✓ All validations passed!\n");
  return 0;
}