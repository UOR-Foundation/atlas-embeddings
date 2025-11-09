/*
 * UOR Prime Structure FFI - Comprehensive Test Suite
 *
 * This test suite validates all FFI functions against expected values
 * and mathematical invariants of the Prime Structure.
 */

#include <stdint.h>

#include <stdio.h>

#include "uor_ffi.h"

#include <assert.h>
#include <string.h>

/* ANSI color codes for test output */
#define GREEN "\033[0;32m"
#define RED "\033[0;31m"
#define YELLOW "\033[0;33m"
#define RESET "\033[0m"

/* Test result tracking */
static int tests_run    = 0;
static int tests_passed = 0;
static int tests_failed = 0;

/* Test assertion macros */
#define TEST_ASSERT(expr, msg)                            \
  do {                                                    \
    tests_run++;                                          \
    if (!(expr)) {                                        \
      printf(RED "  ✗ %s: %s" RESET "\n", __func__, msg); \
      tests_failed++;                                     \
      return 0;                                           \
    }                                                     \
    tests_passed++;                                       \
    return 1;                                             \
  } while (0)

#define RUN_TEST(test_func)               \
  do {                                    \
    printf("Running %s... ", #test_func); \
    if (test_func()) {                    \
      printf(GREEN "✓" RESET "\n");       \
    }                                     \
  } while (0)

/* Test Functions */

int test_abi_version(void) {
  uint32_t version = lean_uor_abi_version();
  TEST_ASSERT(version == UOR_FFI_ABI_VERSION, "ABI version mismatch");
}

int test_constants(void) {
  uint32_t pages    = lean_uor_pages();
  uint32_t bytes    = lean_uor_bytes();
  uint32_t rclasses = lean_uor_rclasses();

  TEST_ASSERT(pages == 48, "Pages should be 48");
  TEST_ASSERT(bytes == 256, "Bytes should be 256");
  TEST_ASSERT(rclasses == 96, "R-classes should be 96");
  TEST_ASSERT(pages * bytes == 12288, "Total elements should be 12288");
}

int test_r96_classifier_range(void) {
  /* Test that all outputs are in valid range */
  for (int i = 0; i < 256; i++) {
    uint8_t cls = lean_uor_r96_classify((uint8_t)i);
    if (cls >= 96) {
      char msg[100];
      sprintf(msg, "R96(%d) = %d, expected < 96", i, cls);
      TEST_ASSERT(0, msg);
    }
  }
  TEST_ASSERT(1, "All R96 outputs in valid range");
}

int test_r96_classifier_surjective(void) {
  /* Test that all 96 classes are produced */
  int class_seen[96] = {0};

  for (int i = 0; i < 256; i++) {
    uint8_t cls     = lean_uor_r96_classify((uint8_t)i);
    class_seen[cls] = 1;
  }

  for (int i = 0; i < 96; i++) {
    if (!class_seen[i]) {
      char msg[100];
      sprintf(msg, "Class %d never produced", i);
      TEST_ASSERT(0, msg);
    }
  }
  TEST_ASSERT(1, "R96 is surjective onto [0,95]");
}

int test_r96_classifier_periodic(void) {
  /* Test periodicity with period 96 */
  for (int i = 0; i < 160; i++) { /* Test beyond 96 */
    uint8_t cls1 = lean_uor_r96_classify((uint8_t)i);
    uint8_t cls2 = lean_uor_r96_classify((uint8_t)(i + 96));
    if (cls1 != cls2) {
      char msg[100];
      sprintf(msg, "R96(%d) != R96(%d), expected periodic", i, i + 96);
      TEST_ASSERT(0, msg);
    }
  }
  TEST_ASSERT(1, "R96 has period 96");
}

int test_r96_specific_values(void) {
  /* Test specific known values */
  TEST_ASSERT(lean_uor_r96_classify(0) == 0, "R96(0) should be 0");
  TEST_ASSERT(lean_uor_r96_classify(95) == 95, "R96(95) should be 95");
  TEST_ASSERT(lean_uor_r96_classify(96) == 0, "R96(96) should be 0");
  TEST_ASSERT(lean_uor_r96_classify(255) == 63, "R96(255) should be 63");
}

int test_phi_encode_decode(void) {
  /* Test encoding and decoding round-trip */
  for (uint8_t page = 0; page < 48; page++) {
    for (uint8_t byte = 0; byte < 256; byte += 17) { /* Sample testing */
      uint32_t code         = lean_uor_phi_encode(page, byte);
      uint8_t  decoded_page = lean_uor_phi_page(code);
      uint8_t  decoded_byte = lean_uor_phi_byte(code);

      if (decoded_page != page || decoded_byte != byte) {
        char msg[100];
        sprintf(msg, "Round-trip failed for (%d,%d)", page, byte);
        TEST_ASSERT(0, msg);
      }
    }
  }
  TEST_ASSERT(1, "Phi encode/decode round-trip successful");
}

int test_phi_encode_format(void) {
  /* Test encoding format: (page << 8) | byte */
  uint32_t code     = lean_uor_phi_encode(3, 16);
  uint32_t expected = (3 << 8) | 16;
  TEST_ASSERT(code == expected, "Encoding should be (page << 8) | byte");
}

int test_phi_page_modulo(void) {
  /* Test that page extraction applies modulo 48 */
  uint32_t code1 = lean_uor_phi_encode(5, 100);
  uint32_t code2 = lean_uor_phi_encode(53, 100); /* 53 % 48 = 5 */

  uint8_t page1 = lean_uor_phi_page(code1);
  uint8_t page2 = lean_uor_phi_page(code2);

  TEST_ASSERT(page1 == 5, "Page should be 5");
  TEST_ASSERT(page2 == 5, "Page 53 should become 5 (mod 48)");
}

int test_phi_byte_extraction(void) {
  /* Test byte extraction (low 8 bits) */
  uint32_t code = 0x12345678;
  uint8_t  byte = lean_uor_phi_byte(code);
  TEST_ASSERT(byte == 0x78, "Should extract low 8 bits");
}

int test_truth_zero(void) {
  /* Test truth ≙ conservation (zero budget) */
  TEST_ASSERT(lean_uor_truth_zero(0) == 1, "Truth(0) should be true");
  TEST_ASSERT(lean_uor_truth_zero(1) == 0, "Truth(1) should be false");
  TEST_ASSERT(lean_uor_truth_zero(100) == 0, "Truth(100) should be false");
  TEST_ASSERT(lean_uor_truth_zero(0xFFFFFFFF) == 0,
              "Truth(MAX) should be false");
}

int test_truth_add_identity(void) {
  /* Test additive identity: Truth(0 + 0) = true */
  TEST_ASSERT(lean_uor_truth_add(0, 0) == 1, "Truth(0+0) should be true");
}

int test_truth_add_nonzero(void) {
  /* Test that non-zero sums are false */
  TEST_ASSERT(lean_uor_truth_add(1, 0) == 0, "Truth(1+0) should be false");
  TEST_ASSERT(lean_uor_truth_add(0, 1) == 0, "Truth(0+1) should be false");
  TEST_ASSERT(lean_uor_truth_add(5, 10) == 0, "Truth(5+10) should be false");
}

int test_truth_add_overflow(void) {
  /* Test overflow case: MAX + 1 wraps to 0 */
  uint32_t max    = 0xFFFFFFFF;
  uint8_t  result = lean_uor_truth_add(max, 1);
  /* Note: This tests 32-bit overflow behavior */
  TEST_ASSERT(result == 1, "Truth(MAX+1) should wrap to 0 (true)");
}

/* Invariant Tests */

int test_compression_ratio(void) {
  /* Verify 3/8 compression ratio */
  uint32_t rclasses = lean_uor_rclasses();
  uint32_t bytes    = lean_uor_bytes();

  /* 96/256 = 3/8 */
  TEST_ASSERT(rclasses * 8 == bytes * 3, "Compression ratio should be 3/8");
}

int test_total_elements(void) {
  /* Verify total element count */
  uint32_t pages = lean_uor_pages();
  uint32_t bytes = lean_uor_bytes();
  uint32_t total = pages * bytes;

  TEST_ASSERT(total == 12288, "Total elements should be 12288");
  TEST_ASSERT(total == (1 << 12) * 3, "12288 = 2^12 * 3");
}

int test_page_structure(void) {
  /* Verify page count structure: 48 = 3 * 16 = 3 * 2^4 */
  uint32_t pages = lean_uor_pages();
  TEST_ASSERT(pages == 48, "Pages should be 48");
  TEST_ASSERT(pages == 3 * 16, "48 = 3 * 16");
  TEST_ASSERT(pages == 3 * (1 << 4), "48 = 3 * 2^4");
}

int test_byte_structure(void) {
  /* Verify byte count structure: 256 = 2^8 */
  uint32_t bytes = lean_uor_bytes();
  TEST_ASSERT(bytes == 256, "Bytes should be 256");
  TEST_ASSERT(bytes == (1 << 8), "256 = 2^8");
}

int test_rclass_structure(void) {
  /* Verify resonance class structure: 96 = 3 * 32 = 3 * 2^5 */
  uint32_t rclasses = lean_uor_rclasses();
  TEST_ASSERT(rclasses == 96, "R-classes should be 96");
  TEST_ASSERT(rclasses == 3 * 32, "96 = 3 * 32");
  TEST_ASSERT(rclasses == 3 * (1 << 5), "96 = 3 * 2^5");
}

/* Main Test Runner */

void print_test_summary(void) {
  printf("\n" YELLOW "═══════════════════════════════════════" RESET "\n");
  printf(YELLOW "Test Summary:" RESET "\n");
  printf("  Total tests run: %d\n", tests_run);
  printf("  Tests passed: " GREEN "%d" RESET "\n", tests_passed);
  printf("  Tests failed: " RED "%d" RESET "\n", tests_failed);

  if (tests_failed == 0) {
    printf("\n" GREEN "✓ ALL TESTS PASSED!" RESET "\n");
  } else {
    printf("\n" RED "✗ SOME TESTS FAILED" RESET "\n");
  }
  printf(YELLOW "═══════════════════════════════════════" RESET "\n");
}

int main(void) {
  printf(YELLOW "═══════════════════════════════════════" RESET "\n");
  printf(YELLOW "UOR Prime Structure FFI Test Suite" RESET "\n");
  printf(YELLOW "═══════════════════════════════════════" RESET "\n\n");

  /* Initialize the library */
  printf("Initializing UOR library...\n");
  lean_initialize_uor(0);
  printf("Library initialized.\n\n");

  /* Run all tests */
  printf(YELLOW "Running Constants Tests:" RESET "\n");
  RUN_TEST(test_abi_version);
  RUN_TEST(test_constants);

  printf("\n" YELLOW "Running R96 Classifier Tests:" RESET "\n");
  RUN_TEST(test_r96_classifier_range);
  RUN_TEST(test_r96_classifier_surjective);
  RUN_TEST(test_r96_classifier_periodic);
  RUN_TEST(test_r96_specific_values);

  printf("\n" YELLOW "Running Φ Encoding Tests:" RESET "\n");
  RUN_TEST(test_phi_encode_decode);
  RUN_TEST(test_phi_encode_format);
  RUN_TEST(test_phi_page_modulo);
  RUN_TEST(test_phi_byte_extraction);

  printf("\n" YELLOW "Running Truth/Conservation Tests:" RESET "\n");
  RUN_TEST(test_truth_zero);
  RUN_TEST(test_truth_add_identity);
  RUN_TEST(test_truth_add_nonzero);
  RUN_TEST(test_truth_add_overflow);

  printf("\n" YELLOW "Running Mathematical Invariant Tests:" RESET "\n");
  RUN_TEST(test_compression_ratio);
  RUN_TEST(test_total_elements);
  RUN_TEST(test_page_structure);
  RUN_TEST(test_byte_structure);
  RUN_TEST(test_rclass_structure);

  /* Print summary */
  print_test_summary();

  /* Finalize the library */
  printf("\nFinalizing UOR library...\n");
  lean_finalize_uor();
  printf("Library finalized.\n");

  return tests_failed > 0 ? 1 : 0;
}