/*
 * UOR Prime Structure FFI - Minimal Wrapper Test Suite
 *
 * This test suite validates all FFI functions using the minimal wrapper
 * implementation to avoid C++ ABI linking issues.
 */

#include <stdint.h>

#include <stdio.h>

#include "minimal_wrapper.c"

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

int test_constants(void) {
  TEST_ASSERT(lean_uor_pages_minimal() == 48, "Pages should be 48");
  TEST_ASSERT(lean_uor_bytes_minimal() == 256, "Bytes should be 256");
  TEST_ASSERT(lean_uor_rclasses_minimal() == 96, "RClasses should be 96");
}

int test_r96_classifier_range(void) {
  /* Test that all outputs are in range [0, 95] */
  for (int i = 0; i <= 255; i++) {
    uint8_t result = lean_uor_r96_classify_minimal((uint8_t)i);
    if (result >= 96) {
      char msg[100];
      sprintf(msg, "R96(%d) = %d, expected < 96", i, result);
      TEST_ASSERT(0, msg);
    }
  }
  TEST_ASSERT(1, "All R96 outputs in valid range");
}

int test_r96_classifier_periodic(void) {
  /* Test periodicity with period 96 */
  for (int i = 0; i < 160; i++) { /* Test beyond 96 */
    uint8_t cls1 = lean_uor_r96_classify_minimal((uint8_t)i);
    uint8_t cls2 = lean_uor_r96_classify_minimal((uint8_t)(i + 96));
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
  TEST_ASSERT(lean_uor_r96_classify_minimal(0) == 0, "R96(0) should be 0");
  TEST_ASSERT(lean_uor_r96_classify_minimal(95) == 95, "R96(95) should be 95");
  TEST_ASSERT(lean_uor_r96_classify_minimal(96) == 0, "R96(96) should be 0");
  TEST_ASSERT(lean_uor_r96_classify_minimal(255) == 63,
              "R96(255) should be 63");
}

int test_phi_encode_decode(void) {
  /* Test encoding and decoding round-trip */
  for (uint8_t page = 0; page < 48; page++) {
    for (uint8_t byte = 0; byte < 256; byte += 17) { /* Sample testing */
      uint32_t code         = lean_uor_phi_encode_minimal(page, byte);
      uint8_t  decoded_page = lean_uor_phi_page_minimal(code);
      uint8_t  decoded_byte = lean_uor_phi_byte_minimal(code);

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
  uint32_t code     = lean_uor_phi_encode_minimal(3, 16);
  uint32_t expected = (3 << 8) | 16;
  TEST_ASSERT(code == expected, "Encoding should be (page << 8) | byte");
}

int test_truth_conservation(void) {
  /* Test truth conservation functions */
  TEST_ASSERT(lean_uor_truth_zero_minimal(0) == 1, "Truth(0) should be true");
  TEST_ASSERT(lean_uor_truth_zero_minimal(1) == 0, "Truth(1) should be false");
  TEST_ASSERT(lean_uor_truth_zero_minimal(100) == 0,
              "Truth(100) should be false");

  TEST_ASSERT(lean_uor_truth_add_minimal(0, 0) == 1,
              "Truth(0+0) should be true");
  TEST_ASSERT(lean_uor_truth_add_minimal(1, 0) == 0,
              "Truth(1+0) should be false");
  TEST_ASSERT(lean_uor_truth_add_minimal(5, 10) == 0,
              "Truth(5+10) should be false");

  /* Test overflow */
  TEST_ASSERT(lean_uor_truth_add_minimal(0xFFFFFFFF, 1) == 1,
              "Truth(MAX+1) should be true (overflow)");
}

void print_summary(void) {
  printf(YELLOW "═══════════════════════════════════════" RESET "\n");
  printf("Tests run: %d\n", tests_run);
  printf(GREEN "Tests passed: %d" RESET "\n", tests_passed);

  if (tests_failed > 0) {
    printf(RED "Tests failed: %d" RESET "\n", tests_failed);
    printf("\n" RED "✗ SOME TESTS FAILED" RESET "\n");
  } else {
    printf("\n" GREEN "✓ ALL TESTS PASSED" RESET "\n");
  }
  printf(YELLOW "═══════════════════════════════════════" RESET "\n");
}

int main(void) {
  printf(YELLOW "═══════════════════════════════════════" RESET "\n");
  printf(YELLOW "UOR Prime Structure FFI Test Suite (Minimal)" RESET "\n");
  printf(YELLOW "═══════════════════════════════════════" RESET "\n\n");

  /* Initialize the minimal wrapper */
  printf("Initializing UOR minimal wrapper...\n");
  lean_initialize_uor_minimal(0);
  printf("Wrapper initialized.\n\n");

  /* Run all tests */
  printf(YELLOW "Running Constants Tests:" RESET "\n");
  RUN_TEST(test_constants);

  printf("\n" YELLOW "Running R96 Classifier Tests:" RESET "\n");
  RUN_TEST(test_r96_classifier_range);
  RUN_TEST(test_r96_classifier_periodic);
  RUN_TEST(test_r96_specific_values);

  printf("\n" YELLOW "Running Φ Encoding Tests:" RESET "\n");
  RUN_TEST(test_phi_encode_decode);
  RUN_TEST(test_phi_encode_format);

  printf("\n" YELLOW "Running Truth Conservation Tests:" RESET "\n");
  RUN_TEST(test_truth_conservation);

  printf("\n");
  print_summary();

  return tests_failed > 0 ? 1 : 0;
}