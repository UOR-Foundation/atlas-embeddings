/*
 * UOR Prime Structure FFI - Verification Executable
 *
 * This program performs quick verification of the FFI library functionality
 * and mathematical invariants. It's designed for rapid smoke testing and
 * continuous integration.
 */

#include <stdint.h>

#include <stdio.h>
#include <stdlib.h>

#include "uor_ffi.h"

#include <string.h>

#define VERSION "1.0.0"

/* ANSI color codes */
#define GREEN "\033[0;32m"
#define RED "\033[0;31m"
#define YELLOW "\033[0;33m"
#define BLUE "\033[0;34m"
#define RESET "\033[0m"

/* Verification levels */
typedef enum {
  VERIFY_QUICK    = 0,
  VERIFY_STANDARD = 1,
  VERIFY_THOROUGH = 2
} verify_level_t;

/* Verification results */
typedef struct {
  int checks_run;
  int checks_passed;
  int checks_failed;
  int warnings;
} verify_result_t;

/* Global result tracking */
static verify_result_t result = {0, 0, 0, 0};

/* Verification macros */
#define VERIFY(expr, msg)                       \
  do {                                          \
    result.checks_run++;                        \
    if (expr) {                                 \
      result.checks_passed++;                   \
      if (verbose)                              \
        printf(GREEN "  ✓ " RESET "%s\n", msg); \
    } else {                                    \
      result.checks_failed++;                   \
      printf(RED "  ✗ " RESET "%s\n", msg);     \
    }                                           \
  } while (0)

#define WARN_IF(expr, msg)                     \
  do {                                         \
    if (expr) {                                \
      result.warnings++;                       \
      printf(YELLOW "  ⚠ " RESET "%s\n", msg); \
    }                                          \
  } while (0)

/* Global options */
static int            verbose = 0;
static verify_level_t level   = VERIFY_STANDARD;

/* Verification Functions */

void verify_abi_compatibility(void) {
  printf("\n" BLUE "Verifying ABI Compatibility..." RESET "\n");

  uint32_t runtime_version = lean_uor_abi_version();
  uint32_t header_version  = UOR_FFI_ABI_VERSION;

  VERIFY(runtime_version == header_version, "ABI version matches header");

  WARN_IF(runtime_version > header_version,
          "Runtime ABI newer than header - may have new features");

  WARN_IF(runtime_version < header_version,
          "Runtime ABI older than header - some features may be missing");
}

void verify_constants(void) {
  printf("\n" BLUE "Verifying Prime Structure Constants..." RESET "\n");

  uint32_t pages    = lean_uor_pages();
  uint32_t bytes    = lean_uor_bytes();
  uint32_t rclasses = lean_uor_rclasses();

  VERIFY(pages == 48, "Pages = 48");
  VERIFY(bytes == 256, "Bytes = 256");
  VERIFY(rclasses == 96, "Resonance classes = 96");

  /* Verify mathematical relationships */
  VERIFY(pages * bytes == 12288, "Total elements = 12,288");
  VERIFY(rclasses * 8 == bytes * 3, "Compression ratio = 3/8");

  /* Verify power-of-2 structures */
  VERIFY(pages == 3 * 16, "Pages = 3 × 2^4");
  VERIFY(bytes == (1 << 8), "Bytes = 2^8");
  VERIFY(rclasses == 3 * 32, "R-classes = 3 × 2^5");
}

void verify_r96_classifier(void) {
  printf("\n" BLUE "Verifying R96 Classifier..." RESET "\n");

  /* Quick checks for standard level */
  VERIFY(lean_uor_r96_classify(0) == 0, "R96(0) = 0");
  VERIFY(lean_uor_r96_classify(95) == 95, "R96(95) = 95");
  VERIFY(lean_uor_r96_classify(96) == 0, "R96(96) = 0 (periodic)");
  VERIFY(lean_uor_r96_classify(255) == 63, "R96(255) = 63");

  if (level >= VERIFY_THOROUGH) {
    /* Check range validity for all inputs */
    int range_valid = 1;
    for (int i = 0; i < 256; i++) {
      uint8_t cls = lean_uor_r96_classify((uint8_t)i);
      if (cls >= 96) {
        range_valid = 0;
        break;
      }
    }
    VERIFY(range_valid, "All R96 outputs in range [0,95]");

    /* Check surjectivity */
    int class_seen[96] = {0};
    for (int i = 0; i < 256; i++) {
      uint8_t cls     = lean_uor_r96_classify((uint8_t)i);
      class_seen[cls] = 1;
    }

    int all_classes_produced = 1;
    for (int i = 0; i < 96; i++) {
      if (!class_seen[i]) {
        all_classes_produced = 0;
        break;
      }
    }
    VERIFY(all_classes_produced, "R96 is surjective (all classes produced)");
  }
}

void verify_phi_encoding(void) {
  printf("\n" BLUE "Verifying Φ Boundary Encoding..." RESET "\n");

  /* Test specific encoding */
  uint32_t code     = lean_uor_phi_encode(3, 16);
  uint32_t expected = (3 << 8) | 16;
  VERIFY(code == expected, "Encode(3,16) = 0x0310");

  /* Test decoding */
  VERIFY(lean_uor_phi_page(code) == 3, "Page extraction correct");
  VERIFY(lean_uor_phi_byte(code) == 16, "Byte extraction correct");

  /* Test modulo behavior */
  uint32_t code_mod = lean_uor_phi_encode(51, 100); /* 51 % 48 = 3 */
  VERIFY(lean_uor_phi_page(code_mod) == 3, "Page modulo 48 applied");

  if (level >= VERIFY_STANDARD) {
    /* Test round-trip for sample values */
    int round_trip_ok = 1;
    for (int p = 0; p < 48; p += 12) {
      for (int b = 0; b < 256; b += 64) {
        uint32_t enc = lean_uor_phi_encode(p, b);
        if (lean_uor_phi_page(enc) != p || lean_uor_phi_byte(enc) != b) {
          round_trip_ok = 0;
          break;
        }
      }
    }
    VERIFY(round_trip_ok, "Encode/decode round-trip successful");
  }
}

void verify_truth_conservation(void) {
  printf("\n" BLUE "Verifying Truth ≙ Conservation..." RESET "\n");

  /* Basic truth checks */
  VERIFY(lean_uor_truth_zero(0) == 1, "Truth(0) = true");
  VERIFY(lean_uor_truth_zero(1) == 0, "Truth(1) = false");
  VERIFY(lean_uor_truth_zero(0xFFFFFFFF) == 0, "Truth(MAX) = false");

  /* Additive conservation */
  VERIFY(lean_uor_truth_add(0, 0) == 1, "Truth(0+0) = true");
  VERIFY(lean_uor_truth_add(1, 0) == 0, "Truth(1+0) = false");
  VERIFY(lean_uor_truth_add(5, 10) == 0, "Truth(5+10) = false");

  /* Overflow wrapping */
  uint8_t overflow_result = lean_uor_truth_add(0xFFFFFFFF, 1);
  VERIFY(overflow_result == 1, "Truth(MAX+1) = true (wraps to 0)");
}

void verify_mathematical_invariants(void) {
  if (level < VERIFY_STANDARD)
    return;

  printf("\n" BLUE "Verifying Mathematical Invariants..." RESET "\n");

  uint32_t pages    = lean_uor_pages();
  uint32_t bytes    = lean_uor_bytes();
  uint32_t rclasses = lean_uor_rclasses();

  /* Unity constraint implications */
  VERIFY(pages == 48, "Unity constraint: 48 pages");

  /* Triple-cycle conservation */
  int total = pages * bytes;
  VERIFY(total == 12288, "12,288 total elements");
  VERIFY(total == 3 * 4096, "12,288 = 3 × 2^12");

  /* Compression bound */
  double ratio    = (double)rclasses / bytes;
  double expected = 3.0 / 8.0;
  double epsilon  = 0.0001;
  VERIFY(ratio > expected - epsilon && ratio < expected + epsilon,
         "Compression ratio = 3/8");

  /* Holographic principle check */
  VERIFY(total == pages * bytes, "Boundary = Pages × Bytes");
  VERIFY(rclasses < bytes, "Compression achieved (96 < 256)");
}

void print_summary(void) {
  printf("\n" YELLOW "═══════════════════════════════════════" RESET "\n");
  printf(YELLOW "Verification Summary" RESET "\n");
  printf(YELLOW "═══════════════════════════════════════" RESET "\n");

  printf("Checks run:    %d\n", result.checks_run);
  printf("Checks passed: " GREEN "%d" RESET "\n", result.checks_passed);
  printf("Checks failed: " RED "%d" RESET "\n", result.checks_failed);
  printf("Warnings:      " YELLOW "%d" RESET "\n", result.warnings);

  if (result.checks_failed == 0) {
    printf("\n" GREEN "✓ VERIFICATION SUCCESSFUL" RESET "\n");
  } else {
    printf("\n" RED "✗ VERIFICATION FAILED" RESET "\n");
  }
}

void print_usage(const char *prog_name) {
  printf("Usage: %s [OPTIONS]\n", prog_name);
  printf("\nOptions:\n");
  printf("  -h, --help       Show this help message\n");
  printf("  -v, --verbose    Show all verification checks\n");
  printf("  -q, --quick      Quick verification (minimal checks)\n");
  printf("  -t, --thorough   Thorough verification (all checks)\n");
  printf("  --version        Show version information\n");
  printf("\nVerification Levels:\n");
  printf("  Quick:    Basic functionality checks\n");
  printf("  Standard: Default level with core invariants (default)\n");
  printf("  Thorough: Complete verification including all values\n");
}

int main(int argc, char *argv[]) {
  /* Parse command line arguments */
  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
      print_usage(argv[0]);
      return 0;
    } else if (strcmp(argv[i], "-v") == 0 ||
               strcmp(argv[i], "--verbose") == 0) {
      verbose = 1;
    } else if (strcmp(argv[i], "-q") == 0 || strcmp(argv[i], "--quick") == 0) {
      level = VERIFY_QUICK;
    } else if (strcmp(argv[i], "-t") == 0 ||
               strcmp(argv[i], "--thorough") == 0) {
      level = VERIFY_THOROUGH;
    } else if (strcmp(argv[i], "--version") == 0) {
      printf("UOR FFI Verifier v%s\n", VERSION);
      return 0;
    } else {
      fprintf(stderr, "Unknown option: %s\n", argv[i]);
      print_usage(argv[0]);
      return 1;
    }
  }

  /* Print header */
  printf(YELLOW "═══════════════════════════════════════" RESET "\n");
  printf(YELLOW "UOR Prime Structure FFI Verification" RESET "\n");
  printf("Version: %s\n", VERSION);
  printf("Level: %s\n", level == VERIFY_QUICK      ? "Quick"
                        : level == VERIFY_THOROUGH ? "Thorough"
                                                   : "Standard");
  printf(YELLOW "═══════════════════════════════════════" RESET "\n");

  /* Initialize library */
  printf("\nInitializing UOR library...\n");
  lean_initialize_uor(0);

  /* Run verification checks */
  verify_abi_compatibility();
  verify_constants();
  verify_r96_classifier();
  verify_phi_encoding();
  verify_truth_conservation();
  verify_mathematical_invariants();

  /* Print summary */
  print_summary();

  /* Finalize library */
  printf("\nFinalizing UOR library...\n");
  lean_finalize_uor();

  /* Return exit code based on results */
  return result.checks_failed > 0 ? 1 : 0;
}