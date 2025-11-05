#include <stdio.h>

#include "uor_ffi.h"

int main(void) {
  printf("Initializing UOR...\n");
  lean_initialize_uor(0);

  printf("Calling UOR_PAGES...\n");
  uint32_t pages = lean_uor_pages();
  printf("Pages: %u\n", pages);

  printf("Done.\n");
  lean_finalize_uor();
  return 0;
}