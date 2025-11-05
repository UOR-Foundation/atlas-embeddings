# C API Reference

## Header Files

### uor_ffi_hybrid.h

The hybrid header provides both Lean runtime and minimal C implementations.

## Constants

```c
#define UOR_PAGES 48      // Number of pages
#define UOR_BYTES 256     // Bytes per page  
#define UOR_RCLASSES 96   // Resonance classes
```

## Core Functions

### Structure Properties

#### `UOR_PAGES()`
```c
uint32_t UOR_PAGES(void);
```
Returns the number of pages in the structure (48).

#### `UOR_BYTES()`
```c
uint32_t UOR_BYTES(void);
```
Returns the number of bytes per page (256).

#### `UOR_RCLASSES()`
```c
uint32_t UOR_RCLASSES(void);
```
Returns the number of resonance classes (96).

### R96 Classification

#### `UOR_R96_CLASSIFY()`
```c
uint8_t UOR_R96_CLASSIFY(uint8_t b);
```
Classifies a byte value into its resonance class.

**Parameters:**
- `b`: Byte value to classify [0-255]

**Returns:** Resonance class [0-95]

### Phi Encoding

#### `UOR_PHI_ENCODE()`
```c
uint32_t UOR_PHI_ENCODE(uint8_t page, uint8_t byte);
```
Encodes page and byte coordinates into a single code.

**Parameters:**
- `page`: Page number [0-47]
- `byte`: Byte offset [0-255]

**Returns:** 32-bit encoded coordinate

#### `UOR_PHI_PAGE()`
```c
uint8_t UOR_PHI_PAGE(uint32_t code);
```
Extracts the page component from an encoded coordinate.

**Parameters:**
- `code`: Encoded coordinate

**Returns:** Page number [0-47]

#### `UOR_PHI_BYTE()`
```c
uint8_t UOR_PHI_BYTE(uint32_t code);
```
Extracts the byte component from an encoded coordinate.

**Parameters:**
- `code`: Encoded coordinate

**Returns:** Byte offset [0-255]

### Truth Functions

#### `UOR_TRUTH_ZERO()`
```c
uint8_t UOR_TRUTH_ZERO(int32_t budget);
```
Checks if a budget value represents truth (conservation at zero).

**Parameters:**
- `budget`: Value to check

**Returns:** 1 if budget is zero (truth), 0 otherwise

#### `UOR_TRUTH_ADD()`
```c
uint8_t UOR_TRUTH_ADD(int32_t a, int32_t b);
```
Checks if two values sum to conservation (zero).

**Parameters:**
- `a`: First value
- `b`: Second value

**Returns:** 1 if a + b = 0, 0 otherwise

## Compilation Modes

### Pure C Mode (Default)
```c
#include "uor_ffi_hybrid.h"
// Uses minimal C implementation
```

### Lean Runtime Mode
```c
#define UOR_USE_LEAN_RUNTIME
#include "uor_ffi_hybrid.h"
// Uses verified Lean implementation
```

## Example Usage

```c
#include <stdio.h>
#include "uor_ffi_hybrid.h"

int main() {
    // Initialize (only needed for Lean runtime)
    #ifdef UOR_USE_LEAN_RUNTIME
    UOR_INIT(0);
    #endif
    
    // Get structure properties
    printf("Pages: %u\n", UOR_PAGES());
    printf("Bytes per page: %u\n", UOR_BYTES());
    printf("Resonance classes: %u\n", UOR_RCLASSES());
    
    // Classify a byte
    uint8_t cls = UOR_R96_CLASSIFY(255);
    printf("R96(255) = %u\n", cls);
    
    // Encode and decode coordinates
    uint32_t code = UOR_PHI_ENCODE(3, 16);
    printf("Encoded: %u\n", code);
    printf("Page: %u\n", UOR_PHI_PAGE(code));
    printf("Byte: %u\n", UOR_PHI_BYTE(code));
    
    // Check conservation
    if (UOR_TRUTH_ZERO(0)) {
        printf("0 represents truth\n");
    }
    
    // Cleanup (only needed for Lean runtime)
    #ifdef UOR_USE_LEAN_RUNTIME
    UOR_FINALIZE();
    #endif
    
    return 0;
}
```

## Linking

### Pure C (Recommended)
```bash
gcc -o myapp myapp.c
```

### With Lean Runtime
```bash
gcc -o myapp myapp.c -L.lake/build/lib -lUOR -lLean -lstdc++ -lgmp
```