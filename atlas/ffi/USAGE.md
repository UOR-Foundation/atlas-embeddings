# UOR FFI Usage Guide

## Overview

The UOR FFI provides cross-language bindings for the Prime Structure mathematical framework. It offers two implementation modes:

1. **Pure C Mode** - A standalone C implementation with no dependencies
2. **Lean Runtime Mode** - Uses the verified Lean implementation (requires C++ runtime)

## Quick Start

### Pure C (Recommended)

```c
#include "uor_ffi_hybrid.h"

int main() {
    uint32_t pages = UOR_PAGES();        // 48
    uint8_t cls = UOR_R96_CLASSIFY(100); // 4
    return 0;
}
```

Compile with:
```bash
gcc myapp.c -o myapp
```

### With Language Bindings

#### Python
```python
import uor

pages = uor.pages()                      # 48
cls = uor.r96_classify(100)              # 4
coord = uor.PhiCoordinate(3, 16)         # Φ(3,16)
```

#### Go
```go
import "github.com/atlas-12288/uor"

pages := uor.GetPages()                  // 48
cls := uor.R96Classify(100)              // 4
coord := uor.PhiCoordinate{3, 16}        // Φ(3,16)
```

#### Rust
```rust
use uor;

let pages = uor::pages();                // 48
let cls = uor::r96_classify(100);        // 4
let coord = uor::PhiCoordinate::new(3, 16); // Φ(3,16)
```

#### Node.js
```javascript
const uor = require('uor-ffi');

const pages = uor.getPages();            // 48
const cls = uor.r96Classify(100);        // 4
const coord = new uor.PhiCoordinate(3, 16); // Φ(3,16)
```

## API Reference

### Constants
- `PAGES` - Number of pages (48)
- `BYTES` - Bytes per page (256)
- `RCLASSES` - Resonance classes (96)
- `TOTAL_ELEMENTS` - Total elements (12,288)

### Functions

#### Structure Properties
- `pages()` - Get number of pages
- `bytes()` - Get bytes per page
- `rclasses()` - Get number of resonance classes

#### R96 Classification
- `r96_classify(byte)` - Classify byte to resonance class [0,95]

#### Phi Encoding
- `phi_encode(page, byte)` - Encode coordinates to 32-bit code
- `phi_page(code)` - Extract page from code
- `phi_byte(code)` - Extract byte from code

#### Truth Conservation
- `truth_zero(budget)` - Check if budget is zero (truth)
- `truth_add(a, b)` - Check if sum is zero (truth)

## Best Practices

### 1. Use Pure C Mode for Simplicity

The pure C implementation works everywhere without dependencies:

```c
// No runtime initialization needed
uint32_t result = UOR_PAGES();
```

### 2. Handle Modulo Operations

Page coordinates are automatically taken modulo 48:

```c
uint32_t code = UOR_PHI_ENCODE(51, 100); // 51 % 48 = 3
uint8_t page = UOR_PHI_PAGE(code);       // Returns 3
```

### 3. Verify Compression Ratio

The R96 classifier achieves 3/8 compression:

```c
double ratio = (double)UOR_RCLASSES() / UOR_BYTES(); // 0.375
```

### 4. Test Conservation Laws

Truth values represent conservation:

```c
if (UOR_TRUTH_ZERO(0)) {
    // Budget conserves (is zero)
}

if (UOR_TRUTH_ADD(0xFFFFFFFF, 1)) {
    // Overflow wraps to zero (truth)
}
```

## Implementation Modes

### Pure C Mode

**Pros:**
- No dependencies
- Easy compilation
- Cross-platform
- Header-only option

**Cons:**
- Not formally verified
- Manual sync with Lean

**When to use:**
- Development and testing
- Embedded systems
- Quick prototypes
- CI/CD pipelines

### Lean Runtime Mode

**Pros:**
- Formally verified
- Automatic updates
- Proof guarantees

**Cons:**
- Complex dependencies
- C++ ABI issues
- Larger binary size

**When to use:**
- Production systems requiring verification
- Research applications
- When correctness is critical

## Troubleshooting

### Linking Errors

If you get undefined symbols with Lean runtime:

1. Use pure C mode instead:
```c
// Don't define UOR_USE_LEAN_RUNTIME
#include "uor_ffi_hybrid.h"
```

2. Or use Docker for consistent environment:
```bash
docker build -f ffi/Dockerfile -t uor-ffi .
docker run --rm -v $(pwd):/workspace uor-ffi make test
```

### C++ Standard Library Issues

Lean uses libc++ while most systems use libstdc++. Solutions:

1. Use clang with libc++:
```bash
clang++ -stdlib=libc++ myapp.cpp -luor
```

2. Use the static bundle:
```bash
./create_bundle.sh
gcc myapp.c -luor_bundle -lstdc++ -lgmp -lpthread
```

### Performance Optimization

For maximum performance:

```c
// Batch operations
for (int i = 0; i < 256; i++) {
    classes[i] = UOR_R96_CLASSIFY(i);
}

// Use lookup tables for hot paths
static uint8_t r96_table[256];
static int initialized = 0;
if (!initialized) {
    for (int i = 0; i < 256; i++) {
        r96_table[i] = UOR_R96_CLASSIFY(i);
    }
    initialized = 1;
}
```

## Examples

### Complete Example

```c
#include <stdio.h>
#include "uor_ffi_hybrid.h"

int main() {
    // Initialize (no-op in pure C)
    UOR_INIT(0);
    
    // Display structure
    printf("Prime Structure: %u pages × %u bytes\n", 
           UOR_PAGES(), UOR_BYTES());
    printf("Compression: %u classes (%.1f%%)\n",
           UOR_RCLASSES(), 
           100.0 * UOR_RCLASSES() / UOR_BYTES());
    
    // Classify bytes
    for (int i = 0; i < 10; i++) {
        printf("R96(%d) = %u\n", i, UOR_R96_CLASSIFY(i));
    }
    
    // Encode coordinates
    uint32_t code = UOR_PHI_ENCODE(3, 16);
    printf("Φ(3,16) = 0x%04X\n", code);
    printf("Decode: (%u,%u)\n", 
           UOR_PHI_PAGE(code), UOR_PHI_BYTE(code));
    
    // Check conservation
    if (UOR_TRUTH_ZERO(0)) {
        printf("Zero conserves truth\n");
    }
    
    UOR_FINALIZE();
    return 0;
}
```

### Language-Specific Examples

See the `pkg/` directory for complete examples in:
- Go: `pkg/go/test/`
- Rust: `pkg/rust/src/lib.rs`
- Python: `pkg/python/test/`
- Node.js: `pkg/node/test/`

## Contributing

When adding new FFI functions:

1. Add to `ffi/c/uor_ffi.h`
2. Implement in `ffi/c/minimal_wrapper.c`
3. Export from Lean in `lean/UOR/FFI/CAPI.lean`
4. Update language bindings in `pkg/`
5. Add tests in each language
6. Update this documentation

## License

MIT License - See LICENSE file for details.