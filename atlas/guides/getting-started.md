---
layout: default
title: Getting Started
sidebar: guides
---

# Getting Started with UOR Prime Structure FFI

Welcome to the UOR Prime Structure FFI - a multi-language implementation of the 12,288-element holographic mathematical framework.

## What is UOR Prime Structure?

UOR Prime Structure is a mathematically verified framework that implements:

- **12,288-element structure** (48 pages × 256 bytes) representing fundamental mathematical objects
- **R96 resonance classifier** that maps 256 byte values to 96 resonance classes (3/8 compression ratio)
- **Φ boundary encoding** for efficient coordinate packing and retrieval
- **Truth ≙ conservation** budget semantics based on verified mathematical principles

The implementation is formally verified in Lean 4 and provides FFI bindings for C, Go, Rust, Python, and Node.js.

## Quick Installation

Choose your preferred language and follow the installation steps:

### Go
```bash
go get github.com/atlas-12288/uor
```

### Python
```bash
pip install uor-prime-structure
```

### Rust
```bash
cargo add uor-prime-structure
```

### Node.js
```bash
npm install uor-prime-structure
```

### C
```bash
# Build from source
git clone https://github.com/atlas-12288/uor-prime-structure
cd uor-prime-structure
make install
```

For detailed installation instructions, see the [Installation Guide](installation).

## First Example

Here's a simple example that demonstrates the core functionality in multiple languages:

### Go
```go
package main

import (
    "fmt"
    uor "github.com/atlas-12288/uor"
)

func main() {
    // Initialize the UOR system
    uor.Initialize()
    defer uor.Finalize()
    
    // Get basic constants
    fmt.Printf("Pages: %d\n", uor.GetPages())     // 48
    fmt.Printf("Bytes: %d\n", uor.GetBytes())     // 256
    fmt.Printf("Classes: %d\n", uor.GetRClasses()) // 96
    
    // Classify a byte using R96 resonance classifier
    b := byte(255)
    class := uor.R96Classify(b)
    fmt.Printf("R96(%d) = %d\n", b, class)
    
    // Use Φ boundary encoding
    page, byteVal := byte(3), byte(16)
    encoded := uor.PhiEncode(page, byteVal)
    fmt.Printf("Φ-encode(%d, %d) = %d\n", page, byteVal, encoded)
    
    // Extract coordinates back
    extractedPage := uor.PhiPage(encoded)
    extractedByte := uor.PhiByte(encoded)
    fmt.Printf("Φ-decode(%d) = (%d, %d)\n", encoded, extractedPage, extractedByte)
}
```

### Python
```python
import uor

def main():
    # Initialize the UOR system
    uor.initialize()
    
    try:
        # Get basic constants
        print(f"Pages: {uor.get_pages()}")     # 48
        print(f"Bytes: {uor.get_bytes()}")     # 256
        print(f"Classes: {uor.get_rclasses()}") # 96
        
        # Classify a byte using R96 resonance classifier
        b = 255
        class_val = uor.r96_classify(b)
        print(f"R96({b}) = {class_val}")
        
        # Use Φ boundary encoding
        page, byte_val = 3, 16
        encoded = uor.phi_encode(page, byte_val)
        print(f"Φ-encode({page}, {byte_val}) = {encoded}")
        
        # Extract coordinates back
        extracted_page = uor.phi_page(encoded)
        extracted_byte = uor.phi_byte(encoded)
        print(f"Φ-decode({encoded}) = ({extracted_page}, {extracted_byte})")
        
    finally:
        uor.finalize()

if __name__ == "__main__":
    main()
```

### Rust
```rust
use uor_prime_structure as uor;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize the UOR system
    uor::initialize()?;
    
    // Get basic constants
    println!("Pages: {}", uor::get_pages());     // 48
    println!("Bytes: {}", uor::get_bytes());     // 256
    println!("Classes: {}", uor::get_rclasses()); // 96
    
    // Classify a byte using R96 resonance classifier
    let b = 255u8;
    let class = uor::r96_classify(b)?;
    println!("R96({}) = {}", b, class);
    
    // Use Φ boundary encoding
    let (page, byte_val) = (3u8, 16u8);
    let encoded = uor::phi_encode(page, byte_val)?;
    println!("Φ-encode({}, {}) = {}", page, byte_val, encoded);
    
    // Extract coordinates back
    let extracted_page = uor::phi_page(encoded)?;
    let extracted_byte = uor::phi_byte(encoded)?;
    println!("Φ-decode({}) = ({}, {})", encoded, extracted_page, extracted_byte);
    
    uor::finalize();
    Ok(())
}
```

### Node.js
```javascript
const uor = require('uor-prime-structure');

async function main() {
    try {
        // Initialize the UOR system
        await uor.initialize();
        
        // Get basic constants
        console.log(`Pages: ${uor.getPages()}`);     // 48
        console.log(`Bytes: ${uor.getBytes()}`);     // 256
        console.log(`Classes: ${uor.getRClasses()}`); // 96
        
        // Classify a byte using R96 resonance classifier
        const b = 255;
        const classVal = uor.r96Classify(b);
        console.log(`R96(${b}) = ${classVal}`);
        
        // Use Φ boundary encoding
        const [page, byteVal] = [3, 16];
        const encoded = uor.phiEncode(page, byteVal);
        console.log(`Φ-encode(${page}, ${byteVal}) = ${encoded}`);
        
        // Extract coordinates back
        const extractedPage = uor.phiPage(encoded);
        const extractedByte = uor.phiByte(encoded);
        console.log(`Φ-decode(${encoded}) = (${extractedPage}, ${extractedByte})`);
        
    } finally {
        uor.finalize();
    }
}

main().catch(console.error);
```

### C
```c
#include <stdio.h>
#include "uor_ffi.h"

int main() {
    // Initialize the UOR system
    if (lean_uor_initialize() != 0) {
        fprintf(stderr, "Failed to initialize UOR\n");
        return 1;
    }
    
    // Get basic constants
    printf("Pages: %u\n", lean_uor_pages());     // 48
    printf("Bytes: %u\n", lean_uor_bytes());     // 256
    printf("Classes: %u\n", lean_uor_rclasses()); // 96
    
    // Classify a byte using R96 resonance classifier
    uint8_t b = 255;
    uint8_t class = lean_uor_r96_classify(b);
    printf("R96(%u) = %u\n", b, class);
    
    // Use Φ boundary encoding
    uint8_t page = 3, byte_val = 16;
    uint32_t encoded = lean_uor_phi_encode(page, byte_val);
    printf("Φ-encode(%u, %u) = %u\n", page, byte_val, encoded);
    
    // Extract coordinates back
    uint8_t extracted_page = lean_uor_phi_page(encoded);
    uint8_t extracted_byte = lean_uor_phi_byte(encoded);
    printf("Φ-decode(%u) = (%u, %u)\n", encoded, extracted_page, extracted_byte);
    
    // Clean up
    lean_uor_finalize();
    return 0;
}
```

## Expected Output

All examples should produce output similar to:

```
Pages: 48
Bytes: 256
Classes: 96
R96(255) = 47
Φ-encode(3, 16) = 784
Φ-decode(784) = (3, 16)
```

## Key Concepts

### 1. The 48×256 Structure
The core structure consists of 48 pages, each containing 256 bytes, forming a 12,288-element mathematical object with verified properties.

### 2. R96 Resonance Classification
The R96 classifier maps all 256 possible byte values to exactly 96 resonance classes, achieving a 3/8 compression ratio that is mathematically optimal for this structure.

### 3. Φ Boundary Encoding
The Φ (Phi) encoding system provides efficient coordinate packing, allowing page and byte coordinates to be stored in a single 32-bit value while maintaining fast extraction.

### 4. Truth ≙ Conservation
The truth functions implement conservation semantics where "truth" corresponds to zero budget, based on the verified mathematical principle that α₄α₅ = 1.

## Next Steps

- **[Installation Guide](installation)** - Detailed setup instructions for all platforms
- **[Architecture Overview](architecture)** - Understanding the system design
- **[Basic Examples](../examples/basic)** - More comprehensive examples
- **[API Reference](../api/)** - Complete function documentation
- **[Best Practices](best-practices)** - Recommended usage patterns

## Mathematical Background

For those interested in the underlying mathematics, the UOR Prime Structure is built on:

- **Unity Constraint**: α₄α₅ = 1 creating fundamental symmetries
- **96 Resonance Classes**: Exactly 96 distinct values from 8-bit patterns
- **Conservation Laws**: Triple-cycle invariant with sum 687.110133...
- **Holographic Duality**: Bulk↔boundary correspondence via master isomorphism Φ

The implementation is formally verified in Lean 4, ensuring mathematical correctness and consistency across all language bindings.

See the [Mathematics Guide](mathematics) for detailed mathematical context and proofs.