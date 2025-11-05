---
layout: default
title: Basic Examples
sidebar: examples
---

# Basic Examples

This page provides simple examples demonstrating core UOR Prime Structure FFI functionality across all supported languages. These examples are perfect for getting started and understanding the basic API.

## Core Functions Demonstrated

1. **System Constants**: Getting pages (48), bytes (256), and R-classes (96)
2. **R96 Classification**: Converting byte values to resonance classes
3. **Φ Encoding/Decoding**: Coordinate packing and extraction
4. **Truth Functions**: Conservation budget semantics

## Complete Examples

### C Example

```c
#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include "uor_ffi.h"

int main() {
    // Initialize the UOR system
    if (lean_uor_initialize() != 0) {
        fprintf(stderr, "Failed to initialize UOR\n");
        return 1;
    }
    
    printf("UOR Prime Structure Basic Example\n");
    printf("=================================\n\n");
    
    // 1. System Constants
    printf("1. System Constants:\n");
    printf("   Pages: %u\n", lean_uor_pages());
    printf("   Bytes per page: %u\n", lean_uor_bytes());
    printf("   Resonance classes: %u\n", lean_uor_rclasses());
    printf("   ABI Version: %u\n\n", lean_uor_abi_version());
    
    // 2. R96 Resonance Classification
    printf("2. R96 Resonance Classification:\n");
    uint8_t test_bytes[] = {0, 1, 127, 128, 255};
    for (int i = 0; i < 5; i++) {
        uint8_t byte_val = test_bytes[i];
        uint8_t r96_class = lean_uor_r96_classify(byte_val);
        printf("   R96(%3u) = %2u\n", byte_val, r96_class);
        assert(r96_class < 96); // Verify valid range
    }
    printf("\n");
    
    // 3. Φ Boundary Encoding
    printf("3. Φ Boundary Encoding:\n");
    uint8_t test_coords[][2] = {% raw %}{{0, 0}, {3, 16}, {47, 255}, {12, 128}}{% endraw %};
    for (int i = 0; i < 4; i++) {
        uint8_t page = test_coords[i][0];
        uint8_t byte = test_coords[i][1];
        
        uint32_t encoded = lean_uor_phi_encode(page, byte);
        uint8_t decoded_page = lean_uor_phi_page(encoded);
        uint8_t decoded_byte = lean_uor_phi_byte(encoded);
        
        printf("   Φ-encode(%2u, %3u) = %5u\n", page, byte, encoded);
        printf("   Φ-decode(%5u) = (%2u, %3u)\n", encoded, decoded_page, decoded_byte);
        
        // Verify roundtrip
        assert(decoded_page == page);
        assert(decoded_byte == byte);
        printf("\n");
    }
    
    // 4. Truth ≙ Conservation
    printf("4. Truth ≙ Conservation:\n");
    int32_t budgets[] = {0, 1, -1, 42, -42};
    for (int i = 0; i < 5; i++) {
        int32_t budget = budgets[i];
        uint8_t is_truth = lean_uor_truth_zero(budget);
        printf("   Truth(%3d) = %s\n", budget, is_truth ? "true" : "false");
        assert((budget == 0) == (is_truth == 1)); // Verify logic
    }
    
    printf("\n   Addition conservation:\n");
    int32_t pairs[][2] = {% raw %}{{5, -5}, {0, 0}, {3, 7}, {-10, 10}}{% endraw %};
    for (int i = 0; i < 4; i++) {
        int32_t a = pairs[i][0], b = pairs[i][1];
        uint8_t conserved = lean_uor_truth_add(a, b);
        printf("   Truth(%3d + %3d) = %s\n", a, b, conserved ? "true" : "false");
    }
    
    printf("\nAll assertions passed! UOR FFI working correctly.\n");
    
    // Cleanup
    lean_uor_finalize();
    return 0;
}
```

**Expected Output:**
```
UOR Prime Structure Basic Example
=================================

1. System Constants:
   Pages: 48
   Bytes per page: 256
   Resonance classes: 96
   ABI Version: 1

2. R96 Resonance Classification:
   R96(  0) =  0
   R96(  1) =  1
   R96(127) = 63
   R96(128) = 64
   R96(255) = 47

3. Φ Boundary Encoding:
   Φ-encode( 0,   0) =     0
   Φ-decode(    0) = ( 0,   0)

   Φ-encode( 3,  16) =   784
   Φ-decode(  784) = ( 3,  16)

   Φ-encode(47, 255) = 12287
   Φ-decode(12287) = (47, 255)

   Φ-encode(12, 128) =  3200
   Φ-decode( 3200) = (12, 128)

4. Truth ≙ Conservation:
   Truth(  0) = true
   Truth(  1) = false
   Truth( -1) = false
   Truth( 42) = false
   Truth(-42) = false

   Addition conservation:
   Truth(  5 +  -5) = true
   Truth(  0 +   0) = true
   Truth(  3 +   7) = false
   Truth(-10 +  10) = true

All assertions passed! UOR FFI working correctly.
```

### Go Example

```go
package main

import (
	"fmt"
	uor "github.com/atlas-12288/uor-prime-structure"
)

func main() {
	// Initialize the UOR system
	if err := uor.Initialize(); err != nil {
		fmt.Printf("Failed to initialize UOR: %v\n", err)
		return
	}
	defer uor.Finalize()
	
	fmt.Println("UOR Prime Structure Basic Example")
	fmt.Println("=================================")
	fmt.Println()
	
	// 1. System Constants
	fmt.Println("1. System Constants:")
	fmt.Printf("   Pages: %d\n", uor.GetPages())
	fmt.Printf("   Bytes per page: %d\n", uor.GetBytes())
	fmt.Printf("   Resonance classes: %d\n", uor.GetRClasses())
	fmt.Printf("   ABI Version: %d\n\n", uor.GetABIVersion())
	
	// 2. R96 Resonance Classification
	fmt.Println("2. R96 Resonance Classification:")
	testBytes := []byte{0, 1, 127, 128, 255}
	for _, b := range testBytes {
		r96Class := uor.R96Classify(b)
		fmt.Printf("   R96(%3d) = %2d\n", b, r96Class)
		if r96Class >= 96 {
			panic(fmt.Sprintf("Invalid R96 class: %d", r96Class))
		}
	}
	fmt.Println()
	
	// 3. Φ Boundary Encoding
	fmt.Println("3. Φ Boundary Encoding:")
	testCoords := [][]byte{% raw %}{{0, 0}, {3, 16}, {47, 255}, {12, 128}}{% endraw %}
	for _, coord := range testCoords {
		page, byteVal := coord[0], coord[1]
		
		encoded := uor.PhiEncode(page, byteVal)
		decodedPage := uor.PhiPage(encoded)
		decodedByte := uor.PhiByte(encoded)
		
		fmt.Printf("   Φ-encode(%2d, %3d) = %5d\n", page, byteVal, encoded)
		fmt.Printf("   Φ-decode(%5d) = (%2d, %3d)\n", encoded, decodedPage, decodedByte)
		
		// Verify roundtrip
		if decodedPage != page || decodedByte != byteVal {
			panic(fmt.Sprintf("Roundtrip failed: (%d, %d) -> %d -> (%d, %d)", 
				page, byteVal, encoded, decodedPage, decodedByte))
		}
		fmt.Println()
	}
	
	// 4. Truth ≙ Conservation
	fmt.Println("4. Truth ≙ Conservation:")
	budgets := []int32{0, 1, -1, 42, -42}
	for _, budget := range budgets {
		isTruth := uor.TruthZero(budget)
		fmt.Printf("   Truth(%3d) = %t\n", budget, isTruth)
		// Verify logic
		if (budget == 0) != isTruth {
			panic(fmt.Sprintf("Truth logic failed for budget %d", budget))
		}
	}
	
	fmt.Println("\n   Addition conservation:")
	pairs := [][]int32{% raw %}{{5, -5}, {0, 0}, {3, 7}, {-10, 10}}{% endraw %}
	for _, pair := range pairs {
		a, b := pair[0], pair[1]
		conserved := uor.TruthAdd(a, b)
		fmt.Printf("   Truth(%3d + %3d) = %t\n", a, b, conserved)
	}
	
	fmt.Println("\nAll checks passed! UOR FFI working correctly.")
}
```

### Python Example

```python
import uor

def main():
    # Initialize the UOR system
    uor.initialize()
    
    try:
        print("UOR Prime Structure Basic Example")
        print("=================================")
        print()
        
        # 1. System Constants
        print("1. System Constants:")
        print(f"   Pages: {uor.get_pages()}")
        print(f"   Bytes per page: {uor.get_bytes()}")
        print(f"   Resonance classes: {uor.get_rclasses()}")
        print(f"   ABI Version: {uor.get_abi_version()}")
        print()
        
        # 2. R96 Resonance Classification
        print("2. R96 Resonance Classification:")
        test_bytes = [0, 1, 127, 128, 255]
        for byte_val in test_bytes:
            r96_class = uor.r96_classify(byte_val)
            print(f"   R96({byte_val:3d}) = {r96_class:2d}")
            assert r96_class < 96, f"Invalid R96 class: {r96_class}"
        print()
        
        # 3. Φ Boundary Encoding
        print("3. Φ Boundary Encoding:")
        test_coords = [(0, 0), (3, 16), (47, 255), (12, 128)]
        for page, byte_val in test_coords:
            encoded = uor.phi_encode(page, byte_val)
            decoded_page = uor.phi_page(encoded)
            decoded_byte = uor.phi_byte(encoded)
            
            print(f"   Φ-encode({page:2d}, {byte_val:3d}) = {encoded:5d}")
            print(f"   Φ-decode({encoded:5d}) = ({decoded_page:2d}, {decoded_byte:3d})")
            
            # Verify roundtrip
            assert decoded_page == page and decoded_byte == byte_val, \
                f"Roundtrip failed: ({page}, {byte_val}) -> {encoded} -> ({decoded_page}, {decoded_byte})"
            print()
        
        # 4. Truth ≙ Conservation
        print("4. Truth ≙ Conservation:")
        budgets = [0, 1, -1, 42, -42]
        for budget in budgets:
            is_truth = uor.truth_zero(budget)
            print(f"   Truth({budget:3d}) = {is_truth}")
            # Verify logic
            assert (budget == 0) == is_truth, f"Truth logic failed for budget {budget}"
        
        print("\n   Addition conservation:")
        pairs = [(5, -5), (0, 0), (3, 7), (-10, 10)]
        for a, b in pairs:
            conserved = uor.truth_add(a, b)
            print(f"   Truth({a:3d} + {b:3d}) = {conserved}")
        
        print("\nAll checks passed! UOR FFI working correctly.")
        
    finally:
        uor.finalize()

if __name__ == "__main__":
    main()
```

### Rust Example

```rust
use uor_prime_structure as uor;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    // Initialize the UOR system
    uor::initialize()?;
    
    println!("UOR Prime Structure Basic Example");
    println!("=================================\n");
    
    // 1. System Constants
    println!("1. System Constants:");
    println!("   Pages: {}", uor::get_pages());
    println!("   Bytes per page: {}", uor::get_bytes());
    println!("   Resonance classes: {}", uor::get_rclasses());
    println!("   ABI Version: {}\n", uor::get_abi_version());
    
    // 2. R96 Resonance Classification
    println!("2. R96 Resonance Classification:");
    let test_bytes = [0u8, 1, 127, 128, 255];
    for &byte_val in &test_bytes {
        let r96_class = uor::r96_classify(byte_val)?;
        println!("   R96({:3}) = {:2}", byte_val, r96_class);
        assert!(r96_class < 96, "Invalid R96 class: {}", r96_class);
    }
    println!();
    
    // 3. Φ Boundary Encoding
    println!("3. Φ Boundary Encoding:");
    let test_coords = [(0u8, 0u8), (3, 16), (47, 255), (12, 128)];
    for (page, byte_val) in test_coords {
        let encoded = uor::phi_encode(page, byte_val)?;
        let decoded_page = uor::phi_page(encoded)?;
        let decoded_byte = uor::phi_byte(encoded)?;
        
        println!("   Φ-encode({:2}, {:3}) = {:5}", page, byte_val, encoded);
        println!("   Φ-decode({:5}) = ({:2}, {:3})", encoded, decoded_page, decoded_byte);
        
        // Verify roundtrip
        assert_eq!(decoded_page, page, "Page roundtrip failed");
        assert_eq!(decoded_byte, byte_val, "Byte roundtrip failed");
        println!();
    }
    
    // 4. Truth ≙ Conservation
    println!("4. Truth ≙ Conservation:");
    let budgets = [0i32, 1, -1, 42, -42];
    for budget in budgets {
        let is_truth = uor::truth_zero(budget)?;
        println!("   Truth({:3}) = {}", budget, is_truth);
        // Verify logic
        assert_eq!((budget == 0), is_truth, "Truth logic failed for budget {}", budget);
    }
    
    println!("\n   Addition conservation:");
    let pairs = [(5i32, -5i32), (0, 0), (3, 7), (-10, 10)];
    for (a, b) in pairs {
        let conserved = uor::truth_add(a, b)?;
        println!("   Truth({:3} + {:3}) = {}", a, b, conserved);
    }
    
    println!("\nAll checks passed! UOR FFI working correctly.");
    
    uor::finalize();
    Ok(())
}
```

### Node.js Example

```javascript
const uor = require('uor-prime-structure');

async function main() {
    try {
        // Initialize the UOR system
        await uor.initialize();
        
        console.log('UOR Prime Structure Basic Example');
        console.log('=================================\n');
        
        // 1. System Constants
        console.log('1. System Constants:');
        console.log(`   Pages: ${uor.getPages()}`);
        console.log(`   Bytes per page: ${uor.getBytes()}`);
        console.log(`   Resonance classes: ${uor.getRClasses()}`);
        console.log(`   ABI Version: ${uor.getABIVersion()}\n`);
        
        // 2. R96 Resonance Classification
        console.log('2. R96 Resonance Classification:');
        const testBytes = [0, 1, 127, 128, 255];
        for (const byteVal of testBytes) {
            const r96Class = uor.r96Classify(byteVal);
            console.log(`   R96(${byteVal.toString().padStart(3)}) = ${r96Class.toString().padStart(2)}`);
            console.assert(r96Class < 96, `Invalid R96 class: ${r96Class}`);
        }
        console.log();
        
        // 3. Φ Boundary Encoding
        console.log('3. Φ Boundary Encoding:');
        const testCoords = [[0, 0], [3, 16], [47, 255], [12, 128]];
        for (const [page, byteVal] of testCoords) {
            const encoded = uor.phiEncode(page, byteVal);
            const decodedPage = uor.phiPage(encoded);
            const decodedByte = uor.phiByte(encoded);
            
            console.log(`   Φ-encode(${page.toString().padStart(2)}, ${byteVal.toString().padStart(3)}) = ${encoded.toString().padStart(5)}`);
            console.log(`   Φ-decode(${encoded.toString().padStart(5)}) = (${decodedPage.toString().padStart(2)}, ${decodedByte.toString().padStart(3)})`);
            
            // Verify roundtrip
            console.assert(decodedPage === page && decodedByte === byteVal, 
                `Roundtrip failed: (${page}, ${byteVal}) -> ${encoded} -> (${decodedPage}, ${decodedByte})`);
            console.log();
        }
        
        // 4. Truth ≙ Conservation
        console.log('4. Truth ≙ Conservation:');
        const budgets = [0, 1, -1, 42, -42];
        for (const budget of budgets) {
            const isTruth = uor.truthZero(budget);
            console.log(`   Truth(${budget.toString().padStart(3)}) = ${isTruth}`);
            // Verify logic
            console.assert((budget === 0) === isTruth, `Truth logic failed for budget ${budget}`);
        }
        
        console.log('\n   Addition conservation:');
        const pairs = [[5, -5], [0, 0], [3, 7], [-10, 10]];
        for (const [a, b] of pairs) {
            const conserved = uor.truthAdd(a, b);
            console.log(`   Truth(${a.toString().padStart(3)} + ${b.toString().padStart(3)}) = ${conserved}`);
        }
        
        console.log('\nAll checks passed! UOR FFI working correctly.');
        
    } catch (error) {
        console.error('Error:', error);
        process.exit(1);
    } finally {
        uor.finalize();
    }
}

main().catch(console.error);
```

## Key Observations

### Mathematical Properties Verified

1. **Constant Values**: All languages return identical system constants
2. **R96 Range**: All classified values are in [0, 95] range  
3. **Φ Roundtrip**: Encoding and decoding preserves coordinates
4. **Truth Semantics**: Zero budget equals truth, conservation holds for sum = 0

### Language Differences

- **C**: Direct FFI calls, manual memory management
- **Go**: Clean defer patterns, built-in error handling
- **Python**: Exception-based error handling, clean syntax
- **Rust**: Result types for safety, comprehensive error handling
- **Node.js**: Async/await patterns, Promise-based API

### Performance Notes

For these simple operations:
- **Pure implementations** are 10-15x faster than FFI calls
- **FFI calls** provide mathematical verification guarantees
- **Batch operations** significantly improve FFI performance

## Next Steps

- Explore [language-specific examples](.) for advanced usage patterns
- Review [performance benchmarks](../guides/benchmarks) for optimization strategies
- Study [best practices](../guides/best-practices) for production usage
- Check [API documentation](../api/) for complete function references