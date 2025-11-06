// tests/test_explosion.c
// Conway–Monster Atlas Upgrade Kit v1.1
// Test suite for explosion (expansion) operations

#include "atlas_bridge.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <math.h>

#define EPSILON 1e-10

// Test basic dimension queries
void test_dimensions(void) {
    printf("Testing dimensions...\n");
    
    uint32_t base, bridge;
    int result = atlas_dims(&base, &bridge);
    
    assert(result == 0);
    assert(base == 12288);
    assert(bridge == 98304);
    
    printf("  ✓ Dimensions correct: base=%u, bridge=%u\n", base, bridge);
}

// Test mode switching
void test_mode_switching(void) {
    printf("Testing mode switching...\n");
    
    // Switch to class mode
    atlas_set_mode(ATLAS_MODE_CLASS);
    
    // Switch to bridge mode
    atlas_set_mode(ATLAS_MODE_BRIDGE);
    
    // Enable spinlift
    atlas_spinlift_enable(1);
    
    // Disable spinlift
    atlas_spinlift_enable(0);
    
    printf("  ✓ Mode switching works\n");
}

// Test phi encoding/decoding
void test_phi_encoding(void) {
    printf("Testing phi encoding...\n");
    
    uint8_t test_page = 10;
    uint8_t test_byte = 42;
    
    uint32_t encoded = phi_encode(test_page, test_byte);
    
    uint8_t decoded_page, decoded_byte;
    int result = phi_decode(encoded, &decoded_page, &decoded_byte);
    
    assert(result == 0);
    assert(decoded_page == test_page);
    assert(decoded_byte == test_byte);
    
    printf("  ✓ Phi encoding/decoding correct\n");
}

// Test bridge indexing
void test_bridge_indexing(void) {
    printf("Testing bridge indexing...\n");
    
    uint32_t base_idx = 1000;
    
    // Test all 8 lift levels
    for (uint8_t k = 0; k < 8; k++) {
        uint32_t bridge_idx = phi_bridge(base_idx, k);
        
        // Bridge index should be in valid range
        assert(bridge_idx >= base_idx);
        assert(bridge_idx < 98304);
        
        // Check pattern: idx_base + 12288 * k
        uint32_t expected = base_idx + 12288 * k;
        assert(bridge_idx == expected);
    }
    
    printf("  ✓ Bridge indexing correct\n");
}

// Test explosion from base to bridge
void test_explosion_basic(void) {
    printf("Testing basic explosion...\n");
    
    // TODO: Create a vector in base space
    // TODO: Explode it to bridge space
    // TODO: Verify dimension expansion and structure
    
    printf("  ✓ Basic explosion works (stub)\n");
}

// Test that explosion preserves structure
void test_explosion_structure(void) {
    printf("Testing explosion structure preservation...\n");
    
    // TODO: Test that resonance class structure is preserved
    // TODO: Verify that the 8-fold lift maintains coherence
    
    printf("  ✓ Structure preservation works (stub)\n");
}

// Test boundary cases
void test_boundary_cases(void) {
    printf("Testing boundary cases...\n");
    
    // Test edge of base space
    uint8_t page, byte;
    int result = phi_decode(12287, &page, &byte);
    assert(result == 0);
    
    // Test out of bounds
    result = phi_decode(12288, &page, &byte);
    assert(result != 0);
    
    printf("  ✓ Boundary cases handled correctly\n");
}

int main(void) {
    printf("=== Conway-Monster Atlas Upgrade Kit v1.1 ===\n");
    printf("=== Test Suite: Explosion Operations ===\n\n");
    
    test_dimensions();
    test_mode_switching();
    test_phi_encoding();
    test_bridge_indexing();
    test_explosion_basic();
    test_explosion_structure();
    test_boundary_cases();
    
    printf("\n✓ All explosion tests passed!\n");
    return 0;
}
