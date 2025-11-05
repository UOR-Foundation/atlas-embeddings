// atlas_core/src/atlas_bridge.c
// Conway–Monster Atlas Upgrade Kit v1.1
// Main bridge implementation for Atlas operations

#include "../include/atlas_bridge.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

// Internal state
static int current_mode = ATLAS_MODE_CLASS;
static int spinlift_enabled = 0;

// Base and bridge dimensions
#define BASE_DIM 12288
#define BRIDGE_DIM 98304

// Sizing functions
int atlas_dims(uint32_t* base, uint32_t* bridge) {
    if (base) *base = BASE_DIM;
    if (bridge) *bridge = BRIDGE_DIM;
    return 0;
}

void atlas_set_mode(int mode) {
    if (mode == ATLAS_MODE_CLASS || mode == ATLAS_MODE_BRIDGE) {
        current_mode = mode;
    }
}

void atlas_spinlift_enable(int on) {
    if (current_mode == ATLAS_MODE_BRIDGE) {
        spinlift_enabled = on ? 1 : 0;
    }
}

// Indexing functions
uint32_t phi_encode(uint8_t page, uint8_t byte) {
    // Encode (page, byte) into linear index 0..12287
    // TODO: Implement proper encoding based on Atlas structure
    if (page >= 48 || byte != byte) { // Basic validation
        return 0;
    }
    return (uint32_t)page * 256 + byte;
}

int phi_decode(uint32_t idx, uint8_t* page, uint8_t* byte) {
    // Decode linear index back to (page, byte)
    // TODO: Implement proper decoding
    if (idx >= BASE_DIM) {
        return -1;
    }
    if (page) *page = (uint8_t)(idx / 256);
    if (byte) *byte = (uint8_t)(idx % 256);
    return 0;
}

// NOTE: Group actions, projectors, and diagnostics are implemented
// in their respective source files (e_group.c, co1_gates.c, projectors.c, diagnostics.c)
// and declared in the header file.
