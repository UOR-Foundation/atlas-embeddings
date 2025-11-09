# Atlas Core Serialization

This document describes the serialization capabilities added to `atlas-core` for CUDA consumption (Task AC2).

## Overview

The `serialize` module provides functions to precompute and serialize resonance metadata (class masks, mirror pairs, and phase windows) into formats suitable for upload to CUDA global or constant memory.

## Features

### Dual Format Support

1. **JSON Format** - Human-readable format for tooling and debugging
   - Pretty-printed output
   - Suitable for configuration files and inspection
   - Cross-platform compatibility

2. **Binary Format** - Compact format optimized for runtime
   - Little-endian encoding
   - Minimal overhead (114 bytes base)
   - Direct CUDA memory upload ready
   - Stable layout across versions

### Core API

```rust
use atlas_core::serialize::*;
use atlas_core::{AtlasClassMask, AtlasPhaseWindow};

// Create resonance data package
let mut data = ResonanceData::new();

// Add kernel-specific metadata
data.add_class_mask(AtlasClassMask::all());
data.add_phase_window(AtlasPhaseWindow { begin: 100, span: 50 });

// Serialize to JSON
let json = data.to_json()?;

// Serialize to binary
let binary = data.to_binary();

// Calculate size
let size = data.size_bytes();

// Validate integrity
data.validate()?;
```

### Helper Functions

C-compatible buffer packing:

```rust
// Pack mirror pairs
let mut mirror_buffer = vec![AtlasMirrorPair::new(0, 0); 48];
let count = pack_mirror_pairs(&mut mirror_buffer);

// Pack unity classes
let mut unity_buffer = vec![0u8; 10];
let unity_count = pack_unity_classes(&mut unity_buffer);
```

## Memory Constraints

All serialized data is designed to fit within CUDA constant memory limits (64KB typical):

| Configuration | Size | % of 64KB |
|--------------|------|-----------|
| Base data (48 pairs + 2 classes) | 114 bytes | 0.17% |
| + 10 class masks + 10 windows | 314 bytes | 0.48% |
| + 100 class masks + 100 windows | 2,114 bytes | 3.2% |

Even aggressive configurations use less than 5% of constant memory.

## Binary Layout

```
[mirror_pair_count: u32]
[mirror_pairs: [(u8, u8); mirror_pair_count]]
[unity_class_count: u32]
[unity_classes: [u8; unity_class_count]]
[class_mask_count: u32]
[class_masks: [(u64, u32); class_mask_count]]
[phase_window_count: u32]
[phase_windows: [(u32, u32); phase_window_count]]
```

## Testing

### Unit Tests (29 tests in `serialize.rs`)
- Serialization roundtrips (JSON and binary)
- Size calculations
- Data validation
- Conversion helpers
- Atlas data consistency

### Integration Tests (11 tests in `serialize_integration.rs`)
- Format stability
- CUDA memory constraints
- Cross-format consistency
- C-compatible packing
- Error handling

### Snapshot Tests (15 tests in `serialize_stability.rs`) - AC4
- Binary format stability snapshots
- JSON format stability snapshots
- Roundtrip correctness verification
- Backward compatibility with legacy formats
- Version marker for breaking change detection

The snapshot tests use `insta` to capture and compare serialized output across releases.
When snapshots fail, reviewers must:
1. Assess impact on CUDA runtime compatibility
2. Update version number if breaking changes occurred
3. Document the changes in release notes
4. Accept new snapshots with `cargo insta review`

### Example
Run the demonstration:
```bash
cargo run --package atlas-core --example serialize_demo
```

### Benchmarks
Run size measurements:
```bash
cargo bench --package atlas-core --bench serialize_bench
```

## Usage in CUDA Pipelines

1. **Precompute at Build Time**
   ```rust
   let data = ResonanceData::new();
   let binary = data.to_binary();
   std::fs::write("resonance_data.bin", binary)?;
   ```

2. **Package with Kernels**
   - Include binary in kernel artifact bundle
   - Ship alongside `.ptx` or `.cubin` files

3. **Upload to Device**
   ```cuda
   // Read binary data
   const uint8_t* resonance_data = load_resonance_data();
   
   // Upload to constant memory
   cudaMemcpyToSymbol(device_resonance_data, resonance_data, size);
   ```

4. **Use in Kernels**
   ```cuda
   __constant__ ResonanceMetadata metadata;
   
   __global__ void kernel() {
       // Access precomputed data
       uint8_t mirror = metadata.mirror_pairs[class_id];
   }
   ```

## Validation

All serialized data undergoes validation:
- Mirror pairs are symmetric and complete (all 96 classes)
- Unity classes are valid (exactly 2 classes)
- Phase windows are within mod 768 range
- Class masks properly formed

## Stability Guarantees

- Binary format uses stable layout
- Test suite includes format stability checks
- Breaking changes require version bump
- Roundtrip tests ensure consistency

## Performance

Benchmarks show minimal overhead:
- JSON serialization: ~4.3 μs
- Binary serialization: ~278 ns
- JSON deserialization: ~4.0 μs
- Binary deserialization: ~115 ns

Binary format is ~15x faster and ~24x smaller than JSON.

## Launch-Time Validation APIs (AC3)

### Overview

The `LaunchValidationData` structure provides precomputed lookup tables for efficient launch-time validation of Atlas invariants. These APIs enable O(1) checks for:
- Unity class membership
- Mirror pair lookups
- Phase window validation
- Class mask conflicts

### Creating Validation Data

```rust
use atlas_core::LaunchValidationData;

// Create validation data (precompute once)
let validation_data = LaunchValidationData::new();

// Query at launch time
assert!(validation_data.is_unity_class(47)); // Fast O(1) lookup
let mirror = validation_data.get_mirror(10); // O(1) lookup
assert_eq!(mirror, Some(85));
```

### Memory Footprint

`LaunchValidationData` uses exactly 112 bytes:
- Unity flags: 12 bytes (96 bits, one per class)
- Mirror table: 96 bytes (one byte per class)
- Total: 108 bytes + 4 bytes padding = 112 bytes

This fits easily in CUDA constant memory alongside other kernel metadata.

### API Reference

#### `is_unity_class(class_id: u8) -> bool`
Check if a class is in the unity set with O(1) lookup.

```rust
if validation_data.is_unity_class(class_id) {
    // Handle unity class
}
```

#### `get_mirror(class_id: u8) -> Option<u8>`
Get the mirror of a class with O(1) lookup. Returns `None` for invalid class IDs.

```rust
if let Some(mirror) = validation_data.get_mirror(class_id) {
    // Use mirror class
}
```

#### `are_mirror_pairs(classes: &[u8]) -> bool`
Check if all classes in a set form valid mirror pairs. A kernel is "mirror-safe" if all its classes appear with their mirrors.

```rust
let kernel_classes = [10, 85, 20, 75];
if validation_data.are_mirror_pairs(&kernel_classes) {
    // Kernel is mirror-safe
}
```

#### `is_phase_valid(phase: u32, window: &AtlasPhaseWindow) -> bool`
Validate that a phase is within a phase window, handling wrapping at mod 768.

```rust
let window = AtlasPhaseWindow { begin: 100, span: 50 };
if validation_data.is_phase_valid(current_phase, &window) {
    // Phase is valid
}
```

#### `masks_conflict(mask_a: &AtlasClassMask, mask_b: &AtlasClassMask) -> bool`
Check if two class masks share any classes, indicating potential scheduling conflicts.

```rust
if validation_data.masks_conflict(&kernel_mask, &active_mask) {
    // Schedule conflict detected
}
```

### Integration with Runtime

The runtime components should use these APIs during launch validation:

1. **Pre-Launch Phase Check**:
```rust
let validation_data = LaunchValidationData::new();
if !validation_data.is_phase_valid(current_phase, &kernel.phase_window) {
    return Err(RuntimeError::PhaseWindowIncompatible);
}
```

2. **Class Mask Conflict Detection**:
```rust
if validation_data.masks_conflict(&kernel.class_mask, &scheduler.active_classes()) {
    return ScheduleDecision::Serialize;
}
```

3. **Mirror Safety Verification**:
```rust
if kernel.mirror_safe {
    assert!(validation_data.are_mirror_pairs(&kernel.classes));
}
```

4. **Unity Neutrality Pre-Check**:
```rust
if kernel.unity_neutral {
    for &class in &kernel.classes {
        if validation_data.is_unity_class(class) {
            // Enable unity neutrality tracking
        }
    }
}
```

### Including in Serialized Data

Validation data can optionally be included in serialized resonance packages:

```rust
// Create with validation data
let data = ResonanceData::with_validation();

// Or add to existing data
let mut data = ResonanceData::new();
data.add_validation_data();

// Serialize (validation data included)
let binary = data.to_binary();
```

The binary format remains backward compatible—older readers will skip the validation data if present, and newer readers will handle its absence gracefully.

### C ABI for CUDA Integration

C-compatible functions are provided for device-side validation:

```c
// Create validation data
LaunchValidationData* data = launch_validation_data_new();

// Check unity class
bool is_unity = launch_validation_is_unity(data, class_id);

// Get mirror
uint8_t mirror = launch_validation_get_mirror(data, class_id);

// Validate phase
bool valid = launch_validation_is_phase_valid(data, phase, &window);

// Check mask conflicts
bool conflict = launch_validation_masks_conflict(data, &mask_a, &mask_b);

// Free
launch_validation_data_free(data);
```

### Performance Characteristics

All validation operations are O(1):
- Unity checks: Single bit test
- Mirror lookups: Array index
- Phase validation: Arithmetic comparison
- Mask conflicts: Bitwise AND

This makes them suitable for high-frequency launch-time checks without performance degradation.
