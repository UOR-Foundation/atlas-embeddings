//! Demonstration of launch-time validation APIs (AC3)
//!
//! Run with:
//! ```bash
//! cargo run --example launch_validation_demo
//! ```

use atlas_core::{unity_positions, AtlasClassMask, AtlasPhaseWindow, LaunchValidationData, PHASE_MODULUS};

fn main() {
    println!("=== Launch-Time Validation API Demo ===\n");

    // Create validation data (typically precomputed once)
    let validation_data = LaunchValidationData::new();
    println!(
        "✓ Created validation data ({} bytes)",
        LaunchValidationData::size_bytes()
    );

    // Example 1: Unity class checks
    println!("\n--- Unity Class Validation ---");
    let unity_classes = unity_positions();
    println!(
        "Unity classes in Atlas: {:?}",
        unity_classes.iter().map(|c| c.as_u8()).collect::<Vec<_>>()
    );

    for class in unity_classes {
        let class_id = class.as_u8();
        assert!(validation_data.is_unity_class(class_id));
        println!("  Class {} is unity: ✓", class_id);
    }

    // Example 2: Mirror pair lookups
    println!("\n--- Mirror Pair Lookups ---");
    let test_classes = [0, 10, 47, 95];
    for &class_id in &test_classes {
        if let Some(mirror) = validation_data.get_mirror(class_id) {
            println!("  Class {} ↔ Class {} (mirror)", class_id, mirror);
            // Verify symmetry
            assert_eq!(validation_data.get_mirror(mirror), Some(class_id));
        }
    }

    // Example 3: Mirror-safe kernel validation
    println!("\n--- Mirror-Safe Kernel Validation ---");

    // Simulate a kernel that uses mirror pairs
    let kernel_classes = vec![10, validation_data.get_mirror(10).unwrap()];
    if validation_data.are_mirror_pairs(&kernel_classes) {
        println!("  Kernel with classes {:?}: mirror-safe ✓", kernel_classes);
    }

    // Simulate a kernel with unpaired classes
    let bad_kernel = vec![10, 20, 30];
    if !validation_data.are_mirror_pairs(&bad_kernel) {
        println!("  Kernel with classes {:?}: NOT mirror-safe ✗", bad_kernel);
    }

    // Example 4: Phase window validation
    println!("\n--- Phase Window Validation ---");

    // Normal window [100, 150)
    let window = AtlasPhaseWindow { begin: 100, span: 50 };
    println!("  Testing window [{}, {})", window.begin, window.begin + window.span);

    let phases_to_test = [99, 100, 125, 149, 150, 200];
    for &phase in &phases_to_test {
        let valid = validation_data.is_phase_valid(phase, &window);
        println!("    Phase {}: {}", phase, if valid { "✓ valid" } else { "✗ invalid" });
    }

    // Wrapping window [700, 50) = [700, 768) ∪ [0, 50)
    let wrapping = AtlasPhaseWindow { begin: 700, span: 118 };
    println!(
        "\n  Testing wrapping window [{}, {}) (wraps at {})",
        wrapping.begin,
        (wrapping.begin + wrapping.span) % PHASE_MODULUS,
        PHASE_MODULUS
    );

    let wrap_phases = [699, 700, 750, 0, 49, 50];
    for &phase in &wrap_phases {
        let valid = validation_data.is_phase_valid(phase, &wrapping);
        println!("    Phase {}: {}", phase, if valid { "✓ valid" } else { "✗ invalid" });
    }

    // Example 5: Class mask conflict detection
    println!("\n--- Class Mask Conflict Detection ---");

    let mut kernel_mask = AtlasClassMask::empty();
    kernel_mask.low = (1u64 << 10) | (1u64 << 20); // Classes 10, 20

    let mut active_mask = AtlasClassMask::empty();
    active_mask.low = (1u64 << 20) | (1u64 << 30); // Classes 20, 30

    if validation_data.masks_conflict(&kernel_mask, &active_mask) {
        println!("  Kernel mask conflicts with active classes (class 20 overlap) ✓");
    }

    let mut disjoint_mask = AtlasClassMask::empty();
    disjoint_mask.low = 1u64 << 50; // Class 50

    if !validation_data.masks_conflict(&kernel_mask, &disjoint_mask) {
        println!("  Kernel mask has no conflicts with disjoint classes ✓");
    }

    // Example 6: Integration scenario
    println!("\n--- Typical Launch Validation Flow ---");

    let current_phase = 125u32;
    let kernel_window = AtlasPhaseWindow { begin: 100, span: 50 };
    let kernel_classes = vec![10, validation_data.get_mirror(10).unwrap()];
    let mut kernel_class_mask = AtlasClassMask::empty();
    kernel_class_mask.low = (1u64 << 10) | (1u64 << validation_data.get_mirror(10).unwrap());

    println!("  Validating kernel launch at phase {}:", current_phase);

    // Step 1: Phase check
    if !validation_data.is_phase_valid(current_phase, &kernel_window) {
        println!("    ✗ Phase validation failed");
        return;
    }
    println!("    ✓ Phase {} is within window", current_phase);

    // Step 2: Mirror safety check
    if !validation_data.are_mirror_pairs(&kernel_classes) {
        println!("    ✗ Kernel is not mirror-safe");
        return;
    }
    println!("    ✓ Kernel is mirror-safe");

    // Step 3: Scheduling conflict check
    let active = AtlasClassMask::empty(); // No active kernels
    if validation_data.masks_conflict(&kernel_class_mask, &active) {
        println!("    ⚠ Scheduling conflict - must serialize");
    } else {
        println!("    ✓ No scheduling conflicts");
    }

    println!("    → Kernel launch validated successfully!");

    println!("\n=== Demo Complete ===");
}
