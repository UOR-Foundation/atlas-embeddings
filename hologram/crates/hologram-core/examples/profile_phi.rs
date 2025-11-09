use hologram_core::{ops, Executor};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize tracing
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::DEBUG)
        .with_target(true)
        .with_thread_ids(true)
        .with_line_number(true)
        .init();

    println!("=== PhiCoordinate Performance Profile ===\n");

    // Create executor (should initialize pools once)
    println!("Creating executor...");
    let start = std::time::Instant::now();
    let mut exec = Executor::new()?;
    println!("Executor created in {:?}\n", start.elapsed());

    // Allocate boundary pool buffers (256 f32 elements = 1024 bytes)
    println!("Allocating boundary pool buffers...");
    let start = std::time::Instant::now();
    let size = 256;
    let (w, h) = ((size * 4 + 255) / 256, 256); // (4 pages, 256 bytes/page)

    let a = exec.allocate_boundary::<f32>(0, w, h)?;
    let b = exec.allocate_boundary::<f32>(1, w, h)?;
    let mut c = exec.allocate_boundary::<f32>(2, w, h)?;
    println!("Buffers allocated in {:?}\n", start.elapsed());

    // First operation (may trigger pool initialization)
    println!("=== First operation (may trigger initialization) ===");
    let start = std::time::Instant::now();
    ops::math::vector_add(&mut exec, &a, &b, &mut c, size)?;
    let first_op_time = start.elapsed();
    println!("First vector_add completed in {:?}\n", first_op_time);

    // Subsequent operations (should reuse initialized pools)
    println!("=== Subsequent operations (warm) ===");
    let iterations = 10000;
    let start = std::time::Instant::now();
    for _ in 0..iterations {
        ops::math::vector_add(&mut exec, &a, &b, &mut c, size)?;
    }
    let total_time = start.elapsed();
    let avg_time = total_time / iterations;

    println!("Completed {} iterations in {:?}", iterations, total_time);
    println!("Average time per operation: {:?}", avg_time);
    println!("Throughput: {:.2} Mops/s", 1_000_000.0 / avg_time.as_nanos() as f64);
    println!(
        "Throughput: {:.2} Gelem/s",
        1_000.0 * size as f64 / avg_time.as_nanos() as f64
    );

    Ok(())
}
