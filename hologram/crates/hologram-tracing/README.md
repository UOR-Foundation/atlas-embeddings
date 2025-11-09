# hologram-tracing

Shared tracing configuration helpers for the Atlas / Hologram workspace, including comprehensive performance instrumentation utilities.

## Features

- **Consistent tracing configuration** across binaries, tests, and examples
- **Environment-driven profiles** for local development, CI, and performance analysis
- **Performance instrumentation** with automatic timing, bandwidth, and FLOPS calculation
- **Ergonomic macros** for common instrumentation patterns
- **Field redaction** for sensitive data
- **Flexible output formats** (Pretty, Compact, JSON)

## Quick Start

### Basic Tracing

```rust
use hologram_tracing::{TracingConfig, init_global_tracing};

// Initialize with default (local) configuration
let config = TracingConfig::default();
init_global_tracing(&config)?;

// Your application code with tracing
tracing::info!("Application started");
```

### Performance Tracing

```rust
use hologram_tracing::{perf_span, perf_event};
use hologram_tracing::performance::{record_allocation, record_transfer};

// Create a performance span
{
    let _span = perf_span!("vector_add", n = 1024, bytes = 4096);
    // ... operation code ...
} // Automatically logs duration

// Record specific performance events
record_allocation(1024, "Linear", 64, 150);
record_transfer(4096, "H2D", 250);
```

## Configuration Profiles

### Local Development (`for_local()`)

- Pretty ANSI-colored output
- Performance tracing enabled in debug builds
- Human-readable format

```rust
let config = TracingConfig::for_local();
```

### CI/Production (`for_ci()`)

- JSON output for machine parsing
- No ANSI colors
- Performance tracing disabled

```rust
let config = TracingConfig::for_ci();
```

### Performance Analysis (`for_performance()`)

- JSON output with detailed span events
- Performance tracing always enabled
- Debug/trace level logging for performance-critical crates
- Includes ENTER, EXIT, and CLOSE span events

```rust
let config = TracingConfig::for_performance();
```

## Environment Variables

### Basic Configuration

- `HOLOGRAM_TRACING_PROFILE`: Profile preset (`local`, `ci`, or `performance`)
- `HOLOGRAM_TRACING_FORMAT`: Output format (`pretty`, `compact`, or `json`)
- `HOLOGRAM_TRACING_DIRECTIVES`: Tracing filter directives (e.g., `atlas_backends=debug,info`)
- `HOLOGRAM_TRACING_REDACT_FIELDS`: Comma-separated fields to redact (e.g., `secret,token`)
- `HOLOGRAM_TRACING_REDACT_TOKEN`: Replacement text for redacted values (default: `***REDACTED***`)

### Performance Configuration

- `HOLOGRAM_PERF_TRACING`: Enable/disable performance tracing (`true`, `false`, `1`, `yes`)
- `HOLOGRAM_PERF_THRESHOLD_US`: Minimum duration (microseconds) to log (filters noise)
- `HOLOGRAM_PERF_DIRECTIVES`: Performance-specific tracing directives

### Example Usage

```bash
# Local development with performance tracing
export HOLOGRAM_TRACING_PROFILE=local
export HOLOGRAM_PERF_TRACING=true
cargo run

# CI with JSON output
export HOLOGRAM_TRACING_PROFILE=ci
export HOLOGRAM_TRACING_FORMAT=json
cargo test

# Performance analysis with threshold filtering
export HOLOGRAM_TRACING_PROFILE=performance
export HOLOGRAM_PERF_THRESHOLD_US=1000  # Only log operations > 1ms
cargo run --example benchmark
```

## Performance Tracing

### Automatic Timing with `PerformanceSpan`

```rust
use hologram_tracing::performance::PerformanceSpan;

{
    let span = PerformanceSpan::new("expensive_operation", Some(1000));
    // ... operation code ...
} // Logs duration only if > 1000μs
```

### Convenience Macros

```rust
use hologram_tracing::{perf_span, perf_event, timed_block, perf_span_threshold};

// Simple span
let _span = perf_span!("operation");

// Span with fields
let _span = perf_span!("vector_add", n = 1024, bytes = 4096);

// Span with threshold (only logs if > 1ms)
let _span = perf_span_threshold!("slow_op", 1000, size = 2048);

// Timed block
let (result, duration_us) = timed_block!("computation", {
    expensive_function()
});

// Performance event
perf_event!("cache_hit", size = 1024, latency_ns = 50);
```

### Standard Performance Recording Functions

```rust
use hologram_tracing::performance::*;

// Memory allocation
record_allocation(
    1024,          // size_bytes
    "Linear",      // pool_type
    64,            // alignment
    150            // duration_us
);

// ISA execution
record_execution(
    1024,          // instruction_count
    500,           // duration_us
    3              // active_classes
);

// Data transfer
record_transfer(
    4096,          // bytes
    "H2D",         // direction (H2D/D2H/D2D)
    250            // duration_us
);

// Operation throughput
record_throughput(
    "vector_add",  // operation
    1024,          // elements
    100            // duration_us
);

// FLOPS measurement
record_flops(
    "gemm",        // operation
    2 * 128 * 128 * 128,  // flop_count
    5000           // duration_us
);
```

## Performance Overhead

The performance instrumentation is designed to have minimal overhead:

- **Disabled**: Zero cost (compile-time checks)
- **Enabled but unused**: < 1% overhead (span creation only)
- **Enabled and logging**: < 10% overhead (depends on log frequency)

Threshold filtering helps reduce overhead by only logging significant operations.

## Output Format Examples

### Pretty Output (Local Development)

```
2024-10-22T12:34:56.789Z DEBUG perf name="vector_add" n=1024 bytes=4096
2024-10-22T12:34:56.791Z DEBUG   duration_us=123 duration_ms=0.123 event="performance_span_complete"
```

### JSON Output (CI/Performance Analysis)

```json
{
  "timestamp": "2024-10-22T12:34:56.789Z",
  "level": "DEBUG",
  "target": "perf",
  "fields": {
    "name": "vector_add",
    "n": 1024,
    "bytes": 4096,
    "duration_us": 123,
    "duration_ms": 0.123,
    "event": "performance_span_complete"
  }
}
```

## Integration with Applications

### Example: Instrumented Operation

```rust
use hologram_tracing::{perf_span, performance::record_throughput};

pub fn vector_add(a: &[f32], b: &[f32], c: &mut [f32]) -> Result<()> {
    let _span = perf_span!("vector_add",
        n = a.len(),
        bytes = a.len() * std::mem::size_of::<f32>()
    );

    let start = std::time::Instant::now();

    for i in 0..a.len() {
        c[i] = a[i] + b[i];
    }

    record_throughput("vector_add", a.len(), start.elapsed().as_micros() as u64);
    Ok(())
}
```

### Example: Benchmark with Tracing

```rust
use hologram_tracing::{TracingConfig, init_global_tracing};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Initialize performance tracing
    let config = TracingConfig::for_performance();
    init_global_tracing(&config)?;

    // Run benchmarks
    run_benchmarks();

    Ok(())
}
```

## Post-Processing Traces

JSON output can be parsed and analyzed:

```bash
# Capture traces to file
HOLOGRAM_TRACING_FORMAT=json cargo run 2> traces.json

# Extract performance spans
cat traces.json | jq 'select(.fields.event == "performance_span_complete")'

# Calculate average duration
cat traces.json | jq -s 'map(select(.fields.duration_us)) | map(.fields.duration_us) | add / length'

# Find slowest operations
cat traces.json | jq -s 'sort_by(.fields.duration_us) | reverse | .[0:10]'
```

## Troubleshooting

### Performance Tracing Not Appearing

1. Check that `enable_performance_tracing` is true
2. Verify log level is debug or trace
3. Ensure directives include performance-critical crates
4. Check threshold isn't filtering out all spans

```rust
let mut config = TracingConfig::from_env();
config.enable_performance_tracing = true;
config.performance_threshold_us = None;  // Log everything
config.directives = Some("debug".to_string());
```

### Too Much Output

1. Increase threshold to filter noise
2. Use more specific directives
3. Target only critical operations

```bash
export HOLOGRAM_PERF_THRESHOLD_US=10000  # Only log > 10ms
export HOLOGRAM_PERF_DIRECTIVES="atlas_backends::cpu=debug"
```

### Permission Errors in Tests

Tests with environment variables should use the `ENV_LOCK` mutex:

```rust
#[test]
fn my_test() {
    let _guard = ENV_LOCK.lock().unwrap();
    // Test code that modifies environment
}
```

## Advanced Usage

### Custom Span Levels

```rust
use hologram_tracing::performance::PerformanceSpan;
use tracing::Level;

let span = PerformanceSpan::with_level(
    Level::WARN,
    "critical_operation",
    Some(5000)
);
```

### Conditional Instrumentation

```rust
if config.enable_performance_tracing {
    let _span = perf_span!("optional_instrumentation");
    // ... code ...
}
```

### Integration with External Tools

Export traces for analysis with tools like:

- **Jaeger**: For distributed tracing visualization
- **Flamegraphs**: For hierarchical performance analysis
- **Custom analyzers**: Parse JSON for domain-specific insights

## See Also

- [Performance Profiling Guide](../../docs/PERFORMANCE_PROFILING.md) - Comprehensive performance analysis workflow
- [Developer Guide](../../docs/DEVELOPER_GUIDE_INSTRUMENTATION.md) - Adding instrumentation to code
- [User Guide](../../docs/USER_GUIDE_PERFORMANCE_TRACING.md) - End-user tracing guide
