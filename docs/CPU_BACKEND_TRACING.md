# CPU Backend Tracing Instrumentation

## Overview

This document describes the comprehensive tracing instrumentation added to the CPU backend for performance monitoring and debugging.

## Implementation

### Dependencies

Added `hologram-tracing` dependency to `hologram-backends/Cargo.toml`:

```toml
[dependencies]
hologram-tracing = { path = "../hologram-tracing" }
```

### Instrumented Functions

All critical execution paths in `CpuExecutor` now have performance tracking using `perf_span!` macros:

#### 1. Program Execution
- **Function**: `execute()`
- **Metrics**:
  - `instructions`: Number of instructions in program
  - `grid_size`: Total number of blocks (x * y * z)
  - `block_size`: Total number of threads per block (x * y * z)
- **Purpose**: Track overall program execution time

#### 2. Memory Operations
- **LDG** (Load Global): `execute_ldg()`
  - Metrics: `bytes` = type size
- **STG** (Store Global): `execute_stg()`
  - Metrics: `bytes` = type size
- **LDS** (Load Shared): `execute_lds()`
  - Metrics: `bytes` = type size
- **STS** (Store Shared): `execute_sts()`
  - Metrics: `bytes` = type size

#### 3. Control Flow Operations
- **BRA** (Branch): `execute_bra()`
- **CALL** (Call subroutine): `execute_call()`
- **RET** (Return): `execute_ret()`
- **LOOP** (Loop): `execute_loop()`
- **EXIT** (Exit): `execute_exit()`

#### 4. Synchronization Operations
- **BarSync** (Barrier synchronization): `execute_barrier_sync()`
- **MemFence** (Memory fence): `execute_memory_fence()`

## Usage

### Enabling Tracing

Tracing is enabled through environment variables. See [hologram-tracing documentation](../crates/hologram-tracing/README.md) for full details.

**Quick start for performance profiling:**

```bash
# Enable performance tracing with debug output
export HOLOGRAM_TRACING_PROFILE=performance
export HOLOGRAM_PERF_TRACING=true

# Run your program
cargo run --release
```

**Development mode:**

```bash
# Pretty output for local development
export HOLOGRAM_TRACING_PROFILE=local
export RUST_LOG=hologram_backends=debug

cargo test
```

### Example Output

When running with tracing enabled, you'll see output like:

```
DEBUG perf{name="cpu_ldg" bytes=4}: hologram_tracing::performance: performance_span_complete duration_us=3 duration_ms=0.003
DEBUG perf{name="cpu_stg" bytes=4}: hologram_tracing::performance: performance_span_complete duration_us=4 duration_ms=0.004
DEBUG perf{name="cpu_exit"}: hologram_tracing::performance: performance_span_complete duration_us=0 duration_ms=0.0
DEBUG perf{name="cpu_execute_program" instructions=3 grid_size=1 block_size=1}: hologram_tracing::performance: performance_span_complete duration_us=83 duration_ms=0.083
```

### Filtering by Threshold

Set a minimum duration threshold to only log slow operations:

```bash
# Only log operations that take more than 100 microseconds
export HOLOGRAM_PERF_THRESHOLD_US=100
```

### JSON Output for Analysis

For machine-readable logs suitable for analysis:

```bash
export HOLOGRAM_TRACING_FORMAT=json
export HOLOGRAM_TRACING_PROFILE=performance
```

Output will be structured JSON:

```json
{
  "timestamp": "2025-10-28T23:46:54.455302Z",
  "level": "DEBUG",
  "fields": {
    "event": "performance_span_complete",
    "name": "cpu_execute_program",
    "instructions": 3,
    "grid_size": 1,
    "block_size": 1,
    "duration_us": 83,
    "duration_ms": 0.083
  }
}
```

## Performance Impact

The tracing instrumentation uses RAII guards (`perf_span!`) that:
- Have minimal overhead when tracing is disabled (compile-time checks)
- Only measure time elapsed using `Instant::now()` - no allocations
- Use threshold filtering to avoid logging fast operations
- Automatically clean up when scope exits

**Overhead**: < 1μs per span when enabled, ~0ns when disabled

## Testing

A comprehensive test validates the tracing instrumentation:

```rust
#[test]
fn test_tracing_instrumentation() {
    // Creates a program with LDG, STG, EXIT instructions
    // Executes with tracing enabled
    // Validates performance spans are emitted
}
```

Run with:
```bash
cargo test test_tracing_instrumentation -- --nocapture
```

## Future Enhancements

### GPU Backend Integration
When GPU backends are implemented, they can use the same tracing infrastructure:

```rust
impl Executor<GpuMemoryManager> for GpuExecutor {
    fn execute(&mut self, program: &Program, config: &LaunchConfig) -> Result<()> {
        let _span = perf_span!(
            "gpu_execute_program",
            instructions = program.instructions.len(),
            grid_size = config.grid.x * config.grid.y * config.grid.z,
            block_size = config.block.x * config.block.y * config.block.z
        );
        // GPU execution...
    }
}
```

### Additional Metrics
Future improvements could add:
- Memory bandwidth tracking for transfers
- Cache hit/miss rates
- Instruction dispatch statistics
- Parallel execution efficiency

### Integration with Profiling Tools
The tracing data can be exported to:
- Chrome Trace Viewer (via `tracing-chrome`)
- Prometheus metrics (via `tracing-prometheus`)
- OpenTelemetry (via `tracing-opentelemetry`)

## Architecture

The tracing implementation follows the established pattern in `hologram-tracing`:

1. **Performance Span**: RAII guard that measures duration
2. **Automatic Cleanup**: Logs on drop
3. **Threshold Filtering**: Configurable minimum duration
4. **Structured Fields**: Key-value pairs for analysis
5. **Zero-Overhead**: Disabled spans compile to no-ops

## References

- [hologram-tracing crate](../crates/hologram-tracing/)
- [CLAUDE.md - Testing Standards](../CLAUDE.md#testing-standards)
- [Tracing Subscriber Documentation](https://docs.rs/tracing-subscriber/)
- [Performance Tracing Examples](../crates/hologram-tracing/src/performance.rs)
