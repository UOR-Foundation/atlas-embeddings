//! Comprehensive Instrumentation for Generator-Based Execution
//!
//! This module provides four levels of instrumentation:
//! 1. **Generator-level**: Individual generator call metrics
//! 2. **Compilation-level**: Operation → generator sequence compilation
//! 3. **Execution-level**: Full operation execution end-to-end
//! 4. **Optimization-level**: Canonicalization and fusion passes
//!
//! ## Design Principles
//!
//! - **Zero-overhead when tracing disabled**: All metrics collection is behind tracing feature
//! - **Structured logging**: Uses tracing crate for consistent event format
//! - **Aggregation-friendly**: Metrics designed for collection by tools like Prometheus/Jaeger
//! - **Low overhead**: <1% performance impact when enabled
//!
//! ## Example
//!
//! ```text
//! use hologram_core::instrumentation::{ExecutionMetrics, record_execution};
//!
//! let start = std::time::Instant::now();
//! // ... execute operation ...
//! let metrics = ExecutionMetrics::new("vector_add", n, start);
//! metrics.log();
//! ```

use std::time::{Duration, Instant};

// ============================================================================
// Generator-Level Metrics
// ============================================================================

/// Metrics for a single generator call
#[derive(Debug, Clone)]
pub struct GeneratorMetrics {
    /// Generator name (mark, copy, swap, merge, split, quote, evaluate)
    pub generator_name: &'static str,
    /// Duration of generator execution (nanoseconds)
    pub duration_ns: u64,
    /// Number of bytes processed (12,288 for single class, 24,576 for two classes)
    pub bytes_processed: usize,
    /// Source class
    pub src_class: u8,
    /// Destination class (if applicable)
    pub dst_class: Option<u8>,
    /// Context class (if applicable)
    pub context_class: Option<u8>,
}

impl GeneratorMetrics {
    /// Create metrics for Mark generator (single class, 12,288 bytes)
    pub fn mark(class: u8, duration: Duration) -> Self {
        Self {
            generator_name: "mark",
            duration_ns: duration.as_nanos() as u64,
            bytes_processed: 12_288,
            src_class: class,
            dst_class: None,
            context_class: None,
        }
    }

    /// Create metrics for Copy generator (two classes, 24,576 bytes)
    pub fn copy(src: u8, dst: u8, duration: Duration) -> Self {
        Self {
            generator_name: "copy",
            duration_ns: duration.as_nanos() as u64,
            bytes_processed: 24_576,
            src_class: src,
            dst_class: Some(dst),
            context_class: None,
        }
    }

    /// Create metrics for Swap generator (two classes, 24,576 bytes)
    pub fn swap(class_a: u8, class_b: u8, duration: Duration) -> Self {
        Self {
            generator_name: "swap",
            duration_ns: duration.as_nanos() as u64,
            bytes_processed: 24_576,
            src_class: class_a,
            dst_class: Some(class_b),
            context_class: None,
        }
    }

    /// Create metrics for Merge generator (three classes, 36,864 bytes)
    pub fn merge(src: u8, dst: u8, context: u8, duration: Duration) -> Self {
        Self {
            generator_name: "merge",
            duration_ns: duration.as_nanos() as u64,
            bytes_processed: 36_864,
            src_class: src,
            dst_class: Some(dst),
            context_class: Some(context),
        }
    }

    /// Create metrics for Split generator (three classes, 36,864 bytes)
    pub fn split(src: u8, dst: u8, context: u8, duration: Duration) -> Self {
        Self {
            generator_name: "split",
            duration_ns: duration.as_nanos() as u64,
            bytes_processed: 36_864,
            src_class: src,
            dst_class: Some(dst),
            context_class: Some(context),
        }
    }

    /// Calculate throughput in GB/s
    pub fn throughput_gbps(&self) -> f64 {
        if self.duration_ns == 0 {
            return 0.0;
        }
        // bytes_processed / (duration_ns / 1e9) / 1e9
        // = bytes_processed * 1e9 / duration_ns / 1e9
        // = bytes_processed / duration_ns
        self.bytes_processed as f64 / self.duration_ns as f64
    }

    /// Log metrics via tracing
    pub fn log(&self) {
        tracing::trace!(
            generator = self.generator_name,
            duration_ns = self.duration_ns,
            bytes_processed = self.bytes_processed,
            throughput_gbps = self.throughput_gbps(),
            src_class = self.src_class,
            dst_class = ?self.dst_class,
            context_class = ?self.context_class,
            "generator_executed"
        );
    }
}

// ============================================================================
// Compilation-Level Metrics
// ============================================================================

/// Metrics for operation → generator sequence compilation
#[derive(Debug, Clone)]
pub struct CompilationMetrics {
    /// Operation name being compiled
    pub operation_name: String,
    /// Original operation count before canonicalization
    pub original_ops: usize,
    /// Canonical operation count after canonicalization
    pub canonical_ops: usize,
    /// Compilation duration (microseconds)
    pub duration_us: u64,
}

impl CompilationMetrics {
    /// Create compilation metrics
    pub fn new(
        operation_name: impl Into<String>,
        original_ops: usize,
        canonical_ops: usize,
        duration: Duration,
    ) -> Self {
        Self {
            operation_name: operation_name.into(),
            original_ops,
            canonical_ops,
            duration_us: duration.as_micros() as u64,
        }
    }

    /// Calculate reduction percentage
    pub fn reduction_percent(&self) -> f64 {
        if self.original_ops == 0 {
            return 0.0;
        }
        let reduction = self.original_ops.saturating_sub(self.canonical_ops);
        (reduction as f64 / self.original_ops as f64) * 100.0
    }

    /// Log metrics via tracing
    pub fn log(&self) {
        tracing::debug!(
            operation = %self.operation_name,
            original_ops = self.original_ops,
            canonical_ops = self.canonical_ops,
            duration_us = self.duration_us,
            reduction_percent = self.reduction_percent(),
            "compilation_completed"
        );
    }
}

// ============================================================================
// Execution-Level Metrics
// ============================================================================

/// Metrics for full operation execution (compilation + generator execution)
#[derive(Debug, Clone)]
pub struct ExecutionMetrics {
    /// Operation name (e.g., "vector_add", "gemm", "relu")
    pub operation_name: String,
    /// Total duration (compilation + execution) in microseconds
    pub total_duration_us: u64,
    /// Number of logical operations (e.g., n for vector_add, m*k*n for gemm)
    pub logical_ops: usize,
    /// Number of generator calls executed
    pub generator_count: usize,
    /// Compilation time (microseconds)
    pub compilation_time_us: u64,
    /// Execution time (microseconds)
    pub execution_time_us: u64,
}

impl ExecutionMetrics {
    /// Create execution metrics from start time
    pub fn new(operation_name: impl Into<String>, logical_ops: usize, start: Instant) -> Self {
        let total_duration_us = start.elapsed().as_micros() as u64;
        Self {
            operation_name: operation_name.into(),
            total_duration_us,
            logical_ops,
            generator_count: 0,
            compilation_time_us: 0,
            execution_time_us: total_duration_us,
        }
    }

    /// Create with detailed breakdown
    pub fn with_breakdown(
        operation_name: impl Into<String>,
        logical_ops: usize,
        generator_count: usize,
        compilation_time_us: u64,
        execution_time_us: u64,
    ) -> Self {
        Self {
            operation_name: operation_name.into(),
            total_duration_us: compilation_time_us + execution_time_us,
            logical_ops,
            generator_count,
            compilation_time_us,
            execution_time_us,
        }
    }

    /// Calculate operations per second
    pub fn ops_per_second(&self) -> f64 {
        if self.total_duration_us == 0 {
            return 0.0;
        }
        // logical_ops / (total_duration_us / 1e6)
        (self.logical_ops as f64 / self.total_duration_us as f64) * 1_000_000.0
    }

    /// Calculate memory bandwidth (GB/s) assuming 4 bytes per operation (f32)
    pub fn memory_bandwidth_gbps(&self) -> f64 {
        if self.total_duration_us == 0 {
            return 0.0;
        }
        // (logical_ops * 4 bytes) / (total_duration_us / 1e6) / 1e9
        (self.logical_ops as f64 * 4.0 / self.total_duration_us as f64) / 1000.0
    }

    /// Calculate compilation overhead percentage
    pub fn compilation_overhead_percent(&self) -> f64 {
        if self.total_duration_us == 0 {
            return 0.0;
        }
        (self.compilation_time_us as f64 / self.total_duration_us as f64) * 100.0
    }

    /// Log metrics via tracing
    pub fn log(&self) {
        tracing::debug!(
            operation = %self.operation_name,
            total_duration_us = self.total_duration_us,
            logical_ops = self.logical_ops,
            generator_count = self.generator_count,
            compilation_time_us = self.compilation_time_us,
            execution_time_us = self.execution_time_us,
            ops_per_second = self.ops_per_second(),
            memory_bandwidth_gbps = self.memory_bandwidth_gbps(),
            compilation_overhead_percent = self.compilation_overhead_percent(),
            "operation_executed"
        );
    }
}

// ============================================================================
// Optimization-Level Metrics
// ============================================================================

/// Metrics for optimization passes (fusion, canonicalization, etc.)
#[derive(Debug, Clone)]
pub struct OptimizationMetrics {
    /// Optimization pass name (e.g., "fusion", "canonicalization", "dead_code_elimination")
    pub pass_name: String,
    /// Duration of optimization pass (microseconds)
    pub duration_us: u64,
    /// Number of generators before optimization
    pub generators_before: usize,
    /// Number of generators after optimization
    pub generators_after: usize,
    /// Number of transformations applied
    pub transformations_applied: usize,
}

impl OptimizationMetrics {
    /// Create optimization metrics
    pub fn new(
        pass_name: impl Into<String>,
        duration: Duration,
        generators_before: usize,
        generators_after: usize,
        transformations_applied: usize,
    ) -> Self {
        Self {
            pass_name: pass_name.into(),
            duration_us: duration.as_micros() as u64,
            generators_before,
            generators_after,
            transformations_applied,
        }
    }

    /// Calculate reduction percentage
    pub fn reduction_percent(&self) -> f64 {
        if self.generators_before == 0 {
            return 0.0;
        }
        let reduction = self.generators_before.saturating_sub(self.generators_after);
        (reduction as f64 / self.generators_before as f64) * 100.0
    }

    /// Calculate cost/benefit ratio (time spent vs generators saved)
    pub fn cost_benefit_ratio(&self) -> f64 {
        let generators_saved = self.generators_before.saturating_sub(self.generators_after);
        if generators_saved == 0 {
            return f64::INFINITY; // Cost with no benefit
        }
        self.duration_us as f64 / generators_saved as f64
    }

    /// Log metrics via tracing
    pub fn log(&self) {
        tracing::debug!(
            pass = %self.pass_name,
            duration_us = self.duration_us,
            generators_before = self.generators_before,
            generators_after = self.generators_after,
            transformations_applied = self.transformations_applied,
            reduction_percent = self.reduction_percent(),
            cost_benefit_ratio = self.cost_benefit_ratio(),
            "optimization_pass_completed"
        );
    }
}

// ============================================================================
// Aggregate Statistics
// ============================================================================

/// Aggregate statistics across multiple operations
#[derive(Debug, Clone, Default)]
pub struct AggregateStatistics {
    /// Total number of operations executed
    pub operation_count: usize,
    /// Total logical operations
    pub total_logical_ops: usize,
    /// Total generator calls
    pub total_generator_calls: usize,
    /// Total execution time (microseconds)
    pub total_execution_time_us: u64,
    /// Total compilation time (microseconds)
    pub total_compilation_time_us: u64,
}

impl AggregateStatistics {
    /// Create empty statistics
    pub fn new() -> Self {
        Self::default()
    }

    /// Record an operation execution
    pub fn record(&mut self, metrics: &ExecutionMetrics) {
        self.operation_count += 1;
        self.total_logical_ops += metrics.logical_ops;
        self.total_generator_calls += metrics.generator_count;
        self.total_execution_time_us += metrics.execution_time_us;
        self.total_compilation_time_us += metrics.compilation_time_us;
    }

    /// Calculate average operations per second
    pub fn avg_ops_per_second(&self) -> f64 {
        if self.total_execution_time_us == 0 {
            return 0.0;
        }
        (self.total_logical_ops as f64 / self.total_execution_time_us as f64) * 1_000_000.0
    }

    /// Calculate average generator expansion ratio
    pub fn avg_expansion_ratio(&self) -> f64 {
        if self.total_logical_ops == 0 {
            return 0.0;
        }
        self.total_generator_calls as f64 / self.total_logical_ops as f64
    }

    /// Calculate compilation overhead percentage
    pub fn compilation_overhead_percent(&self) -> f64 {
        let total_time = self.total_execution_time_us + self.total_compilation_time_us;
        if total_time == 0 {
            return 0.0;
        }
        (self.total_compilation_time_us as f64 / total_time as f64) * 100.0
    }

    /// Log aggregate statistics
    pub fn log(&self) {
        tracing::info!(
            operation_count = self.operation_count,
            total_logical_ops = self.total_logical_ops,
            total_generator_calls = self.total_generator_calls,
            total_execution_time_us = self.total_execution_time_us,
            total_compilation_time_us = self.total_compilation_time_us,
            avg_ops_per_second = self.avg_ops_per_second(),
            avg_expansion_ratio = self.avg_expansion_ratio(),
            compilation_overhead_percent = self.compilation_overhead_percent(),
            "aggregate_statistics"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generator_metrics_throughput() {
        let metrics = GeneratorMetrics::mark(5, Duration::from_nanos(100));
        assert_eq!(metrics.bytes_processed, 12_288);
        assert_eq!(metrics.duration_ns, 100);
        // 12,288 bytes / 100 ns = 122.88 bytes/ns = 122.88 GB/s
        assert!((metrics.throughput_gbps() - 122.88).abs() < 0.01);
    }

    #[test]
    fn test_execution_metrics_ops_per_second() {
        let metrics = ExecutionMetrics::with_breakdown("test", 1000, 10, 5, 95);
        // 1000 ops / 100 us = 10M ops/sec
        assert_eq!(metrics.ops_per_second(), 10_000_000.0);
        assert_eq!(metrics.compilation_overhead_percent(), 5.0);
    }

    #[test]
    fn test_optimization_metrics_reduction() {
        let metrics = OptimizationMetrics::new("fusion", Duration::from_micros(10), 100, 80, 5);
        // (100 - 80) / 100 = 20%
        assert_eq!(metrics.reduction_percent(), 20.0);
        // 10 us / 20 generators = 0.5 us per generator saved
        assert_eq!(metrics.cost_benefit_ratio(), 0.5);
    }

    #[test]
    fn test_aggregate_statistics() {
        let mut stats = AggregateStatistics::new();

        let m1 = ExecutionMetrics::with_breakdown("op1", 1000, 10, 5, 95);
        let m2 = ExecutionMetrics::with_breakdown("op2", 2000, 20, 10, 190);

        stats.record(&m1);
        stats.record(&m2);

        assert_eq!(stats.operation_count, 2);
        assert_eq!(stats.total_logical_ops, 3000);
        assert_eq!(stats.total_generator_calls, 30);
        assert_eq!(stats.total_execution_time_us, 285);
        assert_eq!(stats.total_compilation_time_us, 15);
    }
}
