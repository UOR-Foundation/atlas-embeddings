//! Performance-focused tracing utilities
//!
//! This module provides utilities for performance instrumentation with automatic
//! timing, bandwidth calculation, and threshold filtering.
//!
//! ## Example
//!
//! ```rust
//! use hologram_tracing::performance::{PerformanceSpan, record_allocation};
//!
//! // Create a performance span with threshold filtering
//! let span = PerformanceSpan::new("my_operation", Some(100));
//! // ... do work ...
//! drop(span); // Logs only if duration > 100μs
//!
//! // Record a memory allocation event
//! record_allocation(1024, "Linear", 64, 150);
//! ```

use std::time::Instant;
use tracing::Level;

/// RAII guard that measures span duration and conditionally logs based on threshold.
///
/// The span is automatically timed when created and logged when dropped, but only
/// if the duration exceeds the optional threshold.
///
/// # Example
///
/// ```rust
/// use hologram_tracing::performance::PerformanceSpan;
///
/// {
///     let _span = PerformanceSpan::new("expensive_operation", Some(1000));
///     // ... operation code ...
/// } // Span logged only if duration > 1000μs
/// ```
pub struct PerformanceSpan {
    _span_name: String,
    threshold_us: Option<u64>,
    start_time: Instant,
    span: tracing::Span,
}

impl PerformanceSpan {
    /// Create a new performance span with optional threshold filtering.
    ///
    /// # Arguments
    ///
    /// * `span_name` - Name of the operation being measured
    /// * `threshold_us` - Minimum duration in microseconds to log (None = always log)
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_tracing::performance::PerformanceSpan;
    ///
    /// // Always log
    /// let span1 = PerformanceSpan::new("always_log", None);
    ///
    /// // Only log if > 100μs
    /// let span2 = PerformanceSpan::new("conditional", Some(100));
    /// ```
    pub fn new(span_name: impl Into<String>, threshold_us: Option<u64>) -> Self {
        let span_name = span_name.into();
        let span = tracing::debug_span!("perf", name = %span_name);
        let start_time = Instant::now();

        Self {
            _span_name: span_name,
            threshold_us,
            start_time,
            span,
        }
    }

    /// Create a new performance span at the specified tracing level.
    ///
    /// # Arguments
    ///
    /// * `level` - Tracing level (Debug, Info, Warn, etc.)
    /// * `span_name` - Name of the operation
    /// * `threshold_us` - Minimum duration in microseconds to log
    ///
    /// # Example
    ///
    /// ```rust
    /// use hologram_tracing::performance::PerformanceSpan;
    /// use tracing::Level;
    ///
    /// let span = PerformanceSpan::with_level(
    ///     Level::INFO,
    ///     "important_operation",
    ///     Some(500)
    /// );
    /// ```
    pub fn with_level(level: Level, span_name: impl Into<String>, threshold_us: Option<u64>) -> Self {
        let span_name = span_name.into();
        let span = match level {
            Level::TRACE => tracing::trace_span!("perf", name = %span_name),
            Level::DEBUG => tracing::debug_span!("perf", name = %span_name),
            Level::INFO => tracing::info_span!("perf", name = %span_name),
            Level::WARN => tracing::warn_span!("perf", name = %span_name),
            Level::ERROR => tracing::error_span!("perf", name = %span_name),
        };
        let start_time = Instant::now();

        Self {
            _span_name: span_name,
            threshold_us,
            start_time,
            span,
        }
    }

    /// Get the elapsed time since span creation.
    pub fn elapsed_us(&self) -> u64 {
        self.start_time.elapsed().as_micros() as u64
    }

    /// Enter this span's context.
    pub fn enter(&self) -> tracing::span::Entered<'_> {
        self.span.enter()
    }
}

impl Drop for PerformanceSpan {
    fn drop(&mut self) {
        let elapsed_us = self.elapsed_us();

        // Only log if threshold is None or duration exceeds threshold
        if self.threshold_us.is_none_or(|t| elapsed_us >= t) {
            let _entered = self.span.enter();
            tracing::debug!(
                duration_us = elapsed_us,
                duration_ms = elapsed_us as f64 / 1000.0,
                "performance_span_complete"
            );
        }
    }
}

/// Record a memory allocation event with standard format.
///
/// Emits a tracing event with allocation details including size, pool type,
/// alignment, and duration.
///
/// # Arguments
///
/// * `size_bytes` - Size of allocation in bytes
/// * `pool_type` - Type of memory pool ("Linear", "Boundary", etc.)
/// * `alignment` - Memory alignment in bytes
/// * `duration_us` - Time taken for allocation in microseconds
///
/// # Example
///
/// ```rust
/// use hologram_tracing::performance::record_allocation;
///
/// record_allocation(1024, "Linear", 64, 150);
/// ```
pub fn record_allocation(size_bytes: usize, pool_type: &str, alignment: usize, duration_us: u64) {
    tracing::debug!(
        event = "allocation",
        size_bytes = size_bytes,
        size_kb = size_bytes as f64 / 1024.0,
        pool_type = pool_type,
        alignment = alignment,
        duration_us = duration_us,
        "memory_allocation"
    );
}

/// Record an ISA program execution event with standard format.
///
/// Emits a tracing event with execution details including instruction count,
/// duration, and calculated throughput.
///
/// # Arguments
///
/// * `instruction_count` - Number of instructions executed
/// * `duration_us` - Execution time in microseconds
/// * `active_classes` - Number of active resonance classes
///
/// # Example
///
/// ```rust
/// use hologram_tracing::performance::record_execution;
///
/// record_execution(1024, 500, 3);
/// ```
pub fn record_execution(instruction_count: usize, duration_us: u64, active_classes: usize) {
    let throughput = if duration_us > 0 {
        (instruction_count as f64 / duration_us as f64) * 1_000_000.0
    } else {
        0.0
    };

    tracing::debug!(
        event = "execution",
        instruction_count = instruction_count,
        duration_us = duration_us,
        duration_ms = duration_us as f64 / 1000.0,
        active_classes = active_classes,
        instructions_per_sec = throughput,
        "isa_execution"
    );
}

/// Record a data transfer event with standard format and bandwidth calculation.
///
/// Emits a tracing event with transfer details including size, direction,
/// duration, and calculated bandwidth.
///
/// # Arguments
///
/// * `bytes` - Number of bytes transferred
/// * `direction` - Transfer direction ("H2D" = Host to Device, "D2H" = Device to Host, "D2D" = Device to Device)
/// * `duration_us` - Transfer time in microseconds
///
/// # Example
///
/// ```rust
/// use hologram_tracing::performance::record_transfer;
///
/// record_transfer(4096, "H2D", 250);
/// ```
pub fn record_transfer(bytes: usize, direction: &str, duration_us: u64) {
    let bandwidth_mbps = if duration_us > 0 {
        (bytes as f64 / duration_us as f64) * 1_000_000.0 / (1024.0 * 1024.0)
    } else {
        0.0
    };

    tracing::debug!(
        event = "transfer",
        bytes = bytes,
        kb = bytes as f64 / 1024.0,
        mb = bytes as f64 / (1024.0 * 1024.0),
        direction = direction,
        duration_us = duration_us,
        duration_ms = duration_us as f64 / 1000.0,
        bandwidth_mbps = bandwidth_mbps,
        bandwidth_gbps = bandwidth_mbps / 1024.0,
        "data_transfer"
    );
}

/// Record an operation throughput event.
///
/// Emits a tracing event for operations with element count, duration, and throughput.
///
/// # Arguments
///
/// * `operation` - Name of the operation
/// * `elements` - Number of elements processed
/// * `duration_us` - Operation time in microseconds
///
/// # Example
///
/// ```rust
/// use hologram_tracing::performance::record_throughput;
///
/// record_throughput("vector_add", 1024, 100);
/// ```
pub fn record_throughput(operation: &str, elements: usize, duration_us: u64) {
    let elements_per_sec = if duration_us > 0 {
        (elements as f64 / duration_us as f64) * 1_000_000.0
    } else {
        0.0
    };

    tracing::debug!(
        event = "throughput",
        operation = operation,
        elements = elements,
        duration_us = duration_us,
        duration_ms = duration_us as f64 / 1000.0,
        elements_per_sec = elements_per_sec,
        melems_per_sec = elements_per_sec / 1_000_000.0,
        "operation_throughput"
    );
}

/// Record FLOPS (floating-point operations per second) for compute operations.
///
/// # Arguments
///
/// * `operation` - Name of the operation
/// * `flops` - Number of floating-point operations
/// * `duration_us` - Operation time in microseconds
///
/// # Example
///
/// ```rust
/// use hologram_tracing::performance::record_flops;
///
/// // Matrix multiply: 2*M*N*K operations
/// record_flops("gemm", 2 * 128 * 128 * 128, 5000);
/// ```
pub fn record_flops(operation: &str, flops: usize, duration_us: u64) {
    let flops_per_sec = if duration_us > 0 {
        (flops as f64 / duration_us as f64) * 1_000_000.0
    } else {
        0.0
    };

    let gflops = flops_per_sec / 1_000_000_000.0;

    tracing::debug!(
        event = "flops",
        operation = operation,
        flops = flops,
        duration_us = duration_us,
        duration_ms = duration_us as f64 / 1000.0,
        flops_per_sec = flops_per_sec,
        gflops = gflops,
        "compute_performance"
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_performance_span_creation() {
        let span = PerformanceSpan::new("test_span", None);
        assert_eq!(span._span_name, "test_span");
        assert_eq!(span.threshold_us, None);
    }

    #[test]
    fn test_performance_span_with_threshold() {
        let span = PerformanceSpan::new("test_span", Some(1000));
        assert_eq!(span.threshold_us, Some(1000));
    }

    #[test]
    fn test_performance_span_elapsed() {
        let span = PerformanceSpan::new("test_span", None);
        thread::sleep(Duration::from_millis(10));
        let elapsed = span.elapsed_us();
        assert!(elapsed >= 10_000, "elapsed should be at least 10ms");
    }

    #[test]
    fn test_performance_span_with_level() {
        let span = PerformanceSpan::with_level(Level::INFO, "test_span", Some(100));
        assert_eq!(span._span_name, "test_span");
        assert_eq!(span.threshold_us, Some(100));
    }

    #[test]
    fn test_record_allocation() {
        // Just verify it doesn't panic
        record_allocation(1024, "Linear", 64, 150);
    }

    #[test]
    fn test_record_execution() {
        // Just verify it doesn't panic
        record_execution(1024, 500, 3);
    }

    #[test]
    fn test_record_transfer() {
        // Just verify it doesn't panic
        record_transfer(4096, "H2D", 250);
    }

    #[test]
    fn test_record_throughput() {
        // Just verify it doesn't panic
        record_throughput("vector_add", 1024, 100);
    }

    #[test]
    fn test_record_flops() {
        // Just verify it doesn't panic
        record_flops("gemm", 2 * 128 * 128 * 128, 5000);
    }

    #[test]
    fn test_bandwidth_calculation() {
        // Transfer 1MB in 1ms = 1000 MB/s
        let bytes = 1024 * 1024;
        let duration_us = 1000;
        let bandwidth_mbps = (bytes as f64 / duration_us as f64) * 1_000_000.0 / (1024.0 * 1024.0);
        assert!((bandwidth_mbps - 1000.0).abs() < 0.01);
    }

    #[test]
    fn test_throughput_calculation() {
        // 1M elements in 1ms = 1B elements/sec
        let elements = 1_000_000;
        let duration_us = 1000;
        let elements_per_sec = (elements as f64 / duration_us as f64) * 1_000_000.0;
        assert!((elements_per_sec - 1_000_000_000.0).abs() < 1.0);
    }

    #[test]
    fn test_gflops_calculation() {
        // 1B FLOPS in 1s = 1 GFLOPS
        let flops = 1_000_000_000;
        let duration_us = 1_000_000;
        let flops_per_sec = (flops as f64 / duration_us as f64) * 1_000_000.0;
        let gflops = flops_per_sec / 1_000_000_000.0;
        assert!((gflops - 1.0).abs() < 0.01);
    }
}
