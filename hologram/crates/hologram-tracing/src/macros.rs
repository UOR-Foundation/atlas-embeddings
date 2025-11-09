//! Convenience macros for performance tracing
//!
//! This module provides ergonomic macros that simplify common performance
//! instrumentation patterns with automatic field capture and span management.

/// Create a performance span with automatic field capture.
///
/// This macro creates a [`crate::performance::PerformanceSpan`] with the given name
/// and fields, returning a guard that will automatically log timing when dropped.
///
/// # Syntax
///
/// ```text
/// perf_span!("name")
/// perf_span!("name", field1 = value1)
/// perf_span!("name", field1 = value1, field2 = value2, ...)
/// ```
///
/// # Example
///
/// ```rust
/// use hologram_tracing::perf_span;
///
/// {
///     let _span = perf_span!("vector_add", n = 1024, bytes = 4096);
///     // ... operation code ...
/// } // Automatically logs duration with fields
/// ```
#[macro_export]
macro_rules! perf_span {
    ($name:expr) => {{
        $crate::performance::PerformanceSpan::new($name, None)
    }};
    ($name:expr, $($field:tt = $value:expr),+ $(,)?) => {{
        let _span = tracing::debug_span!(
            "perf",
            name = $name,
            $($field = $value),+
        ).entered();
        $crate::performance::PerformanceSpan::new($name, None)
    }};
}

/// Emit a standardized performance event.
///
/// This macro emits a tracing event with the given name and metrics at debug level.
///
/// # Syntax
///
/// ```text
/// perf_event!("name", metric1 = value1, metric2 = value2, ...)
/// ```
///
/// # Example
///
/// ```rust
/// use hologram_tracing::perf_event;
///
/// perf_event!("allocation_complete",
///     size_bytes = 1024,
///     duration_us = 150,
///     pool = "Linear"
/// );
/// ```
#[macro_export]
macro_rules! perf_event {
    ($name:expr, $($field:tt = $value:expr),+ $(,)?) => {
        tracing::debug!(
            event = $name,
            $($field = $value),+
        );
    };
}

/// Execute a block of code with automatic timing.
///
/// This macro wraps a block of code in a timed context, returning a tuple
/// of (result, duration_in_microseconds). Useful for benchmarking specific
/// code sections.
///
/// # Syntax
///
/// ```text
/// let (result, duration_us) = timed_block!("operation_name", {
///     // code to time
/// });
/// ```
///
/// # Example
///
/// ```rust
/// use hologram_tracing::timed_block;
///
/// let (sum, duration_us) = timed_block!("sum_calculation", {
///     (1..=100).sum::<i32>()
/// });
///
/// println!("Sum: {}, took {}μs", sum, duration_us);
/// ```
#[macro_export]
macro_rules! timed_block {
    ($name:expr, $block:block) => {{
        let start = std::time::Instant::now();
        let result = $block;
        let duration_us = start.elapsed().as_micros() as u64;
        tracing::debug!(
            operation = $name,
            duration_us = duration_us,
            duration_ms = duration_us as f64 / 1000.0,
            "timed_block_complete"
        );
        (result, duration_us)
    }};
}

/// Create a performance span with threshold filtering.
///
/// Only logs if the duration exceeds the specified threshold in microseconds.
///
/// # Syntax
///
/// ```text
/// perf_span_threshold!("name", threshold_us)
/// perf_span_threshold!("name", threshold_us, field1 = value1, ...)
/// ```
///
/// # Example
///
/// ```rust
/// use hologram_tracing::perf_span_threshold;
///
/// {
///     // Only logs if duration > 1000μs (1ms)
///     let _span = perf_span_threshold!("expensive_op", 1000, size = 1024);
///     // ... operation code ...
/// }
/// ```
#[macro_export]
macro_rules! perf_span_threshold {
    ($name:expr, $threshold_us:expr) => {{
        $crate::performance::PerformanceSpan::new($name, Some($threshold_us))
    }};
    ($name:expr, $threshold_us:expr, $($field:tt = $value:expr),+ $(,)?) => {{
        let _span = tracing::debug_span!(
            "perf",
            name = $name,
            $($field = $value),+
        ).entered();
        $crate::performance::PerformanceSpan::new($name, Some($threshold_us))
    }};
}

#[cfg(test)]
mod tests {
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_perf_span_macro() {
        let _span = perf_span!("test_operation");
        // Should not panic
    }

    #[test]
    fn test_perf_span_with_fields() {
        let _span = perf_span!("test_operation", size = 1024, count = 10);
        // Should not panic
    }

    #[test]
    fn test_perf_event_macro() {
        perf_event!("test_event", metric1 = 100, metric2 = "value");
        // Should not panic
    }

    #[test]
    fn test_timed_block_macro() {
        let (result, duration_us) = timed_block!("test_block", {
            thread::sleep(Duration::from_millis(10));
            42
        });
        assert_eq!(result, 42);
        assert!(duration_us >= 10_000, "Should take at least 10ms");
    }

    #[test]
    fn test_timed_block_with_error() {
        let (result, _duration_us) = timed_block!("test_error_block", { Result::<i32, &str>::Err("test error") });
        assert!(result.is_err());
    }

    #[test]
    fn test_perf_span_threshold_macro() {
        let _span = perf_span_threshold!("test_threshold", 1000);
        // Should not panic
    }

    #[test]
    fn test_perf_span_threshold_with_fields() {
        let _span = perf_span_threshold!("test_threshold", 1000, size = 2048);
        // Should not panic
    }
}
