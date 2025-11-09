//! Shared tracing configuration utilities for the Atlas / Hologram workspace.
//!
//! The helpers in this crate centralise how executables, integration tests,
//! and supporting tools install `tracing` subscribers. By routing setup
//! through a single crate we avoid copy-pasting builder logic and keep the
//! logging surface consistent across binaries.

pub mod performance;

#[macro_use]
pub mod macros;

use std::collections::HashSet;
use std::env;
use std::error::Error;
use std::fmt::{self};
use std::sync::Arc;
pub use tracing::{debug, error, info, trace, warn};

use serde_json::{Map as JsonMap, Number as JsonNumber, Value as JsonValue};
use tracing::Subscriber;
use tracing_subscriber::field::RecordFields;
use tracing_subscriber::fmt::format::FmtSpan;
use tracing_subscriber::layer::Layer;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{fmt as tracing_fmt, EnvFilter, Registry};

/// Configuration describing how the shared tracing subscriber should behave.
#[derive(Clone, Debug)]
pub struct TracingConfig {
    /// Optional tracing directives (e.g. `hologram_cuda=debug,info`). When
    /// absent the crate will fall back to `RUST_LOG` and finally to
    /// [`default_directive`].
    pub directives: Option<String>,
    /// Fallback directive used when neither [`directives`] nor `RUST_LOG`
    /// resolve to a valid filter.
    pub default_directive: String,
    /// Controls whether event targets (module paths) appear in output.
    pub include_targets: bool,
    /// Controls ANSI formatting. Disable for CI logs that strip colour codes.
    pub ansi: bool,
    /// Span lifecycle events to emit. Defaults to [`FmtSpan::NONE`].
    pub span_events: FmtSpan,
    /// Output format for the formatter layer.
    pub output: TracingOutput,
    /// Field names whose values should be redacted before formatting.
    pub redacted_fields: Vec<String>,
    /// Replacement text used when redacting field values.
    pub redaction_text: String,
    /// Controls whether performance tracing is enabled.
    /// When false, performance spans are no-ops with minimal overhead.
    pub enable_performance_tracing: bool,
    /// Minimum duration in microseconds to log performance spans.
    /// Spans with duration below this threshold are not logged.
    /// None means all spans are logged regardless of duration.
    pub performance_threshold_us: Option<u64>,
    /// Performance-specific tracing directives, separate from main directives.
    /// Allows different log levels for performance vs regular tracing.
    pub performance_directives: Option<String>,
}

impl Default for TracingConfig {
    fn default() -> Self {
        Self::for_local()
    }
}

impl TracingConfig {
    /// Returns a configuration tuned for local development (pretty, ANSI-enabled output).
    pub fn for_local() -> Self {
        Self {
            directives: None,
            default_directive: "info".to_string(),
            include_targets: true,
            ansi: true,
            span_events: FmtSpan::NONE,
            output: TracingOutput::Pretty,
            redacted_fields: Vec::new(),
            redaction_text: "***REDACTED***".to_string(),
            enable_performance_tracing: cfg!(debug_assertions),
            performance_threshold_us: None,
            performance_directives: None,
        }
    }

    /// Returns a configuration tuned for CI or log collection environments (JSON, no ANSI).
    pub fn for_ci() -> Self {
        Self {
            directives: None,
            default_directive: "info".to_string(),
            include_targets: true,
            ansi: false,
            span_events: FmtSpan::NONE,
            output: TracingOutput::Json,
            redacted_fields: Vec::new(),
            redaction_text: "***REDACTED***".to_string(),
            enable_performance_tracing: false,
            performance_threshold_us: None,
            performance_directives: None,
        }
    }

    /// Returns a configuration optimized for performance analysis.
    ///
    /// This preset enables:
    /// - JSON output for machine-readable logs
    /// - Detailed span events (ENTER, EXIT, CLOSE)
    /// - Performance tracing enabled
    /// - No ANSI formatting
    /// - Debug-level directives for performance-critical crates
    pub fn for_performance() -> Self {
        Self {
            directives: Some("atlas_backends=debug,hologram_core=debug".to_string()),
            default_directive: "info".to_string(),
            include_targets: true,
            ansi: false,
            span_events: FmtSpan::ENTER | FmtSpan::EXIT | FmtSpan::CLOSE,
            output: TracingOutput::Json,
            redacted_fields: Vec::new(),
            redaction_text: "***REDACTED***".to_string(),
            enable_performance_tracing: true,
            performance_threshold_us: None,
            performance_directives: Some("atlas_backends=trace,hologram_core=trace".to_string()),
        }
    }

    /// Build a configuration using environment hints.
    ///
    /// # Environment Variables
    ///
    /// - `HOLOGRAM_TRACING_PROFILE` - Profile preset: `local` (default), `ci`, or `performance`
    /// - `HOLOGRAM_TRACING_DIRECTIVES` - Overrides tracing directives
    /// - `HOLOGRAM_TRACING_FORMAT` - Output format: `pretty`, `compact`, or `json`
    /// - `HOLOGRAM_TRACING_REDACT_FIELDS` - Comma-separated list of fields to redact
    /// - `HOLOGRAM_TRACING_REDACT_TOKEN` - Replacement text for redacted values
    /// - `HOLOGRAM_PERF_TRACING` - Enable/disable performance tracing: `true` or `false`
    /// - `HOLOGRAM_PERF_THRESHOLD_US` - Minimum duration (microseconds) to log
    /// - `HOLOGRAM_PERF_DIRECTIVES` - Performance-specific tracing directives
    pub fn from_env() -> Self {
        let profile = env::var("HOLOGRAM_TRACING_PROFILE")
            .unwrap_or_else(|_| "local".to_string())
            .to_ascii_lowercase();

        let mut config = match profile.as_str() {
            "ci" => Self::for_ci(),
            "performance" => Self::for_performance(),
            _ => Self::for_local(),
        };

        if let Ok(directives) = env::var("HOLOGRAM_TRACING_DIRECTIVES") {
            if !directives.trim().is_empty() {
                config.directives = Some(directives);
            }
        }

        if let Ok(format) = env::var("HOLOGRAM_TRACING_FORMAT") {
            if let Some(parsed) = TracingOutput::from_env_value(&format) {
                config.output = parsed;
                if matches!(config.output, TracingOutput::Json) {
                    config.ansi = false;
                }
            }
        }

        if let Ok(redacted) = env::var("HOLOGRAM_TRACING_REDACT_FIELDS") {
            let fields = redacted
                .split(',')
                .map(|field| field.trim())
                .filter(|field| !field.is_empty())
                .map(|field| field.to_string())
                .collect::<Vec<_>>();
            if !fields.is_empty() {
                config.redacted_fields = fields;
            }
        }

        if let Ok(token) = env::var("HOLOGRAM_TRACING_REDACT_TOKEN") {
            if !token.is_empty() {
                config.redaction_text = token;
            }
        }

        // Performance tracing configuration
        if let Ok(perf_tracing) = env::var("HOLOGRAM_PERF_TRACING") {
            config.enable_performance_tracing = perf_tracing.eq_ignore_ascii_case("true")
                || perf_tracing == "1"
                || perf_tracing.eq_ignore_ascii_case("yes");
        }

        if let Ok(threshold) = env::var("HOLOGRAM_PERF_THRESHOLD_US") {
            if let Ok(threshold_us) = threshold.parse::<u64>() {
                config.performance_threshold_us = Some(threshold_us);
            }
        }

        if let Ok(perf_directives) = env::var("HOLOGRAM_PERF_DIRECTIVES") {
            if !perf_directives.trim().is_empty() {
                config.performance_directives = Some(perf_directives);
            }
        }

        config
    }

    /// Resolve the `EnvFilter` to use for the subscriber.
    fn resolve_filter(&self) -> Result<EnvFilter, TracingSetupError> {
        if let Some(directives) = &self.directives {
            EnvFilter::try_new(directives).map_err(|err| TracingSetupError::InvalidFilter(err.to_string()))
        } else {
            match EnvFilter::try_from_default_env() {
                Ok(filter) => Ok(filter),
                Err(_) => Ok(EnvFilter::new(self.default_directive.clone())),
            }
        }
    }
}

/// Errors surfaced when configuring the shared tracing subscriber fails.
#[derive(Debug)]
pub enum TracingSetupError {
    /// The provided directive string could not be parsed.
    InvalidFilter(String),
    /// Installing the global subscriber failed (usually because one is
    /// already set).
    SubscriberInit(tracing_subscriber::util::TryInitError),
}

impl fmt::Display for TracingSetupError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TracingSetupError::InvalidFilter(msg) => {
                write!(f, "invalid tracing directive: {msg}")
            }
            TracingSetupError::SubscriberInit(err) => {
                write!(f, "failed to install global tracing subscriber: {err}")
            }
        }
    }
}

impl Error for TracingSetupError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            TracingSetupError::SubscriberInit(err) => Some(err),
            _ => None,
        }
    }
}

/// Build a `tracing` subscriber using the provided configuration.
pub fn build_subscriber(config: &TracingConfig) -> Result<impl Subscriber + Send + Sync, TracingSetupError> {
    let (filter, fmt_layer) = subscriber_layers(config)?;
    Ok(Registry::default().with(fmt_layer).with(filter))
}

/// Build the filter and formatting layers for external composition.
pub fn subscriber_layers(
    config: &TracingConfig,
) -> Result<(EnvFilter, Box<dyn Layer<Registry> + Send + Sync>), TracingSetupError> {
    let filter = config.resolve_filter()?;
    let span_events = config.span_events.clone();
    let include_targets = config.include_targets;
    let ansi = config.ansi;
    let redacted_fields: Arc<HashSet<String>> = Arc::new(config.redacted_fields.iter().cloned().collect());
    let redaction_text = Arc::new(config.redaction_text.clone());
    let redaction_enabled = !redacted_fields.is_empty();

    let layer: Box<dyn Layer<Registry> + Send + Sync> = match config.output {
        TracingOutput::Compact => {
            let layer = tracing_fmt::layer()
                .with_target(include_targets)
                .with_ansi(ansi)
                .with_span_events(span_events);
            if redaction_enabled {
                Box::new(layer.fmt_fields(TextRedactingFields::new(
                    Arc::clone(&redacted_fields),
                    Arc::clone(&redaction_text),
                )))
            } else {
                Box::new(layer)
            }
        }
        TracingOutput::Pretty => {
            let layer = tracing_fmt::layer()
                .pretty()
                .with_target(include_targets)
                .with_ansi(ansi)
                .with_span_events(span_events);
            if redaction_enabled {
                Box::new(layer.fmt_fields(TextRedactingFields::new(
                    Arc::clone(&redacted_fields),
                    Arc::clone(&redaction_text),
                )))
            } else {
                Box::new(layer)
            }
        }
        TracingOutput::Json => {
            let layer = tracing_fmt::layer()
                .json()
                .with_target(include_targets)
                .with_span_events(span_events)
                .with_ansi(false);
            if redaction_enabled {
                Box::new(layer.fmt_fields(JsonRedactingFields::new(
                    Arc::clone(&redacted_fields),
                    Arc::clone(&redaction_text),
                )))
            } else {
                Box::new(layer)
            }
        }
    };

    Ok((filter, layer))
}

/// Install the configured subscriber as the process-wide default.
pub fn init_global_tracing(config: &TracingConfig) -> Result<(), TracingSetupError> {
    build_subscriber(config)?
        .try_init()
        .map_err(TracingSetupError::SubscriberInit)
}

#[derive(Clone)]
struct TextRedactingFields {
    redacted: Arc<HashSet<String>>,
    replacement: Arc<String>,
}

impl TextRedactingFields {
    fn new(redacted: Arc<HashSet<String>>, replacement: Arc<String>) -> Self {
        Self { redacted, replacement }
    }
}

impl<'writer> tracing_subscriber::fmt::FormatFields<'writer> for TextRedactingFields {
    fn format_fields<R>(&self, mut writer: tracing_subscriber::fmt::format::Writer<'writer>, fields: R) -> fmt::Result
    where
        R: RecordFields,
    {
        let mut collector = TextFieldCollector {
            entries: Vec::new(),
            redacted: &self.redacted,
            replacement: self.replacement.as_str(),
        };
        fields.record(&mut collector);

        for (index, (key, value)) in collector.entries.into_iter().enumerate() {
            if index > 0 {
                writer.write_char(' ')?;
            }
            writer.write_str(&key)?;
            writer.write_char('=')?;
            writer.write_str(&value)?;
        }

        Ok(())
    }
}

struct TextFieldCollector<'a> {
    entries: Vec<(String, String)>,
    redacted: &'a HashSet<String>,
    replacement: &'a str,
}

impl<'a> TextFieldCollector<'a> {
    fn is_redacted(&self, field: &tracing::field::Field) -> bool {
        self.redacted.contains(field.name())
    }

    fn push_redacted(&mut self, field: &tracing::field::Field) {
        self.entries
            .push((field.name().to_string(), format!("{:?}", self.replacement)));
    }

    fn push_value(&mut self, field: &tracing::field::Field, value: String) {
        self.entries.push((field.name().to_string(), value));
    }
}

impl<'a> tracing::field::Visit for TextFieldCollector<'a> {
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn fmt::Debug) {
        if self.is_redacted(field) {
            self.push_redacted(field);
        } else {
            self.push_value(field, format!("{:?}", value));
        }
    }

    fn record_i64(&mut self, field: &tracing::field::Field, value: i64) {
        if self.is_redacted(field) {
            self.push_redacted(field);
        } else {
            self.push_value(field, value.to_string());
        }
    }

    fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
        if self.is_redacted(field) {
            self.push_redacted(field);
        } else {
            self.push_value(field, value.to_string());
        }
    }

    fn record_u128(&mut self, field: &tracing::field::Field, value: u128) {
        if self.is_redacted(field) {
            self.push_redacted(field);
        } else {
            self.push_value(field, value.to_string());
        }
    }

    fn record_i128(&mut self, field: &tracing::field::Field, value: i128) {
        if self.is_redacted(field) {
            self.push_redacted(field);
        } else {
            self.push_value(field, value.to_string());
        }
    }

    fn record_bool(&mut self, field: &tracing::field::Field, value: bool) {
        if self.is_redacted(field) {
            self.push_redacted(field);
        } else {
            self.push_value(field, value.to_string());
        }
    }

    fn record_f64(&mut self, field: &tracing::field::Field, value: f64) {
        if self.is_redacted(field) {
            self.push_redacted(field);
        } else {
            self.push_value(field, value.to_string());
        }
    }

    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        if self.is_redacted(field) {
            self.push_redacted(field);
        } else {
            self.push_value(field, format!("{:?}", value));
        }
    }

    fn record_error(&mut self, field: &tracing::field::Field, value: &(dyn Error + 'static)) {
        if self.is_redacted(field) {
            self.push_redacted(field);
        } else {
            self.push_value(field, value.to_string());
        }
    }
}

#[derive(Clone)]
struct JsonRedactingFields {
    redacted: Arc<HashSet<String>>,
    replacement: Arc<String>,
}

impl JsonRedactingFields {
    fn new(redacted: Arc<HashSet<String>>, replacement: Arc<String>) -> Self {
        Self { redacted, replacement }
    }
}

impl<'writer> tracing_subscriber::fmt::FormatFields<'writer> for JsonRedactingFields {
    fn format_fields<R>(&self, mut writer: tracing_subscriber::fmt::format::Writer<'writer>, fields: R) -> fmt::Result
    where
        R: RecordFields,
    {
        let mut collector = JsonFieldCollector {
            entries: Vec::new(),
            redacted: &self.redacted,
            replacement: self.replacement.as_str(),
        };
        fields.record(&mut collector);

        let mut object = JsonMap::with_capacity(collector.entries.len());
        for (key, value) in collector.entries {
            object.insert(key, value);
        }

        let json_value = JsonValue::Object(object);
        let serialized = serde_json::to_string(&json_value).map_err(|_| fmt::Error)?;

        writer.write_str(&serialized)
    }
}

struct JsonFieldCollector<'a> {
    entries: Vec<(String, JsonValue)>,
    redacted: &'a HashSet<String>,
    replacement: &'a str,
}

impl<'a> JsonFieldCollector<'a> {
    fn insert_value(&mut self, field: &tracing::field::Field, value: JsonValue) {
        if self.redacted.contains(field.name()) {
            self.entries.push((
                field.name().to_string(),
                JsonValue::String(self.replacement.to_string()),
            ));
        } else {
            self.entries.push((field.name().to_string(), value));
        }
    }

    fn insert_number<N>(&mut self, field: &tracing::field::Field, number: N)
    where
        N: Into<JsonNumber>,
    {
        let value = JsonValue::Number(number.into());
        self.insert_value(field, value);
    }

    fn insert_string(&mut self, field: &tracing::field::Field, value: String) {
        self.insert_value(field, JsonValue::String(value));
    }
}

impl<'a> tracing::field::Visit for JsonFieldCollector<'a> {
    fn record_debug(&mut self, field: &tracing::field::Field, value: &dyn fmt::Debug) {
        self.insert_string(field, format!("{:?}", value));
    }

    fn record_i64(&mut self, field: &tracing::field::Field, value: i64) {
        self.insert_number(field, value);
    }

    fn record_u64(&mut self, field: &tracing::field::Field, value: u64) {
        self.insert_number(field, value);
    }

    fn record_u128(&mut self, field: &tracing::field::Field, value: u128) {
        self.insert_string(field, value.to_string());
    }

    fn record_i128(&mut self, field: &tracing::field::Field, value: i128) {
        self.insert_string(field, value.to_string());
    }

    fn record_bool(&mut self, field: &tracing::field::Field, value: bool) {
        self.insert_value(field, JsonValue::Bool(value));
    }

    fn record_f64(&mut self, field: &tracing::field::Field, value: f64) {
        let json_value = JsonNumber::from_f64(value)
            .map(JsonValue::Number)
            .unwrap_or_else(|| JsonValue::String(value.to_string()));
        self.insert_value(field, json_value);
    }

    fn record_str(&mut self, field: &tracing::field::Field, value: &str) {
        self.insert_string(field, value.to_string());
    }

    fn record_error(&mut self, field: &tracing::field::Field, value: &(dyn Error + 'static)) {
        self.insert_string(field, value.to_string());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    // Mutex to serialize environment variable tests and prevent race conditions.
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    fn reset_env(keys: &[&str]) {
        for key in keys {
            env::remove_var(key);
        }
    }

    #[test]
    fn rejects_invalid_directive() {
        let _guard = ENV_LOCK.lock().unwrap();
        reset_env(&["HOLOGRAM_TRACING_DIRECTIVES", "RUST_LOG"]);
        let config = TracingConfig {
            directives: Some("=::invalid".to_string()),
            ..TracingConfig::default()
        };
        let result = build_subscriber(&config);
        assert!(matches!(result, Err(TracingSetupError::InvalidFilter(_))));
    }

    #[test]
    fn builds_with_defaults() {
        let _guard = ENV_LOCK.lock().unwrap();
        reset_env(&[]);
        let config = TracingConfig::default();
        assert!(build_subscriber(&config).is_ok());
    }

    #[test]
    fn from_env_respects_profile_and_format() {
        let _guard = ENV_LOCK.lock().unwrap();
        reset_env(&[
            "HOLOGRAM_TRACING_PROFILE",
            "HOLOGRAM_TRACING_FORMAT",
            "HOLOGRAM_TRACING_DIRECTIVES",
            "HOLOGRAM_TRACING_REDACT_FIELDS",
            "HOLOGRAM_TRACING_REDACT_TOKEN",
        ]);

        env::set_var("HOLOGRAM_TRACING_PROFILE", "ci");
        env::set_var("HOLOGRAM_TRACING_FORMAT", "compact");
        env::set_var("HOLOGRAM_TRACING_DIRECTIVES", "atlas=debug");
        env::set_var("HOLOGRAM_TRACING_REDACT_FIELDS", "secret,password");
        env::set_var("HOLOGRAM_TRACING_REDACT_TOKEN", "[filtered]");

        let config = TracingConfig::from_env();
        assert_eq!(config.directives.as_deref(), Some("atlas=debug"));
        assert!(!config.ansi);
        assert!(matches!(config.output, TracingOutput::Compact));
        assert_eq!(config.redacted_fields, vec!["secret", "password"]);
        assert_eq!(config.redaction_text, "[filtered]");
    }

    #[test]
    fn from_env_respects_performance_settings() {
        let _guard = ENV_LOCK.lock().unwrap();
        reset_env(&[
            "HOLOGRAM_TRACING_PROFILE",
            "HOLOGRAM_PERF_TRACING",
            "HOLOGRAM_PERF_THRESHOLD_US",
            "HOLOGRAM_PERF_DIRECTIVES",
        ]);

        env::set_var("HOLOGRAM_PERF_TRACING", "true");
        env::set_var("HOLOGRAM_PERF_THRESHOLD_US", "1000");
        env::set_var("HOLOGRAM_PERF_DIRECTIVES", "atlas_backends=trace");

        let config = TracingConfig::from_env();
        assert!(config.enable_performance_tracing);
        assert_eq!(config.performance_threshold_us, Some(1000));
        assert_eq!(config.performance_directives.as_deref(), Some("atlas_backends=trace"));
    }

    #[test]
    fn for_performance_preset() {
        let config = TracingConfig::for_performance();
        assert!(config.enable_performance_tracing);
        assert!(matches!(config.output, TracingOutput::Json));
        assert!(!config.ansi);
        assert!(config.directives.is_some());
        assert!(config.performance_directives.is_some());
    }

    #[test]
    fn performance_profile_from_env() {
        let _guard = ENV_LOCK.lock().unwrap();
        reset_env(&[
            "HOLOGRAM_TRACING_PROFILE",
            "HOLOGRAM_TRACING_FORMAT",
            "HOLOGRAM_PERF_TRACING",
            "HOLOGRAM_PERF_THRESHOLD_US",
            "HOLOGRAM_PERF_DIRECTIVES",
        ]);

        env::set_var("HOLOGRAM_TRACING_PROFILE", "performance");
        let config = TracingConfig::from_env();
        assert!(config.enable_performance_tracing);
        assert!(matches!(config.output, TracingOutput::Json));
    }
}

/// Output format choices for the tracing formatter layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TracingOutput {
    Compact,
    Pretty,
    Json,
}

impl TracingOutput {
    fn from_env_value(value: &str) -> Option<Self> {
        match value.trim().to_ascii_lowercase().as_str() {
            "compact" => Some(Self::Compact),
            "pretty" => Some(Self::Pretty),
            "json" => Some(Self::Json),
            _ => None,
        }
    }
}
