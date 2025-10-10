//! Data Export Utilities
//!
//! This module provides common export functionality for visualization data,
//! supporting multiple standard formats.
//!
//! # Supported Formats
//!
//! - **`GraphML`**: XML-based graph format
//! - **JSON**: `JavaScript` Object Notation
//! - **CSV**: Comma-Separated Values
//! - **DOT**: Graphviz format
//! - **SVG**: Scalable Vector Graphics
//!
//! # Examples
//!
//! ```rust
//! use atlas_embeddings::visualization::export::{ExportFormat, Exporter};
//!
//! let formats = ExportFormat::all();
//! assert_eq!(formats.len(), 5);
//! ```

/// Supported export formats
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExportFormat {
    /// `GraphML` XML format (for graph tools)
    GraphML,
    /// JSON format (for web visualizations)
    Json,
    /// CSV format (for data analysis)
    Csv,
    /// DOT format (for Graphviz)
    Dot,
    /// SVG format (for vector graphics)
    Svg,
}

impl ExportFormat {
    /// Get all supported export formats
    #[must_use]
    pub fn all() -> Vec<Self> {
        vec![Self::GraphML, Self::Json, Self::Csv, Self::Dot, Self::Svg]
    }

    /// Get file extension for this format
    #[must_use]
    pub const fn extension(&self) -> &str {
        match self {
            Self::GraphML => "graphml",
            Self::Json => "json",
            Self::Csv => "csv",
            Self::Dot => "dot",
            Self::Svg => "svg",
        }
    }

    /// Get MIME type for this format
    #[must_use]
    pub const fn mime_type(&self) -> &str {
        match self {
            Self::GraphML => "application/xml",
            Self::Json => "application/json",
            Self::Csv => "text/csv",
            Self::Dot => "text/vnd.graphviz",
            Self::Svg => "image/svg+xml",
        }
    }
}

/// Generic exporter trait
///
/// Implement this trait to add export capabilities to visualization types.
pub trait Exporter {
    /// Export to the specified format
    ///
    /// # Errors
    ///
    /// Returns `ExportError` if the format is unsupported, serialization fails,
    /// or the data is invalid.
    fn export(&self, format: ExportFormat) -> Result<String, ExportError>;

    /// Export to all supported formats
    fn export_all(&self) -> Vec<(ExportFormat, Result<String, ExportError>)> {
        ExportFormat::all().into_iter().map(|fmt| (fmt, self.export(fmt))).collect()
    }
}

/// Errors that can occur during export
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExportError {
    /// The requested format is not supported for this data type
    UnsupportedFormat(ExportFormat),
    /// An error occurred during serialization
    SerializationError(String),
    /// The data is invalid or incomplete
    InvalidData(String),
}

impl std::fmt::Display for ExportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedFormat(fmt) => {
                write!(f, "Unsupported export format: {fmt:?}")
            },
            Self::SerializationError(msg) => {
                write!(f, "Serialization error: {msg}")
            },
            Self::InvalidData(msg) => {
                write!(f, "Invalid data: {msg}")
            },
        }
    }
}

impl std::error::Error for ExportError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_export_format_all() {
        let formats = ExportFormat::all();
        assert_eq!(formats.len(), 5);
        assert!(formats.contains(&ExportFormat::GraphML));
        assert!(formats.contains(&ExportFormat::Json));
        assert!(formats.contains(&ExportFormat::Csv));
        assert!(formats.contains(&ExportFormat::Dot));
        assert!(formats.contains(&ExportFormat::Svg));
    }

    #[test]
    fn test_export_format_extension() {
        assert_eq!(ExportFormat::GraphML.extension(), "graphml");
        assert_eq!(ExportFormat::Json.extension(), "json");
        assert_eq!(ExportFormat::Csv.extension(), "csv");
        assert_eq!(ExportFormat::Dot.extension(), "dot");
        assert_eq!(ExportFormat::Svg.extension(), "svg");
    }

    #[test]
    fn test_export_format_mime_type() {
        assert_eq!(ExportFormat::GraphML.mime_type(), "application/xml");
        assert_eq!(ExportFormat::Json.mime_type(), "application/json");
        assert_eq!(ExportFormat::Csv.mime_type(), "text/csv");
        assert_eq!(ExportFormat::Dot.mime_type(), "text/vnd.graphviz");
        assert_eq!(ExportFormat::Svg.mime_type(), "image/svg+xml");
    }

    #[test]
    fn test_export_error_display() {
        let err = ExportError::UnsupportedFormat(ExportFormat::Svg);
        assert!(err.to_string().contains("Unsupported"));

        let err = ExportError::SerializationError("test".to_string());
        assert!(err.to_string().contains("Serialization"));

        let err = ExportError::InvalidData("test".to_string());
        assert!(err.to_string().contains("Invalid"));
    }
}
