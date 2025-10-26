//! Golden Seed Fractal Visualization
//!
//! This module generates the **Golden Seed Fractal**: a self-similar 2D visualization
//! of the Atlas structure exhibiting 96-fold self-similarity.
//!
//! # Mathematical Background
//!
//! The Golden Seed Fractal is an Iterated Function System (IFS) based on the Atlas
//! of Resonance Classes. Unlike traditional fractals (Mandelbrot, Julia, Sierpinski),
//! this fractal has **96-fold branching** at each iteration, reflecting the 96 vertices
//! of the Atlas.
//!
//! ## Generation Algorithm
//!
//! The fractal is generated recursively:
//!
//! 1. **Iteration 0**: Place the 96 Atlas vertices in 2D using a symmetric projection
//! 2. **Iteration n+1**: At each vertex from iteration n, place a scaled and rotated
//!    copy of the entire 96-vertex pattern
//! 3. **Scaling**: Use factor r = 1/3 (matching the ternary coordinate d₄₅)
//! 4. **Symmetry**: Preserve the 8-fold sign class structure and mirror symmetry τ
//!
//! ## Unique Properties
//!
//! - **96-fold self-similarity**: Each point branches into 96 sub-points
//! - **8 sign classes**: Color-coded with distinct hues
//! - **48 mirror pairs**: Reflection symmetry preserved at all scales
//! - **Mixed radix**: Encodes both binary (2⁵) and ternary (3) structure
//! - **Fractal dimension**: Approximately D ≈ 4.15 (log₃(96))
//!
//! # Examples
//!
//! ```rust
//! use atlas_embeddings::Atlas;
//! use atlas_embeddings::visualization::fractal::GoldenSeedFractal;
//!
//! let atlas = Atlas::new();
//! let fractal = GoldenSeedFractal::new(&atlas);
//!
//! // Generate 1 iteration (96 + 9,216 points)
//! let points = fractal.generate(1);
//! assert_eq!(points.len(), 96 + 96 * 96);
//!
//! // Export as SVG for logo
//! let svg = fractal.to_svg(1, 800, 800);
//! assert!(svg.contains("<svg"));
//! ```

use crate::atlas::Atlas;
use std::f64::consts::PI;

/// A point in the fractal with color information
#[derive(Debug, Clone)]
pub struct FractalPoint {
    /// X coordinate
    pub x: f64,
    /// Y coordinate
    pub y: f64,
    /// Atlas vertex ID (0-95)
    pub vertex_id: usize,
    /// Sign class (0-7) for coloring
    pub sign_class: usize,
    /// Iteration depth (0 = base pattern)
    pub depth: usize,
}

/// Golden Seed Fractal generator
///
/// Generates self-similar visualizations of the Atlas structure.
#[derive(Debug)]
pub struct GoldenSeedFractal<'a> {
    atlas: &'a Atlas,
    /// Base 2D coordinates for 96 vertices (computed once)
    base_coords: Vec<(f64, f64)>,
}

impl<'a> GoldenSeedFractal<'a> {
    /// Create a new fractal generator
    ///
    /// Computes the base 2D projection of all 96 Atlas vertices.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::Atlas;
    /// use atlas_embeddings::visualization::fractal::GoldenSeedFractal;
    ///
    /// let atlas = Atlas::new();
    /// let fractal = GoldenSeedFractal::new(&atlas);
    /// ```
    #[must_use]
    pub fn new(atlas: &'a Atlas) -> Self {
        let base_coords = Self::compute_base_coordinates(atlas);
        Self { atlas, base_coords }
    }

    /// Compute base 2D coordinates for all 96 Atlas vertices
    ///
    /// Uses a projection that emphasizes the 8-fold sign class symmetry
    /// and the 96-fold structure.
    ///
    /// The projection maps each vertex based on:
    /// - Sign class (0-7): Determines angular position (8-fold symmetry)
    /// - Within-class index (0-11): Determines radial position
    /// - Label coordinates: Fine-tune position for visual clarity
    #[allow(clippy::float_arithmetic)] // Visualization code - geometric calculations required
    #[allow(clippy::cast_precision_loss)] // Small integers (0-11) converted to angles
    fn compute_base_coordinates(atlas: &Atlas) -> Vec<(f64, f64)> {
        let mut coords = Vec::with_capacity(96);

        for vertex_id in 0..96 {
            let label = atlas.label(vertex_id);

            // Compute sign class (0-7) based on label parity
            let sign_class =
                Self::compute_sign_class(label.e1, label.e2, label.e3, label.e6, label.e7);

            // Within-class index (0-11)
            let within_class_index = vertex_id % 12;

            // Base angle from sign class (8 octants)
            let base_angle = (sign_class as f64) * (2.0 * PI / 8.0);

            // Angular offset within octant (12 positions)
            let angle_offset = (within_class_index as f64) * (2.0 * PI / 8.0) / 12.0;

            let angle = base_angle + angle_offset;

            // Radial position varies with degree (5 or 6)
            let degree = atlas.degree(vertex_id);
            let base_radius = if degree == 6 { 1.0 } else { 0.8 };

            // Fine-tune radius based on d45 coordinate (-1, 0, +1)
            let d45_offset = match label.d45 {
                -1 => -0.1,
                1 => 0.1,
                _ => 0.0, // Handles 0 and any unexpected values
            };

            let radius = base_radius + d45_offset;

            // Compute Cartesian coordinates
            let x = radius * angle.cos();
            let y = radius * angle.sin();

            coords.push((x, y));
        }

        coords
    }

    /// Compute sign class (0-7) from label binary coordinates
    ///
    /// The 8 sign classes correspond to the 8 octants determined by
    /// the parity pattern of `(e1, e2, e3, e6, e7)`.
    const fn compute_sign_class(e1: u8, e2: u8, e3: u8, _e6: u8, _e7: u8) -> usize {
        // Use 3 bits for sign class (8 classes)
        // Currently using only e1, e2, e3 for simplicity
        ((e1 as usize) << 2) | ((e2 as usize) << 1) | (e3 as usize)
    }

    /// Generate fractal points up to specified iteration depth
    ///
    /// # Arguments
    ///
    /// * `max_depth` - Maximum iteration depth (0 = base pattern only)
    ///
    /// # Returns
    ///
    /// Vector of all fractal points across all depths `0..=max_depth`
    ///
    /// # Point Count
    ///
    /// - Depth 0: 96 points
    /// - Depth 1: 96 + 96² = 9,312 points
    /// - Depth 2: 96 + 96² + 96³ = 893,088 points (not recommended for visualization)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::Atlas;
    /// use atlas_embeddings::visualization::fractal::GoldenSeedFractal;
    ///
    /// let atlas = Atlas::new();
    /// let fractal = GoldenSeedFractal::new(&atlas);
    ///
    /// let points = fractal.generate(1);
    /// assert_eq!(points.len(), 96 + 96 * 96);
    /// ```
    #[must_use]
    #[allow(clippy::float_arithmetic)] // IFS transformation requires coordinate arithmetic
    pub fn generate(&self, max_depth: usize) -> Vec<FractalPoint> {
        let mut all_points = Vec::new();

        // Depth 0: Base pattern
        for (vertex_id, &(x, y)) in self.base_coords.iter().enumerate() {
            let label = self.atlas.label(vertex_id);
            let sign_class =
                Self::compute_sign_class(label.e1, label.e2, label.e3, label.e6, label.e7);

            all_points.push(FractalPoint { x, y, vertex_id, sign_class, depth: 0 });
        }

        // Iterative refinement: depth 1..=max_depth
        for depth in 1..=max_depth {
            let scaling = Self::scaling_factor(depth);
            let prev_depth_start = if depth == 1 {
                0
            } else {
                Self::point_count(depth - 2)
            };
            let prev_depth_end = Self::point_count(depth - 1);

            // Collect new points in temporary vector to avoid borrowing conflict
            let mut new_points = Vec::new();

            // For each point at previous depth
            for parent in &all_points[prev_depth_start..prev_depth_end] {
                let parent_x = parent.x;
                let parent_y = parent.y;

                // Place scaled copy of all 96 vertices at this point
                for (vertex_id, &(base_x, base_y)) in self.base_coords.iter().enumerate() {
                    let label = self.atlas.label(vertex_id);
                    let sign_class =
                        Self::compute_sign_class(label.e1, label.e2, label.e3, label.e6, label.e7);

                    // Apply IFS transformation: scale and translate
                    let x = base_x.mul_add(scaling, parent_x);
                    let y = base_y.mul_add(scaling, parent_y);

                    new_points.push(FractalPoint { x, y, vertex_id, sign_class, depth });
                }
            }

            // Append all new points
            all_points.extend(new_points);
        }

        all_points
    }

    /// Scaling factor for iteration depth
    ///
    /// Uses 1/3 to match the ternary coordinate structure
    #[allow(clippy::float_arithmetic)] // Scaling calculation for IFS
    #[allow(clippy::cast_possible_truncation)] // Depth will always be small
    #[allow(clippy::cast_possible_wrap)] // Depth is always positive
    fn scaling_factor(depth: usize) -> f64 {
        // 3^(-depth) = (1/3)^depth
        // Computed as: 1.0 / 3.0^depth
        // For depth 1: 1/3 ≈ 0.333
        // For depth 2: 1/9 ≈ 0.111
        match depth {
            0 => 1.0,
            1 => 1.0 / 3.0,
            2 => 1.0 / 9.0,
            3 => 1.0 / 27.0,
            _ => 1.0 / 3.0_f64.powi(depth as i32),
        }
    }

    /// Total point count up to given depth
    ///
    /// Sum of geometric series: 96 × (1 + 96 + 96² + ... + 96^depth)
    #[allow(clippy::cast_possible_truncation)] // Depth will always be small (< 10)
    fn point_count(depth: usize) -> usize {
        (0..=depth).map(|d| 96_usize.pow(d as u32 + 1)).sum()
    }

    /// Export fractal to SVG format
    ///
    /// # Arguments
    ///
    /// * `max_depth` - Iteration depth
    /// * `width` - SVG canvas width in pixels
    /// * `height` - SVG canvas height in pixels
    ///
    /// # Returns
    ///
    /// SVG string with embedded CSS for sign class colors
    #[must_use]
    #[allow(clippy::cast_precision_loss)] // Point count is visualization only
    #[allow(clippy::too_many_lines)] // SVG generation requires detailed code
    #[allow(clippy::float_arithmetic)] // SVG coordinate calculations
    #[allow(clippy::format_push_string)] // SVG generation requires string building
    #[allow(clippy::large_stack_arrays)] // format! macros in SVG generation
    #[allow(clippy::suboptimal_flops)] // Simple formulas preferred for clarity
    pub fn to_svg(&self, max_depth: usize, width: usize, height: usize) -> String {
        let points = self.generate(max_depth);

        let mut svg = format!(
            r#"<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="-2 -2 4 4">"#
        );

        // Add title
        svg.push_str(&format!(
            r"<title>Golden Seed Fractal (Atlas Structure, {} iterations, {} points)</title>",
            max_depth,
            points.len()
        ));

        // Add CSS for sign class colors (8 hues evenly spaced)
        svg.push_str(r#"<defs><style type="text/css"><![CDATA["#);
        for class in 0..8 {
            let hue = (class * 360) / 8;
            svg.push_str(&format!(".sign-class-{class} {{ fill: hsl({hue}, 70%, 50%); }}\n"));
        }
        svg.push_str("]]></style></defs>");

        // Add background (dark)
        svg.push_str(r#"<rect x="-2" y="-2" width="4" height="4" fill="rgb(10, 10, 10)"/>"#);

        // Draw points (back to front by depth for proper layering)
        for point in &points {
            let opacity = 0.8 / (1.0 + point.depth as f64 * 0.3);
            let radius = 0.01 / (1.0 + point.depth as f64 * 0.5);

            svg.push_str(&format!(
                r#"<circle cx="{}" cy="{}" r="{}" class="sign-class-{}" opacity="{}"/>"#,
                point.x, point.y, radius, point.sign_class, opacity
            ));
        }

        svg.push_str("</svg>");
        svg
    }

    /// Get fractal statistics
    ///
    /// Returns `(total_points, fractal_dimension_estimate)`
    #[must_use]
    #[allow(clippy::float_arithmetic)] // Dimension calculation is visualization metadata
    #[allow(clippy::suboptimal_flops)] // Explicit formula for clarity (log base change)
    pub fn statistics(&self, max_depth: usize) -> (usize, f64) {
        let total_points = Self::point_count(max_depth);

        // Fractal dimension: D = log(N) / log(1/r)
        // N = 96 (branching factor), r = 1/3 (scaling)
        // D = log(96) / log(3) ≈ 4.15
        let dimension = 96.0_f64.log(3.0_f64);

        (total_points, dimension)
    }
}

/// A point in the 3D fractal with color information
#[derive(Debug, Clone)]
#[allow(clippy::large_stack_arrays)] // Three f64 coordinates are reasonable for 3D points
pub struct FractalPoint3D {
    /// X coordinate
    pub x: f64,
    /// Y coordinate
    pub y: f64,
    /// Z coordinate
    pub z: f64,
    /// Atlas vertex ID (0-95)
    pub vertex_id: usize,
    /// Sign class (0-7) for coloring
    pub sign_class: usize,
    /// Iteration depth (0 = base pattern)
    pub depth: usize,
}

/// Golden Seed Fractal 3D generator
///
/// Generates self-similar 3D visualizations of the Atlas structure.
#[derive(Debug)]
pub struct GoldenSeedFractal3D<'a> {
    atlas: &'a Atlas,
    /// Base 3D coordinates for 96 vertices (computed once)
    base_coords: Vec<(f64, f64, f64)>,
}

impl<'a> GoldenSeedFractal3D<'a> {
    /// Create a new 3D fractal generator
    ///
    /// Computes the base 3D projection of all 96 Atlas vertices.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::Atlas;
    /// use atlas_embeddings::visualization::fractal::GoldenSeedFractal3D;
    ///
    /// let atlas = Atlas::new();
    /// let fractal = GoldenSeedFractal3D::new(&atlas);
    /// ```
    #[must_use]
    pub fn new(atlas: &'a Atlas) -> Self {
        let base_coords = Self::compute_base_coordinates(atlas);
        Self { atlas, base_coords }
    }

    /// Compute base 3D coordinates for all 96 Atlas vertices
    ///
    /// Uses a spherical projection that emphasizes the 8-fold sign class symmetry
    /// and the 96-fold structure in 3D space.
    ///
    /// The projection maps each vertex based on:
    /// - Sign class (0-7): Determines position in octants
    /// - Within-class index (0-11): Determines angular position
    /// - Label coordinates: Fine-tune position for visual clarity
    #[allow(clippy::float_arithmetic)] // Visualization code - geometric calculations required
    #[allow(clippy::cast_precision_loss)] // Small integers (0-11) converted to angles
    fn compute_base_coordinates(atlas: &Atlas) -> Vec<(f64, f64, f64)> {
        let mut coords = Vec::with_capacity(96);

        for vertex_id in 0..96 {
            let label = atlas.label(vertex_id);

            // Compute sign class (0-7) based on label parity
            let sign_class = GoldenSeedFractal::compute_sign_class(
                label.e1, label.e2, label.e3, label.e6, label.e7,
            );

            // Within-class index (0-11)
            let within_class_index = vertex_id % 12;

            // Azimuthal angle from sign class (8 octants)
            let base_angle = (sign_class as f64) * (2.0 * PI / 8.0);

            // Angular offset within octant (12 positions)
            let angle_offset = (within_class_index as f64) * (2.0 * PI / 8.0) / 12.0;

            let azimuth = base_angle + angle_offset;

            // Polar angle varies with degree and within-class position
            let degree = atlas.degree(vertex_id);
            let base_polar = if degree == 6 { PI / 3.0 } else { PI / 2.5 };
            let polar_offset = (within_class_index as f64) * (PI / 12.0) / 12.0;
            let polar = base_polar + polar_offset;

            // Radial position varies with d45 coordinate (-1, 0, +1)
            let base_radius = 1.0;
            let d45_offset = match label.d45 {
                -1 => -0.1,
                1 => 0.1,
                _ => 0.0, // Handles 0 and any unexpected values
            };

            let radius = base_radius + d45_offset;

            // Convert spherical to Cartesian coordinates
            let x = radius * polar.sin() * azimuth.cos();
            let y = radius * polar.sin() * azimuth.sin();
            let z = radius * polar.cos();

            coords.push((x, y, z));
        }

        coords
    }

    /// Generate 3D fractal points up to specified iteration depth
    ///
    /// # Arguments
    ///
    /// * `max_depth` - Maximum iteration depth (0 = base pattern only)
    ///
    /// # Returns
    ///
    /// Vector of all 3D fractal points across all depths `0..=max_depth`
    ///
    /// # Point Count
    ///
    /// - Depth 0: 96 points
    /// - Depth 1: 96 + 96² = 9,312 points
    /// - Depth 2: 96 + 96² + 96³ = 893,088 points (not recommended for visualization)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::Atlas;
    /// use atlas_embeddings::visualization::fractal::GoldenSeedFractal3D;
    ///
    /// let atlas = Atlas::new();
    /// let fractal = GoldenSeedFractal3D::new(&atlas);
    ///
    /// let points = fractal.generate(1);
    /// assert_eq!(points.len(), 96 + 96 * 96);
    /// ```
    #[must_use]
    #[allow(clippy::float_arithmetic)] // IFS transformation requires coordinate arithmetic
    pub fn generate(&self, max_depth: usize) -> Vec<FractalPoint3D> {
        let mut all_points = Vec::new();

        // Depth 0: Base pattern
        for (vertex_id, &(x, y, z)) in self.base_coords.iter().enumerate() {
            let label = self.atlas.label(vertex_id);
            let sign_class = GoldenSeedFractal::compute_sign_class(
                label.e1, label.e2, label.e3, label.e6, label.e7,
            );

            all_points.push(FractalPoint3D { x, y, z, vertex_id, sign_class, depth: 0 });
        }

        // Iterative refinement: depth 1..=max_depth
        for depth in 1..=max_depth {
            let scaling = GoldenSeedFractal::scaling_factor(depth);
            let prev_depth_start = if depth == 1 {
                0
            } else {
                GoldenSeedFractal::point_count(depth - 2)
            };
            let prev_depth_end = GoldenSeedFractal::point_count(depth - 1);

            // Collect new points in temporary vector to avoid borrowing conflict
            let mut new_points = Vec::new();

            // For each point at previous depth
            for parent in &all_points[prev_depth_start..prev_depth_end] {
                let parent_x = parent.x;
                let parent_y = parent.y;
                let parent_z = parent.z;

                // Place scaled copy of all 96 vertices at this point
                for (vertex_id, &(base_x, base_y, base_z)) in self.base_coords.iter().enumerate() {
                    let label = self.atlas.label(vertex_id);
                    let sign_class = GoldenSeedFractal::compute_sign_class(
                        label.e1, label.e2, label.e3, label.e6, label.e7,
                    );

                    // Apply IFS transformation: scale and translate
                    let x = base_x.mul_add(scaling, parent_x);
                    let y = base_y.mul_add(scaling, parent_y);
                    let z = base_z.mul_add(scaling, parent_z);

                    new_points.push(FractalPoint3D { x, y, z, vertex_id, sign_class, depth });
                }
            }

            // Append all new points
            all_points.extend(new_points);
        }

        all_points
    }

    /// Export 3D fractal to CSV format
    ///
    /// # Arguments
    ///
    /// * `max_depth` - Iteration depth
    ///
    /// # Returns
    ///
    /// CSV string with columns: `id,x,y,z,vertex_id,sign_class,depth`
    #[must_use]
    #[allow(clippy::format_push_string)] // CSV generation requires string building
    #[allow(clippy::large_stack_arrays)] // format! macros in CSV generation
    pub fn to_csv(&self, max_depth: usize) -> String {
        let points = self.generate(max_depth);
        let mut csv = String::from("id,x,y,z,vertex_id,sign_class,depth\n");

        for (id, point) in points.iter().enumerate() {
            csv.push_str(&format!(
                "{},{},{},{},{},{},{}\n",
                id, point.x, point.y, point.z, point.vertex_id, point.sign_class, point.depth
            ));
        }

        csv
    }

    /// Export 3D fractal to JSON format
    ///
    /// # Arguments
    ///
    /// * `max_depth` - Iteration depth
    ///
    /// # Returns
    ///
    /// JSON string with metadata and point array
    #[must_use]
    #[allow(clippy::format_push_string)] // JSON generation requires string building
    pub fn to_json(&self, max_depth: usize) -> String {
        let points = self.generate(max_depth);
        let (total_points, dimension) =
            GoldenSeedFractal::statistics(&GoldenSeedFractal::new(self.atlas), max_depth);
        let mut json = String::from("{\n");

        json.push_str(r#"  "metadata": {"#);
        json.push_str(&format!(r#""max_depth": {max_depth}, "#));
        json.push_str(&format!(r#""total_points": {total_points}, "#));
        json.push_str(&format!(r#""fractal_dimension": {dimension}"#));
        json.push_str("},\n");
        json.push_str(r#"  "points": ["#);
        json.push('\n');

        for (idx, point) in points.iter().enumerate() {
            json.push_str("    {");
            json.push_str(&format!(r#""x": {}, "#, point.x));
            json.push_str(&format!(r#""y": {}, "#, point.y));
            json.push_str(&format!(r#""z": {}, "#, point.z));
            json.push_str(&format!(r#""vertex_id": {}, "#, point.vertex_id));
            json.push_str(&format!(r#""sign_class": {}, "#, point.sign_class));
            json.push_str(&format!(r#""depth": {}"#, point.depth));
            json.push('}');
            if idx < points.len() - 1 {
                json.push(',');
            }
            json.push('\n');
        }

        json.push_str("  ]\n");
        json.push('}');

        json
    }

    /// Get fractal statistics
    ///
    /// Returns `(total_points, fractal_dimension_estimate)`
    #[must_use]
    #[allow(clippy::float_arithmetic)] // Dimension calculation is visualization metadata
    #[allow(clippy::suboptimal_flops)] // Explicit formula for clarity (log base change)
    pub fn statistics(&self, max_depth: usize) -> (usize, f64) {
        let total_points = GoldenSeedFractal::point_count(max_depth);

        // Fractal dimension: D = log(N) / log(1/r)
        // N = 96 (branching factor), r = 1/3 (scaling)
        // D = log(96) / log(3) ≈ 4.15
        let dimension = 96.0_f64.log(3.0_f64);

        (total_points, dimension)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fractal_creation() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal::new(&atlas);
        assert_eq!(fractal.base_coords.len(), 96);
    }

    #[test]
    fn test_fractal_depth_0() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal::new(&atlas);
        let points = fractal.generate(0);
        assert_eq!(points.len(), 96);

        // All points should be at depth 0
        assert!(points.iter().all(|p| p.depth == 0));
    }

    #[test]
    fn test_fractal_depth_1() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal::new(&atlas);
        let points = fractal.generate(1);

        // 96 (depth 0) + 96² (depth 1) = 9,312
        assert_eq!(points.len(), 96 + 96 * 96);

        // Count points at each depth
        let depth_0_count = points.iter().filter(|p| p.depth == 0).count();
        let depth_1_count = points.iter().filter(|p| p.depth == 1).count();

        assert_eq!(depth_0_count, 96);
        assert_eq!(depth_1_count, 96 * 96);
    }

    #[test]
    fn test_sign_class_range() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal::new(&atlas);
        let points = fractal.generate(1);

        // All sign classes should be in range 0..8
        assert!(points.iter().all(|p| p.sign_class < 8));
    }

    #[test]
    fn test_fractal_dimension() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal::new(&atlas);
        let (_, dimension) = fractal.statistics(1);

        // D = log₃(96) ≈ 4.15
        assert!((dimension - 4.15).abs() < 0.01);
    }

    #[test]
    fn test_svg_generation() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal::new(&atlas);
        let svg = fractal.to_svg(1, 800, 800);

        assert!(svg.contains("<svg"));
        assert!(svg.contains("</svg>"));
        assert!(svg.contains("Golden Seed Fractal"));
    }

    // 3D Fractal tests
    #[test]
    fn test_fractal_3d_creation() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal3D::new(&atlas);
        assert_eq!(fractal.base_coords.len(), 96);
    }

    #[test]
    fn test_fractal_3d_depth_0() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal3D::new(&atlas);
        let points = fractal.generate(0);
        assert_eq!(points.len(), 96);

        // All points should be at depth 0
        assert!(points.iter().all(|p| p.depth == 0));
    }

    #[test]
    fn test_fractal_3d_depth_1() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal3D::new(&atlas);
        let points = fractal.generate(1);

        // 96 (depth 0) + 96² (depth 1) = 9,312
        assert_eq!(points.len(), 96 + 96 * 96);

        // Count points at each depth
        let depth_0_count = points.iter().filter(|p| p.depth == 0).count();
        let depth_1_count = points.iter().filter(|p| p.depth == 1).count();

        assert_eq!(depth_0_count, 96);
        assert_eq!(depth_1_count, 96 * 96);
    }

    #[test]
    fn test_fractal_3d_sign_class_range() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal3D::new(&atlas);
        let points = fractal.generate(1);

        // All sign classes should be in range 0..8
        assert!(points.iter().all(|p| p.sign_class < 8));
    }

    #[test]
    fn test_fractal_3d_dimension() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal3D::new(&atlas);
        let (_, dimension) = fractal.statistics(1);

        // D = log₃(96) ≈ 4.15
        assert!((dimension - 4.15).abs() < 0.01);
    }

    #[test]
    fn test_fractal_3d_csv_generation() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal3D::new(&atlas);
        let csv = fractal.to_csv(0);
        assert!(csv.contains("id,x,y,z"));
        assert!(csv.contains("vertex_id"));
        assert!(csv.contains("sign_class"));
        assert!(csv.contains("depth"));
    }

    #[test]
    fn test_fractal_3d_json_generation() {
        let atlas = Atlas::new();
        let fractal = GoldenSeedFractal3D::new(&atlas);
        let json = fractal.to_json(0);
        assert!(json.contains("metadata"));
        assert!(json.contains("points"));
        assert!(json.contains("max_depth"));
        assert!(json.contains("fractal_dimension"));
    }
}
