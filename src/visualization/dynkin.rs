//! Dynkin Diagram Visualization
//!
//! This module generates SVG visualizations of Dynkin diagrams for the five
//! exceptional Lie groups: G₂, F₄, E₆, E₇, E₈.
//!
//! # Dynkin Diagrams
//!
//! A Dynkin diagram is a graph representing the Cartan matrix of a Lie algebra:
//! - Nodes represent simple roots
//! - Edges represent angles between roots (encoded by Cartan matrix entries)
//! - Bond multiplicity: single (angle 120°), double (angle 135°), triple (angle 150°)
//!
//! # Examples
//!
//! ```rust
//! use atlas_embeddings::cartan::CartanMatrix;
//! use atlas_embeddings::visualization::dynkin::DynkinVisualizer;
//!
//! // Generate E₈ Dynkin diagram
//! let e8 = CartanMatrix::<8>::e8();
//! let svg = DynkinVisualizer::generate_svg(&e8, "E₈");
//!
//! assert!(svg.contains("<svg"));
//! assert!(svg.contains("</svg>"));
//! ```

use crate::cartan::CartanMatrix;

/// Visualizer for Dynkin diagrams
///
/// Generates SVG representations of Dynkin diagrams for exceptional Lie groups.
#[derive(Debug, Clone, Copy)]
pub struct DynkinVisualizer;

impl DynkinVisualizer {
    /// Generate SVG for a Cartan matrix
    ///
    /// # Arguments
    ///
    /// * `cartan` - The Cartan matrix to visualize
    /// * `group_name` - Name to display (e.g., "E₈")
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::cartan::CartanMatrix;
    /// use atlas_embeddings::visualization::dynkin::DynkinVisualizer;
    ///
    /// let g2 = CartanMatrix::<2>::g2();
    /// let svg = DynkinVisualizer::generate_svg(&g2, "G₂");
    /// ```
    #[must_use]
    #[allow(clippy::too_many_lines)] // SVG generation requires detailed layout code
    pub fn generate_svg<const N: usize>(cartan: &CartanMatrix<N>, group_name: &str) -> String {
        // Layout parameters for Dynkin diagrams
        // All exceptional groups have specific standard layouts
        match N {
            2 => Self::generate_g2_svg(cartan, group_name),
            4 => Self::generate_f4_svg(cartan, group_name),
            6 => Self::generate_e6_svg(cartan, group_name),
            7 => Self::generate_e7_svg(cartan, group_name),
            8 => Self::generate_e8_svg(cartan, group_name),
            _ => format!("<svg><text>Unsupported rank {N}</text></svg>"),
        }
    }

    /// Generate G₂ Dynkin diagram (rank 2, triple bond)
    ///
    /// Layout: Node 0 --- Node 1 (triple bond pointing left)
    #[must_use]
    #[allow(clippy::format_push_string)] // SVG generation requires string building
    #[allow(clippy::large_stack_arrays)] // format! macros in SVG generation
    fn generate_g2_svg<const N: usize>(_cartan: &CartanMatrix<N>, group_name: &str) -> String {
        let node_radius = 10;
        let spacing = 80;
        let margin = 50;

        let width = 2 * margin + spacing;
        let height = 2 * margin;

        let mut svg = format!(
            r#"<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">"#
        );

        // Title
        svg.push_str(&format!(
            r#"<text x="{}" y="30" font-family="serif" font-size="20" text-anchor="middle">{}</text>"#,
            width / 2,
            group_name
        ));

        let y = height / 2;
        let x1 = margin;
        let x2 = margin + spacing;

        // Triple bond (3 parallel lines)
        let bond_spacing = 4;
        for i in 0_i32..3 {
            let offset = (i - 1) * bond_spacing;
            svg.push_str(&format!(
                r#"<line x1="{}" y1="{}" x2="{}" y2="{}" stroke="black" stroke-width="2"/>"#,
                x1 + node_radius,
                y + offset,
                x2 - node_radius,
                y + offset
            ));
        }

        // Arrow indicating direction (pointing left, since Cartan[0][1] = -1, Cartan[1][0] = -3)
        let arrow_x = (x1 + x2) / 2;
        svg.push_str(&format!(
            r#"<polygon points="{},{} {},{} {},{}" fill="black"/>"#,
            arrow_x - 10,
            y,
            arrow_x,
            y - 6,
            arrow_x,
            y + 6
        ));

        // Nodes
        svg.push_str(&format!(
            r#"<circle cx="{x1}" cy="{y}" r="{node_radius}" fill="white" stroke="black" stroke-width="2"/>"#
        ));
        svg.push_str(&format!(
            r#"<circle cx="{x2}" cy="{y}" r="{node_radius}" fill="white" stroke="black" stroke-width="2"/>"#
        ));

        // Node labels
        svg.push_str(&format!(
            r#"<text x="{x1}" y="{}" font-family="serif" font-size="12" text-anchor="middle">α₁</text>"#,
            y + 30
        ));
        svg.push_str(&format!(
            r#"<text x="{x2}" y="{}" font-family="serif" font-size="12" text-anchor="middle">α₂</text>"#,
            y + 30
        ));

        svg.push_str("</svg>");
        svg
    }

    /// Generate F₄ Dynkin diagram (rank 4, double bond between nodes 1 and 2)
    ///
    /// Layout: 0 — 1 == 2 — 3 (double bond pointing right)
    #[must_use]
    #[allow(clippy::format_push_string)] // SVG generation requires string building
    #[allow(clippy::large_stack_arrays)] // format! macros in SVG generation
    fn generate_f4_svg<const N: usize>(_cartan: &CartanMatrix<N>, group_name: &str) -> String {
        let node_radius = 10;
        let spacing = 80;
        let margin = 50;

        let width = 2 * margin + 3 * spacing;
        let height = 2 * margin;

        let mut svg = format!(
            r#"<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">"#
        );

        // Title
        svg.push_str(&format!(
            r#"<text x="{}" y="30" font-family="serif" font-size="20" text-anchor="middle">{}</text>"#,
            width / 2,
            group_name
        ));

        let y = height / 2;

        // Node positions
        let positions: Vec<i32> = (0..4).map(|i| margin + i * spacing).collect();

        // Single bonds: 0-1 and 2-3
        for i in [0, 2] {
            svg.push_str(&format!(
                r#"<line x1="{}" y1="{y}" x2="{}" y2="{y}" stroke="black" stroke-width="2"/>"#,
                positions[i] + node_radius,
                positions[i + 1] - node_radius
            ));
        }

        // Double bond: 1-2 (pointing right, since Cartan[1][2] = -2, Cartan[2][1] = -1)
        let bond_spacing = 3;
        for offset in [-bond_spacing, bond_spacing] {
            svg.push_str(&format!(
                r#"<line x1="{}" y1="{}" x2="{}" y2="{}" stroke="black" stroke-width="2"/>"#,
                positions[1] + node_radius,
                y + offset,
                positions[2] - node_radius,
                y + offset
            ));
        }

        // Arrow for double bond (pointing right)
        let arrow_x = (positions[1] + positions[2]) / 2;
        svg.push_str(&format!(
            r#"<polygon points="{},{} {},{} {},{}" fill="black"/>"#,
            arrow_x + 10,
            y,
            arrow_x,
            y - 6,
            arrow_x,
            y + 6
        ));

        // Nodes
        for (i, &x) in positions.iter().enumerate() {
            svg.push_str(&format!(
                r#"<circle cx="{x}" cy="{y}" r="{node_radius}" fill="white" stroke="black" stroke-width="2"/>"#
            ));
            svg.push_str(&format!(
                r#"<text x="{x}" y="{}" font-family="serif" font-size="12" text-anchor="middle">α{}</text>"#,
                y + 30,
                i + 1
            ));
        }

        svg.push_str("</svg>");
        svg
    }

    /// Generate E₆ Dynkin diagram (rank 6, branched structure)
    ///
    /// Layout:
    /// ```text
    ///       α₂
    ///       |
    /// α₁ — α₃ — α₄ — α₅ — α₆
    /// ```
    #[must_use]
    #[allow(clippy::format_push_string)] // SVG generation requires string building
    #[allow(clippy::large_stack_arrays)] // format! macros in SVG generation
    fn generate_e6_svg<const N: usize>(_cartan: &CartanMatrix<N>, group_name: &str) -> String {
        let node_radius = 10;
        let spacing = 70;
        let margin = 50;

        let width = 2 * margin + 4 * spacing;
        let height = 2 * margin + spacing;

        let mut svg = format!(
            r#"<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">"#
        );

        // Title
        svg.push_str(&format!(
            r#"<text x="{}" y="30" font-family="serif" font-size="20" text-anchor="middle">{}</text>"#,
            width / 2,
            group_name
        ));

        let y_main = height / 2 + 20;
        let y_branch = y_main - spacing;

        // Main chain positions (α₁, α₃, α₄, α₅, α₆)
        let x_positions = [
            margin,               // α₁
            margin + spacing,     // α₃
            margin + 2 * spacing, // α₄
            margin + 3 * spacing, // α₅
            margin + 4 * spacing, // α₆
        ];

        // Branch position (α₂)
        let x_branch = x_positions[1]; // Above α₃

        // Main chain bonds
        for i in 0..4 {
            svg.push_str(&format!(
                r#"<line x1="{}" y1="{y_main}" x2="{}" y2="{y_main}" stroke="black" stroke-width="2"/>"#,
                x_positions[i] + node_radius,
                x_positions[i + 1] - node_radius
            ));
        }

        // Branch bond (α₂ to α₃)
        svg.push_str(&format!(
            r#"<line x1="{x_branch}" y1="{}" x2="{x_branch}" y2="{}" stroke="black" stroke-width="2"/>"#,
            y_branch + node_radius,
            y_main - node_radius
        ));

        // Nodes - main chain
        let labels = ["α₁", "α₃", "α₄", "α₅", "α₆"];
        for (i, &x) in x_positions.iter().enumerate() {
            svg.push_str(&format!(
                r#"<circle cx="{x}" cy="{y_main}" r="{node_radius}" fill="white" stroke="black" stroke-width="2"/>"#
            ));
            svg.push_str(&format!(
                r#"<text x="{x}" y="{}" font-family="serif" font-size="12" text-anchor="middle">{}</text>"#,
                y_main + 25,
                labels[i]
            ));
        }

        // Branch node (α₂)
        svg.push_str(&format!(
            r#"<circle cx="{x_branch}" cy="{y_branch}" r="{node_radius}" fill="white" stroke="black" stroke-width="2"/>"#
        ));
        svg.push_str(&format!(
            r#"<text x="{x_branch}" y="{}" font-family="serif" font-size="12" text-anchor="middle">α₂</text>"#,
            y_branch - 15
        ));

        svg.push_str("</svg>");
        svg
    }

    /// Generate E₇ Dynkin diagram (rank 7, branched structure)
    ///
    /// Layout:
    /// ```text
    ///          α₂
    ///          |
    /// α₁ — α₃ — α₄ — α₅ — α₆ — α₇
    /// ```
    #[must_use]
    #[allow(clippy::format_push_string)] // SVG generation requires string building
    #[allow(clippy::large_stack_arrays)] // format! macros in SVG generation
    fn generate_e7_svg<const N: usize>(_cartan: &CartanMatrix<N>, group_name: &str) -> String {
        let node_radius = 10;
        let spacing = 70;
        let margin = 50;

        let width = 2 * margin + 5 * spacing;
        let height = 2 * margin + spacing;

        let mut svg = format!(
            r#"<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">"#
        );

        // Title
        svg.push_str(&format!(
            r#"<text x="{}" y="30" font-family="serif" font-size="20" text-anchor="middle">{}</text>"#,
            width / 2,
            group_name
        ));

        let y_main = height / 2 + 20;
        let y_branch = y_main - spacing;

        // Main chain positions
        let x_positions: Vec<i32> = (0..6).map(|i| margin + i * spacing).collect();
        let x_branch = x_positions[1]; // Above α₃

        // Main chain bonds
        for i in 0..5 {
            svg.push_str(&format!(
                r#"<line x1="{}" y1="{y_main}" x2="{}" y2="{y_main}" stroke="black" stroke-width="2"/>"#,
                x_positions[i] + node_radius,
                x_positions[i + 1] - node_radius
            ));
        }

        // Branch bond
        svg.push_str(&format!(
            r#"<line x1="{x_branch}" y1="{}" x2="{x_branch}" y2="{}" stroke="black" stroke-width="2"/>"#,
            y_branch + node_radius,
            y_main - node_radius
        ));

        // Main chain nodes
        let labels = ["α₁", "α₃", "α₄", "α₅", "α₆", "α₇"];
        for (i, &x) in x_positions.iter().enumerate() {
            svg.push_str(&format!(
                r#"<circle cx="{x}" cy="{y_main}" r="{node_radius}" fill="white" stroke="black" stroke-width="2"/>"#
            ));
            svg.push_str(&format!(
                r#"<text x="{x}" y="{}" font-family="serif" font-size="12" text-anchor="middle">{}</text>"#,
                y_main + 25,
                labels[i]
            ));
        }

        // Branch node
        svg.push_str(&format!(
            r#"<circle cx="{x_branch}" cy="{y_branch}" r="{node_radius}" fill="white" stroke="black" stroke-width="2"/>"#
        ));
        svg.push_str(&format!(
            r#"<text x="{x_branch}" y="{}" font-family="serif" font-size="12" text-anchor="middle">α₂</text>"#,
            y_branch - 15
        ));

        svg.push_str("</svg>");
        svg
    }

    /// Generate E₈ Dynkin diagram (rank 8, branched structure)
    ///
    /// Layout:
    /// ```text
    ///             α₂
    ///             |
    /// α₁ — α₃ — α₄ — α₅ — α₆ — α₇ — α₈
    /// ```
    #[must_use]
    #[allow(clippy::format_push_string)] // SVG generation requires string building
    #[allow(clippy::large_stack_arrays)] // format! macros in SVG generation
    fn generate_e8_svg<const N: usize>(_cartan: &CartanMatrix<N>, group_name: &str) -> String {
        let node_radius = 10;
        let spacing = 70;
        let margin = 50;

        let width = 2 * margin + 6 * spacing;
        let height = 2 * margin + spacing;

        let mut svg = format!(
            r#"<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">"#
        );

        // Title
        svg.push_str(&format!(
            r#"<text x="{}" y="30" font-family="serif" font-size="20" text-anchor="middle">{}</text>"#,
            width / 2,
            group_name
        ));

        let y_main = height / 2 + 20;
        let y_branch = y_main - spacing;

        // Main chain positions
        let x_positions: Vec<i32> = (0..7).map(|i| margin + i * spacing).collect();
        let x_branch = x_positions[1]; // Above α₃

        // Main chain bonds
        for i in 0..6 {
            svg.push_str(&format!(
                r#"<line x1="{}" y1="{y_main}" x2="{}" y2="{y_main}" stroke="black" stroke-width="2"/>"#,
                x_positions[i] + node_radius,
                x_positions[i + 1] - node_radius
            ));
        }

        // Branch bond
        svg.push_str(&format!(
            r#"<line x1="{x_branch}" y1="{}" x2="{x_branch}" y2="{}" stroke="black" stroke-width="2"/>"#,
            y_branch + node_radius,
            y_main - node_radius
        ));

        // Main chain nodes
        let labels = ["α₁", "α₃", "α₄", "α₅", "α₆", "α₇", "α₈"];
        for (i, &x) in x_positions.iter().enumerate() {
            svg.push_str(&format!(
                r#"<circle cx="{x}" cy="{y_main}" r="{node_radius}" fill="white" stroke="black" stroke-width="2"/>"#
            ));
            svg.push_str(&format!(
                r#"<text x="{x}" y="{}" font-family="serif" font-size="12" text-anchor="middle">{}</text>"#,
                y_main + 25,
                labels[i]
            ));
        }

        // Branch node
        svg.push_str(&format!(
            r#"<circle cx="{x_branch}" cy="{y_branch}" r="{node_radius}" fill="white" stroke="black" stroke-width="2"/>"#
        ));
        svg.push_str(&format!(
            r#"<text x="{x_branch}" y="{}" font-family="serif" font-size="12" text-anchor="middle">α₂</text>"#,
            y_branch - 15
        ));

        svg.push_str("</svg>");
        svg
    }

    /// Generate all five exceptional group Dynkin diagrams
    ///
    /// Returns a vector of (`group_name`, `svg_content`) pairs.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::visualization::dynkin::DynkinVisualizer;
    ///
    /// let diagrams = DynkinVisualizer::generate_all_exceptional();
    /// assert_eq!(diagrams.len(), 5);
    /// ```
    #[must_use]
    pub fn generate_all_exceptional() -> Vec<(String, String)> {
        vec![
            ("G2".to_string(), Self::generate_svg(&CartanMatrix::<2>::g2(), "G₂")),
            ("F4".to_string(), Self::generate_svg(&CartanMatrix::<4>::f4(), "F₄")),
            ("E6".to_string(), Self::generate_svg(&CartanMatrix::<6>::e6(), "E₆")),
            ("E7".to_string(), Self::generate_svg(&CartanMatrix::<7>::e7(), "E₇")),
            ("E8".to_string(), Self::generate_svg(&CartanMatrix::<8>::e8(), "E₈")),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_g2_svg() {
        let g2 = CartanMatrix::<2>::g2();
        let svg = DynkinVisualizer::generate_svg(&g2, "G₂");
        assert!(svg.contains("<svg"));
    }

    #[test]
    fn test_generate_all_exceptional() {
        let diagrams = DynkinVisualizer::generate_all_exceptional();
        assert_eq!(diagrams.len(), 5);

        let names: Vec<String> = diagrams.iter().map(|(name, _)| name.clone()).collect();
        assert!(names.contains(&"G2".to_string()));
        assert!(names.contains(&"F4".to_string()));
        assert!(names.contains(&"E6".to_string()));
        assert!(names.contains(&"E7".to_string()));
        assert!(names.contains(&"E8".to_string()));
    }
}
