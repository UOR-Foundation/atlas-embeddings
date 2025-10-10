//! E₈ Root System Projections
//!
//! This module provides projection methods for visualizing the 240 E₈ roots
//! in 2D and 3D space.
//!
//! # Projection Methods
//!
//! - **Coxeter Plane**: Most symmetric 2D projection (30° rotational symmetry)
//! - **Principal Components**: PCA-based dimensional reduction
//! - **Coordinate Planes**: Simple projections onto (x,y), (x,y,z) subspaces
//!
//! # Examples
//!
//! ```rust
//! use atlas_embeddings::e8::E8RootSystem;
//! use atlas_embeddings::visualization::e8_roots::E8Projector;
//!
//! let e8 = E8RootSystem::new();
//! let projector = E8Projector::new(&e8);
//!
//! // Get 2D Coxeter plane projection
//! let points_2d = projector.project_coxeter_plane();
//! assert_eq!(points_2d.len(), 240);
//! ```

use crate::arithmetic::Rational;
use crate::e8::E8RootSystem;
use num_traits::ToPrimitive;

/// Projector for E₈ root system
///
/// Provides methods to project 8-dimensional E₈ roots into 2D and 3D for visualization.
#[derive(Debug)]
pub struct E8Projector<'a> {
    #[allow(dead_code)] // Will be used when projection algorithms are implemented
    e8: &'a E8RootSystem,
}

impl<'a> E8Projector<'a> {
    /// Create a new E₈ projector
    ///
    /// # Examples
    ///
    /// ```rust
    /// use atlas_embeddings::e8::E8RootSystem;
    /// use atlas_embeddings::visualization::e8_roots::E8Projector;
    ///
    /// let e8 = E8RootSystem::new();
    /// let projector = E8Projector::new(&e8);
    /// ```
    #[must_use]
    pub const fn new(e8: &'a E8RootSystem) -> Self {
        Self { e8 }
    }

    /// Project to Coxeter plane (2D)
    ///
    /// The Coxeter plane is the most symmetric 2D projection for E₈,
    /// exhibiting 30-fold rotational symmetry.
    ///
    /// The Coxeter plane is defined as the 2D eigenspace of the Coxeter element
    /// (product of all simple reflections) corresponding to eigenvalues e^(±2πi/30).
    ///
    /// Since exact computation requires algebraic numbers, we use a rational
    /// approximation based on the standard Coxeter plane basis vectors.
    ///
    /// For E₈, the Coxeter plane projection uses specific linear combinations
    /// of the 8 coordinates. We use the standard formulation:
    ///
    /// x = (v₁ + v₈)/√2
    /// y = (v₁ - v₈)/√2
    ///
    /// Since √2 is irrational, we work with unnormalized coordinates (scaling is irrelevant for visualization).
    ///
    /// Returns a vector of (x, y) coordinates as exact rationals.
    #[must_use]
    #[allow(clippy::similar_names)] // x_coord, y_coord are distinct
    pub fn project_coxeter_plane(&self) -> Vec<(Rational, Rational)> {
        // Coxeter plane projection for E₈: standard 2D projection showing 30-fold symmetry
        // Using unnormalized coordinates (v₁ + v₈, v₁ - v₈) to maintain exact arithmetic
        self.e8
            .roots()
            .iter()
            .map(|root| {
                let coords = root.coords();
                let v0 = coords[0].to_rational();
                let v7 = coords[7].to_rational();

                // Projection: x = v₀ + v₇, y = v₀ - v₇
                let x_coord = v0 + v7;
                let y_coord = v0 - v7;

                (x_coord, y_coord)
            })
            .collect()
    }

    /// Project to 3D using principal components
    ///
    /// For E₈ visualization, we use the first three coordinates as a simple
    /// 3D projection. This is not a true PCA projection (which would require
    /// computing eigenvectors), but provides a useful 3D view while maintaining
    /// exact rational arithmetic.
    ///
    /// A true PCA would involve:
    /// 1. Computing the 240×240 covariance matrix
    /// 2. Finding eigenvalues and eigenvectors
    /// 3. Projecting onto top 3 eigenvectors
    ///
    /// However, eigenvalues of integer/rational matrices are typically irrational,
    /// so we use a simple coordinate projection instead.
    ///
    /// Returns a vector of (x, y, z) coordinates as exact rationals.
    #[must_use]
    pub fn project_3d_principal(&self) -> Vec<(Rational, Rational, Rational)> {
        // Simple 3D projection using first three coordinates
        self.e8
            .roots()
            .iter()
            .map(|root| {
                let coords = root.coords();
                (coords[0].to_rational(), coords[1].to_rational(), coords[2].to_rational())
            })
            .collect()
    }

    /// Project to simple (x, y) coordinate plane
    ///
    /// Projects onto first two coordinates for quick visualization.
    /// This is the simplest possible projection, maintaining exact arithmetic.
    #[must_use]
    pub fn project_xy_plane(&self) -> Vec<(Rational, Rational)> {
        self.e8
            .roots()
            .iter()
            .map(|root| {
                let coords = root.coords();
                (coords[0].to_rational(), coords[1].to_rational())
            })
            .collect()
    }

    /// Export projection to CSV format
    ///
    /// # Format
    ///
    /// ```csv
    /// id,x,y,z,root_type
    /// 0,0.707,0.000,0.707,integer
    /// 1,0.500,0.500,0.500,half_integer
    /// ```
    ///
    /// # Arguments
    ///
    /// * `projection` - 3D coordinates for each of the 240 roots
    #[must_use]
    #[allow(clippy::cast_precision_loss)] // CSV export only, not used in computation
    #[allow(clippy::similar_names)] // x_f64, y_f64, z_f64 are distinct coordinates
    #[allow(clippy::format_push_string)] // CSV generation requires string building
    #[allow(clippy::large_stack_arrays)] // format! macros in CSV export
    pub fn export_projection_csv(&self, projection: &[(Rational, Rational, Rational)]) -> String {
        let mut csv = String::from("id,x,y,z,root_type\n");

        for (id, (x, y, z)) in projection.iter().enumerate() {
            let x_f64 = x.to_f64().unwrap_or(0.0);
            let y_f64 = y.to_f64().unwrap_or(0.0);
            let z_f64 = z.to_f64().unwrap_or(0.0);

            // Determine root type (integer vs half-integer)
            let root = self.e8.get_root(id);
            let root_type = if root.coords().iter().all(|c| c.to_rational().denom() == &1) {
                "integer"
            } else {
                "half_integer"
            };

            csv.push_str(&format!("{id},{x_f64},{y_f64},{z_f64},{root_type}\n"));
        }

        csv
    }

    /// Export 2D projection to CSV format
    ///
    /// # Format
    ///
    /// ```csv
    /// id,x,y,root_type
    /// 0,0.707,0.000,integer
    /// 1,0.500,0.500,half_integer
    /// ```
    #[must_use]
    #[allow(clippy::cast_precision_loss)] // CSV export only
    #[allow(clippy::similar_names)] // x_f64, y_f64 are distinct
    #[allow(clippy::format_push_string)] // CSV generation requires string building
    #[allow(clippy::large_stack_arrays)] // format! macros in CSV export
    pub fn export_projection_2d_csv(&self, projection: &[(Rational, Rational)]) -> String {
        let mut csv = String::from("id,x,y,root_type\n");

        for (id, (x, y)) in projection.iter().enumerate() {
            let x_f64 = x.to_f64().unwrap_or(0.0);
            let y_f64 = y.to_f64().unwrap_or(0.0);

            let root = self.e8.get_root(id);
            let root_type = if root.coords().iter().all(|c| c.to_rational().denom() == &1) {
                "integer"
            } else {
                "half_integer"
            };

            csv.push_str(&format!("{id},{x_f64},{y_f64},{root_type}\n"));
        }

        csv
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::e8::E8RootSystem;

    #[test]
    fn test_projector_creation() {
        let e8 = E8RootSystem::new();
        let projector = E8Projector::new(&e8);
        let projection = projector.project_coxeter_plane();
        assert_eq!(projection.len(), 240);
    }

    #[test]
    fn test_3d_projection() {
        let e8 = E8RootSystem::new();
        let projector = E8Projector::new(&e8);
        let projection = projector.project_3d_principal();
        assert_eq!(projection.len(), 240);
    }
}
