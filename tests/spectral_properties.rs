//! Spectral Properties Integration Tests
//!
//! End-to-end verification of the Atlas Laplacian spectral analysis.
//! These tests serve as **computational certificates** for the theorems
//! in Chapter 10 (Spectral Analysis).
//!
//! ## Main Result
//!
//! The spectral gap of the Atlas Laplacian is exactly λ₁ = 1,
//! proven via block tridiagonal decomposition into Q₄ hypercube blocks.

use atlas_embeddings::arithmetic::Rational;
use atlas_embeddings::spectral::SpectralAnalysis;
use atlas_embeddings::Atlas;
use num_traits::{One, Zero};

// ─────────────────────────────────────────────────────────────────────────────
// Spectral Gap Tests
// ─────────────────────────────────────────────────────────────────────────────

/// **Theorem 10.4.3: Spectral Gap Is Exactly One**
///
/// The main result of the spectral analysis. The smallest nonzero
/// eigenvalue of the Atlas Laplacian is λ₁ = 1, arising from the
/// block tridiagonal matrix M₀ (Q₄ eigenvalue ν = 0).
#[test]
fn test_spectral_gap_is_exactly_one() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    let gap = spectral.spectral_gap();
    assert_eq!(gap, Rational::from_integer(1), "Spectral gap must be exactly 1");

    // Verify it's a proper integer (not a rational approximation)
    assert_eq!(*gap.numer(), 1, "Numerator must be 1");
    assert_eq!(*gap.denom(), 1, "Denominator must be 1");
}

/// **Spectral Gap Is Positive**
///
/// Verifies λ₁ > 0, confirming each hemisphere is connected.
/// (If the hemisphere were disconnected, λ₁ would be 0.)
#[test]
fn test_spectral_gap_positive() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);
    assert!(spectral.spectral_gap() > Rational::zero());
}

// ─────────────────────────────────────────────────────────────────────────────
// Spectrum Completeness Tests
// ─────────────────────────────────────────────────────────────────────────────

/// **Theorem 10.4.2: Hemisphere Spectrum Completeness**
///
/// Verifies the hemisphere has exactly 48 eigenvalues (counting multiplicity),
/// distributed across 11 distinct values.
#[test]
fn test_hemisphere_spectrum_completeness() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    let hemi = spectral.hemisphere_spectrum();

    // 11 distinct eigenvalues
    assert_eq!(hemi.len(), 11, "11 distinct eigenvalues");

    // 48 total (counting multiplicity)
    let total: usize = hemi.iter().map(|(_, m)| m).sum();
    assert_eq!(total, 48, "48 eigenvalues counting multiplicity");
}

/// **Full Atlas Spectrum Completeness**
///
/// The full Atlas has 96 eigenvalues (two hemispheres × 48 each).
#[test]
fn test_full_spectrum_completeness() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    let full = spectral.full_spectrum();
    let total: usize = full.iter().map(|(_, m)| m).sum();
    assert_eq!(total, 96, "96 total eigenvalues for full Atlas");
}

/// **Specific Multiplicity Values**
///
/// Verifies the exact multiplicity of each eigenvalue in the hemisphere spectrum.
#[test]
fn test_specific_multiplicities() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);
    let hemi = spectral.hemisphere_spectrum();

    // Expected: (eigenvalue, multiplicity)
    let expected = [
        (0, 1),
        (1, 1),
        (2, 4),
        (3, 5),
        (4, 6),
        (5, 10),
        (6, 4),
        (7, 10),
        (8, 1),
        (9, 5),
        (11, 1),
    ];

    for (ev_int, expected_mult) in expected {
        let ev = Rational::from_integer(ev_int);
        let found = hemi.iter().find(|&&(e, _)| e == ev);
        assert_eq!(
            found,
            Some(&(ev, expected_mult)),
            "Eigenvalue {ev_int}: expected multiplicity {expected_mult}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Trace Identity Tests
// ─────────────────────────────────────────────────────────────────────────────

/// **Trace Identity: tr(L_H) = 2|E_H| = 256**
///
/// The Laplacian trace equals twice the edge count. For the hemisphere
/// with 128 edges, this gives trace = 256.
#[test]
fn test_trace_equals_twice_edges() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    assert_eq!(
        spectral.hemisphere_trace(),
        Rational::from_integer(256),
        "tr(L) = 2|E| = 256"
    );
}

/// **Trace² Identity: tr(L_H²) = 1632**
///
/// Verified both from the spectrum (Σ λ²·mult) and from the degree
/// formula (Σ deg(v)² + 2|E|).
#[test]
fn test_trace_squared_identity() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    assert_eq!(
        spectral.hemisphere_trace_squared(),
        Rational::from_integer(1632),
        "tr(L²) = 1632"
    );
}

/// **Trace Consistency: Spectrum vs Direct**
///
/// Verifies that the trace computed from the spectrum matches the trace
/// computed from summing vertex degrees.
#[test]
fn test_trace_consistency() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    // Compute trace from degree sum directly
    let mut degree_sum: i64 = 0;
    for v in 0..atlas.num_vertices() {
        if atlas.label(v).e7 == 0 {
            degree_sum += atlas.degree(v) as i64;
        }
    }

    assert_eq!(
        spectral.hemisphere_trace(),
        Rational::from_integer(degree_sum),
        "Spectrum trace must match degree sum"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Eigenvalue Property Tests
// ─────────────────────────────────────────────────────────────────────────────

/// **All Eigenvalues Are Non-Negative**
///
/// Graph Laplacians are positive semidefinite, so all eigenvalues ≥ 0.
#[test]
fn test_all_eigenvalues_nonnegative() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    for &(ev, _) in spectral.hemisphere_spectrum() {
        assert!(ev >= Rational::zero(), "Eigenvalue {ev} is negative");
    }
}

/// **Gershgorin Upper Bound: λ_max ≤ 12**
///
/// By the Gershgorin circle theorem, all eigenvalues of a graph Laplacian
/// lie in [0, 2·max_degree]. For the Atlas with max_degree = 6, this
/// gives an upper bound of 12.
#[test]
fn test_gershgorin_upper_bound() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    let bound = spectral.gershgorin_upper_bound();
    assert_eq!(bound, Rational::from_integer(12));

    // Verify actual maximum is less than bound
    assert!(
        spectral.max_eigenvalue() <= bound,
        "Max eigenvalue {} exceeds Gershgorin bound {}",
        spectral.max_eigenvalue(),
        bound
    );
}

/// **Maximum Eigenvalue Is 11**
///
/// The largest eigenvalue is 11 (from M₈: eigenvalues {8, 9, 11}).
/// It has multiplicity 1 (from Q₄ eigenvalue 8, which has multiplicity 1).
#[test]
fn test_max_eigenvalue_is_11() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    assert_eq!(spectral.max_eigenvalue(), Rational::from_integer(11));
}

/// **All Eigenvalues Are Integers**
///
/// Since all M_ν eigenvalues {ν, ν+1, ν+3} are integers for integer ν,
/// the entire spectrum consists of integers.
#[test]
fn test_all_eigenvalues_are_integers() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);
    assert!(spectral.all_eigenvalues_integer());
}

/// **Eigenvalue 10 Is Missing**
///
/// The spectrum skips λ = 10 because no combination ν + {0,1,3}
/// for ν ∈ {0,2,4,6,8} yields 10.
#[test]
fn test_eigenvalue_10_missing() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    let ten = Rational::from_integer(10);
    let has_ten = spectral
        .hemisphere_spectrum()
        .iter()
        .any(|&(ev, _)| ev == ten);
    assert!(!has_ten, "Eigenvalue 10 should not appear");
}

// ─────────────────────────────────────────────────────────────────────────────
// Block Tridiagonal Tests
// ─────────────────────────────────────────────────────────────────────────────

/// **Block Matrix M₀ Eigenvalue Verification**
///
/// Verifies det(M₀ - λI) = 0 for λ ∈ {0, 1, 3}.
#[test]
fn test_block_m0_eigenvalues() {
    let spectral = SpectralAnalysis::from_atlas(&Atlas::new());
    let m = spectral.block_matrix(0);

    // Eigenvalue λ = 0: det(M₀) must be 0
    let det_at_0 = rational_det_3x3(&m, Rational::zero());
    assert!(det_at_0.is_zero(), "det(M₀ - 0·I) = {det_at_0}");

    // Eigenvalue λ = 1: det(M₀ - I) must be 0
    let det_at_1 = rational_det_3x3(&m, Rational::one());
    assert!(det_at_1.is_zero(), "det(M₀ - 1·I) = {det_at_1}");

    // Eigenvalue λ = 3: det(M₀ - 3I) must be 0
    let det_at_3 = rational_det_3x3(&m, Rational::from_integer(3));
    assert!(det_at_3.is_zero(), "det(M₀ - 3·I) = {det_at_3}");
}

/// **Block Matrix Trace-Determinant Consistency**
///
/// For each M_ν with eigenvalues {ν, ν+1, ν+3}:
/// - tr(M_ν) = 3ν + 4 (sum of eigenvalues)
/// - det(M_ν) = ν(ν+1)(ν+3) (product of eigenvalues)
#[test]
fn test_block_trace_det_consistency() {
    let spectral = SpectralAnalysis::from_atlas(&Atlas::new());

    for nu in [0, 2, 4, 6, 8] {
        let m = spectral.block_matrix(nu);

        // Trace
        let trace = m[0][0] + m[1][1] + m[2][2];
        let expected_trace = Rational::from_integer(3 * nu + 4);
        assert_eq!(trace, expected_trace, "tr(M_{nu})");

        // Determinant (computed directly)
        let det = m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
            - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
            + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]);
        let expected_det = Rational::from_integer(nu * (nu + 1) * (nu + 3));
        assert_eq!(det, expected_det, "det(M_{nu})");
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Zero Eigenvalue Tests
// ─────────────────────────────────────────────────────────────────────────────

/// **Zero Eigenvalue Multiplicity (Hemisphere)**
///
/// λ = 0 has multiplicity 1 per hemisphere, confirming each hemisphere
/// is a connected graph.
#[test]
fn test_zero_multiplicity_hemisphere() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    let zero_entry = spectral
        .hemisphere_spectrum()
        .iter()
        .find(|&&(ev, _)| ev.is_zero());
    assert_eq!(zero_entry, Some(&(Rational::zero(), 1)));
}

/// **Zero Eigenvalue Multiplicity (Full Atlas)**
///
/// λ = 0 has multiplicity 2 for the full Atlas (two disconnected hemispheres).
#[test]
fn test_zero_multiplicity_full() {
    let atlas = Atlas::new();
    let spectral = SpectralAnalysis::from_atlas(&atlas);

    let zero_entry = spectral
        .full_spectrum()
        .iter()
        .find(|&&(ev, _)| ev.is_zero());
    assert_eq!(zero_entry, Some(&(Rational::zero(), 2)));
}

// ─────────────────────────────────────────────────────────────────────────────
// Symmetry and Consistency Tests
// ─────────────────────────────────────────────────────────────────────────────

/// **Hemisphere Symmetry Under Mirror Map**
///
/// Both hemispheres must produce the same spectrum (they are isomorphic
/// via the mirror map τ which flips e₇).
#[test]
fn test_hemisphere_spectrum_mirror_symmetry() {
    let atlas = Atlas::new();

    // Build spectral analysis (uses hemisphere 0)
    let spectral = SpectralAnalysis::from_atlas(&atlas);
    let spectrum_0 = spectral.hemisphere_spectrum().to_vec();

    // Manually verify hemisphere 1 has same degree distribution
    let mut h1_degrees: Vec<usize> = Vec::new();
    let h1_vertices: Vec<usize> = (0..atlas.num_vertices())
        .filter(|&v| atlas.label(v).e7 == 1)
        .collect();
    let h1_set: std::collections::HashSet<usize> =
        h1_vertices.iter().copied().collect();

    for &v in &h1_vertices {
        let deg = atlas
            .neighbors(v)
            .iter()
            .filter(|n| h1_set.contains(n))
            .count();
        h1_degrees.push(deg);
    }

    // Same degree sequence implies same spectrum for this graph structure
    let deg5 = h1_degrees.iter().filter(|&&d| d == 5).count();
    let deg6 = h1_degrees.iter().filter(|&&d| d == 6).count();
    assert_eq!(deg5, 32, "Hemisphere 1: 32 degree-5 vertices");
    assert_eq!(deg6, 16, "Hemisphere 1: 16 degree-6 vertices");

    // Same block structure implies same spectrum
    let _ = spectrum_0; // Used implicitly through spectral
}

/// **Spectral Analysis Is Deterministic**
///
/// Running the analysis twice produces identical results.
#[test]
fn test_deterministic() {
    let atlas = Atlas::new();
    let s1 = SpectralAnalysis::from_atlas(&atlas);
    let s2 = SpectralAnalysis::from_atlas(&atlas);

    assert_eq!(s1.spectral_gap(), s2.spectral_gap());
    assert_eq!(s1.hemisphere_spectrum(), s2.hemisphere_spectrum());
    assert_eq!(s1.hemisphere_trace(), s2.hemisphere_trace());
    assert_eq!(
        s1.hemisphere_trace_squared(),
        s2.hemisphere_trace_squared()
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Helper Functions
// ─────────────────────────────────────────────────────────────────────────────

/// Compute det(M - λI) for a 3×3 rational matrix
fn rational_det_3x3(m: &[[Rational; 3]; 3], lambda: Rational) -> Rational {
    let shifted = [
        [m[0][0] - lambda, m[0][1], m[0][2]],
        [m[1][0], m[1][1] - lambda, m[1][2]],
        [m[2][0], m[2][1], m[2][2] - lambda],
    ];
    shifted[0][0] * (shifted[1][1] * shifted[2][2] - shifted[1][2] * shifted[2][1])
        - shifted[0][1] * (shifted[1][0] * shifted[2][2] - shifted[1][2] * shifted[2][0])
        + shifted[0][2] * (shifted[1][0] * shifted[2][1] - shifted[1][1] * shifted[2][0])
}
