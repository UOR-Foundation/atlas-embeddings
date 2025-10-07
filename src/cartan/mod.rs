//! Cartan Matrices and Dynkin Diagrams
//!
//! This module provides Cartan matrix representations for Lie algebras,
//! with compile-time rank verification and exact integer arithmetic.
//!
//! # Cartan Matrix
//!
//! A Cartan matrix C is an n×n integer matrix satisfying:
//! 1. Diagonal entries C\[i\]\[i\] = 2
//! 2. Off-diagonal entries C\[i\]\[j\] ≤ 0 for i ≠ j
//! 3. C\[i\]\[j\] = 0 ⟺ C\[j\]\[i\] = 0
//!
//! # Simply-Laced
//!
//! A Cartan matrix is **simply-laced** if all off-diagonal entries are in {0, -1}.
//! The exceptional simply-laced groups are E₆, E₇, E₈.
//! Non-simply-laced exceptional groups are G₂ (triple bond), F₄ (double bond).
//!
//! # Examples
//!
//! ```
//! use atlas_embeddings::cartan::CartanMatrix;
//!
//! // G₂ Cartan matrix (rank 2, triple bond)
//! let g2 = CartanMatrix::new([
//!     [ 2, -3],
//!     [-1,  2],
//! ]);
//! assert_eq!(g2.rank(), 2);
//! assert!(!g2.is_simply_laced());
//! assert!(g2.is_valid());
//!
//! // F₄ Cartan matrix (rank 4, double bond)
//! let f4 = CartanMatrix::new([
//!     [ 2, -1,  0,  0],
//!     [-1,  2, -2,  0],
//!     [ 0, -1,  2, -1],
//!     [ 0,  0, -1,  2],
//! ]);
//! assert_eq!(f4.rank(), 4);
//! assert!(!f4.is_simply_laced());
//! ```

/// Cartan matrix for a Lie algebra
///
/// The type parameter `N` encodes the rank at compile time.
/// All entries are exact integers (no floating point).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CartanMatrix<const N: usize> {
    entries: [[i8; N]; N],
}

impl<const N: usize> CartanMatrix<N> {
    /// Create a new Cartan matrix
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::cartan::CartanMatrix;
    ///
    /// let g2 = CartanMatrix::new([
    ///     [ 2, -3],
    ///     [-1,  2],
    /// ]);
    /// ```
    #[must_use]
    pub const fn new(entries: [[i8; N]; N]) -> Self {
        Self { entries }
    }

    /// Get the rank (dimension) of the Cartan matrix
    #[must_use]
    pub const fn rank(&self) -> usize {
        N
    }

    /// Get entry at position (i, j)
    ///
    /// # Panics
    ///
    /// Panics if indices are out of bounds
    #[must_use]
    pub const fn get(&self, i: usize, j: usize) -> i8 {
        self.entries[i][j]
    }

    /// Get all entries as a 2D array
    #[must_use]
    pub const fn entries(&self) -> &[[i8; N]; N] {
        &self.entries
    }

    /// Check if this is a valid Cartan matrix
    ///
    /// Verifies:
    /// 1. Diagonal entries = 2
    /// 2. Off-diagonal entries ≤ 0
    /// 3. Symmetry condition: C\[i\]\[j\] = 0 ⟺ C\[j\]\[i\] = 0
    #[must_use]
    pub fn is_valid(&self) -> bool {
        // Check diagonal = 2
        for i in 0..N {
            if self.entries[i][i] != 2 {
                return false;
            }
        }

        // Check off-diagonal ≤ 0 and symmetry condition
        for i in 0..N {
            for j in 0..N {
                if i != j {
                    // Off-diagonal must be non-positive
                    if self.entries[i][j] > 0 {
                        return false;
                    }

                    // Symmetry condition: zero iff other is zero
                    let is_zero_ij = self.entries[i][j] == 0;
                    let is_zero_ji = self.entries[j][i] == 0;
                    if is_zero_ij != is_zero_ji {
                        return false;
                    }
                }
            }
        }

        true
    }

    /// Check if the Cartan matrix is simply-laced
    ///
    /// A Cartan matrix is simply-laced if all off-diagonal entries are in {0, -1}.
    /// The simply-laced exceptional groups are E₆, E₇, E₈.
    #[must_use]
    pub fn is_simply_laced(&self) -> bool {
        for i in 0..N {
            for j in 0..N {
                if i != j {
                    let entry = self.entries[i][j];
                    if entry != 0 && entry != -1 {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Check if the matrix is symmetric
    ///
    /// A symmetric Cartan matrix corresponds to a simply-laced group.
    #[must_use]
    pub fn is_symmetric(&self) -> bool {
        for i in 0..N {
            for j in 0..N {
                if self.entries[i][j] != self.entries[j][i] {
                    return false;
                }
            }
        }
        true
    }

    /// Compute determinant of the Cartan matrix
    ///
    /// Uses exact integer arithmetic (no floating point).
    /// For small ranks (≤ 8), uses direct computation.
    #[must_use]
    pub fn determinant(&self) -> i64 {
        match N {
            1 => i64::from(self.entries[0][0]),
            2 => {
                let a = i64::from(self.entries[0][0]);
                let b = i64::from(self.entries[0][1]);
                let c = i64::from(self.entries[1][0]);
                let d = i64::from(self.entries[1][1]);
                a * d - b * c
            },
            3 => self.determinant_3x3(),
            4 => self.determinant_4x4(),
            _ => self.determinant_general(),
        }
    }

    /// Determinant for 3×3 matrix
    fn determinant_3x3(&self) -> i64 {
        let m = &self.entries;
        let a = i64::from(m[0][0]);
        let b = i64::from(m[0][1]);
        let c = i64::from(m[0][2]);
        let d = i64::from(m[1][0]);
        let e = i64::from(m[1][1]);
        let f = i64::from(m[1][2]);
        let g = i64::from(m[2][0]);
        let h = i64::from(m[2][1]);
        let i = i64::from(m[2][2]);

        a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)
    }

    /// Determinant for 4×4 matrix
    fn determinant_4x4(&self) -> i64 {
        let m = &self.entries;
        let mut det = 0_i64;

        // Expansion by first row
        for j in 0..4 {
            let sign = if j % 2 == 0 { 1 } else { -1 };
            let cofactor = self.minor_3x3(0, j);
            det += sign * i64::from(m[0][j]) * cofactor;
        }

        det
    }

    /// Compute 3×3 minor (for 4×4 determinant)
    fn minor_3x3(&self, skip_row: usize, skip_col: usize) -> i64 {
        let mut minor = [[0_i8; 3]; 3];
        let mut mi = 0;

        for i in 0..4 {
            if i == skip_row {
                continue;
            }
            let mut mj = 0;
            for j in 0..4 {
                if j == skip_col {
                    continue;
                }
                minor[mi][mj] = self.entries[i][j];
                mj += 1;
            }
            mi += 1;
        }

        let a = i64::from(minor[0][0]);
        let b = i64::from(minor[0][1]);
        let c = i64::from(minor[0][2]);
        let d = i64::from(minor[1][0]);
        let e = i64::from(minor[1][1]);
        let f = i64::from(minor[1][2]);
        let g = i64::from(minor[2][0]);
        let h = i64::from(minor[2][1]);
        let i = i64::from(minor[2][2]);

        a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)
    }

    /// General determinant computation (for larger matrices)
    ///
    /// Uses Laplace expansion (slow but exact)
    fn determinant_general(&self) -> i64 {
        if N == 0 {
            return 1;
        }
        if N == 1 {
            return i64::from(self.entries[0][0]);
        }

        let mut det = 0_i64;

        // Expansion by first row
        for j in 0..N {
            let sign = if j % 2 == 0 { 1 } else { -1 };
            let cofactor = self.minor_general(0, j);
            det += sign * i64::from(self.entries[0][j]) * cofactor;
        }

        det
    }

    /// Compute general minor (recursive)
    fn minor_general(&self, skip_row: usize, skip_col: usize) -> i64 {
        if N <= 1 {
            return 1;
        }

        // Build (N-1)×(N-1) minor matrix
        let mut minor_entries = vec![vec![0_i8; N - 1]; N - 1];
        let mut mi = 0;

        for i in 0..N {
            if i == skip_row {
                continue;
            }
            let mut mj = 0;
            for j in 0..N {
                if j == skip_col {
                    continue;
                }
                minor_entries[mi][mj] = self.entries[i][j];
                mj += 1;
            }
            mi += 1;
        }

        // Recursive determinant computation
        Self::determinant_recursive(&minor_entries, N - 1)
    }

    /// Recursive determinant helper
    fn determinant_recursive(matrix: &[Vec<i8>], size: usize) -> i64 {
        if size == 1 {
            return i64::from(matrix[0][0]);
        }
        if size == 2 {
            let a = i64::from(matrix[0][0]);
            let b = i64::from(matrix[0][1]);
            let c = i64::from(matrix[1][0]);
            let d = i64::from(matrix[1][1]);
            return a * d - b * c;
        }

        let mut det = 0_i64;

        for j in 0..size {
            let sign = if j % 2 == 0 { 1 } else { -1 };

            // Build minor
            let mut minor = vec![vec![0_i8; size - 1]; size - 1];
            for i in 1..size {
                let mut mj = 0;
                for k in 0..size {
                    if k == j {
                        continue;
                    }
                    minor[i - 1][mj] = matrix[i][k];
                    mj += 1;
                }
            }

            det += sign * i64::from(matrix[0][j]) * Self::determinant_recursive(&minor, size - 1);
        }

        det
    }

    /// Find connected components in Dynkin diagram
    ///
    /// Returns the number of connected components.
    /// A connected Cartan matrix has exactly 1 component.
    #[must_use]
    pub fn num_connected_components(&self) -> usize {
        let mut visited = vec![false; N];
        let mut num_components = 0;

        for start in 0..N {
            if !visited[start] {
                // BFS from this node
                let mut queue = vec![start];
                visited[start] = true;

                while let Some(i) = queue.pop() {
                    #[allow(clippy::needless_range_loop)]
                    for j in 0..N {
                        if i != j && !visited[j] && self.entries[i][j] != 0 {
                            visited[j] = true;
                            queue.push(j);
                        }
                    }
                }

                num_components += 1;
            }
        }

        num_components
    }

    /// Check if Cartan matrix is connected (indecomposable)
    #[must_use]
    pub fn is_connected(&self) -> bool {
        self.num_connected_components() == 1
    }

    /// Extract Dynkin diagram from Cartan matrix
    ///
    /// Computes bonds between simple roots based on Cartan matrix entries.
    /// Bond multiplicity is determined by |Cᵢⱼ × Cⱼᵢ|:
    /// - 1 = single bond (—)
    /// - 2 = double bond (⇒) for F₄
    /// - 3 = triple bond (≡) for G₂
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::cartan::CartanMatrix;
    ///
    /// let g2 = CartanMatrix::g2();
    /// let dynkin = g2.to_dynkin_diagram("G₂");
    ///
    /// assert_eq!(dynkin.rank(), 2);
    /// assert_eq!(dynkin.bonds().len(), 1);
    /// assert_eq!(dynkin.bonds()[0].2, 3); // Triple bond
    /// ```
    #[must_use]
    pub fn to_dynkin_diagram(&self, group_name: &str) -> DynkinDiagram<N> {
        DynkinDiagram::from_cartan(self, group_name)
    }
}

/// Standard Cartan matrices for exceptional groups
impl CartanMatrix<2> {
    /// G₂ Cartan matrix
    ///
    /// ```text
    /// [ 2  -3]
    /// [-1   2]
    /// ```
    #[must_use]
    pub const fn g2() -> Self {
        Self::new([[2, -3], [-1, 2]])
    }
}

impl CartanMatrix<4> {
    /// F₄ Cartan matrix
    ///
    /// ```text
    /// [ 2  -1   0   0]
    /// [-1   2  -2   0]
    /// [ 0  -1   2  -1]
    /// [ 0   0  -1   2]
    /// ```
    #[must_use]
    pub const fn f4() -> Self {
        Self::new([[2, -1, 0, 0], [-1, 2, -2, 0], [0, -1, 2, -1], [0, 0, -1, 2]])
    }
}

impl CartanMatrix<6> {
    /// E₆ Cartan matrix
    ///
    /// ```text
    /// [ 2  -1   0   0   0   0]
    /// [-1   2  -1   0   0   0]
    /// [ 0  -1   2  -1   0  -1]
    /// [ 0   0  -1   2  -1   0]
    /// [ 0   0   0  -1   2   0]
    /// [ 0   0  -1   0   0   2]
    /// ```
    #[must_use]
    pub const fn e6() -> Self {
        Self::new([
            [2, -1, 0, 0, 0, 0],
            [-1, 2, -1, 0, 0, 0],
            [0, -1, 2, -1, 0, -1],
            [0, 0, -1, 2, -1, 0],
            [0, 0, 0, -1, 2, 0],
            [0, 0, -1, 0, 0, 2],
        ])
    }
}

impl CartanMatrix<7> {
    /// E₇ Cartan matrix
    ///
    /// ```text
    /// [ 2  -1   0   0   0   0   0]
    /// [-1   2  -1   0   0   0   0]
    /// [ 0  -1   2  -1   0   0   0]
    /// [ 0   0  -1   2  -1   0  -1]
    /// [ 0   0   0  -1   2  -1   0]
    /// [ 0   0   0   0  -1   2   0]
    /// [ 0   0   0  -1   0   0   2]
    /// ```
    #[must_use]
    pub const fn e7() -> Self {
        Self::new([
            [2, -1, 0, 0, 0, 0, 0],
            [-1, 2, -1, 0, 0, 0, 0],
            [0, -1, 2, -1, 0, 0, 0],
            [0, 0, -1, 2, -1, 0, -1],
            [0, 0, 0, -1, 2, -1, 0],
            [0, 0, 0, 0, -1, 2, 0],
            [0, 0, 0, -1, 0, 0, 2],
        ])
    }
}

impl CartanMatrix<8> {
    /// E₈ Cartan matrix
    ///
    /// ```text
    /// [ 2  -1   0   0   0   0   0   0]
    /// [-1   2  -1   0   0   0   0   0]
    /// [ 0  -1   2  -1   0   0   0   0]
    /// [ 0   0  -1   2  -1   0   0   0]
    /// [ 0   0   0  -1   2  -1   0  -1]
    /// [ 0   0   0   0  -1   2  -1   0]
    /// [ 0   0   0   0   0  -1   2   0]
    /// [ 0   0   0   0  -1   0   0   2]
    /// ```
    #[must_use]
    pub const fn e8() -> Self {
        Self::new([
            [2, -1, 0, 0, 0, 0, 0, 0],
            [-1, 2, -1, 0, 0, 0, 0, 0],
            [0, -1, 2, -1, 0, 0, 0, 0],
            [0, 0, -1, 2, -1, 0, 0, 0],
            [0, 0, 0, -1, 2, -1, 0, -1],
            [0, 0, 0, 0, -1, 2, -1, 0],
            [0, 0, 0, 0, 0, -1, 2, 0],
            [0, 0, 0, 0, -1, 0, 0, 2],
        ])
    }
}

// ============================================================================
// Dynkin Diagrams
// ============================================================================

/// Dynkin diagram representation
///
/// A Dynkin diagram is a graph encoding the structure of a Lie algebra.
/// Nodes represent simple roots, edges represent root relationships.
///
/// From certified Python implementation: exact bonds from Cartan matrix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DynkinDiagram<const N: usize> {
    /// Group name (e.g., "G₂", "F₄", "E₆")
    group_name: String,
    /// Rank (number of simple roots)
    rank: usize,
    /// Cartan matrix (exact integers)
    cartan: CartanMatrix<N>,
    /// Bonds: (`from_node`, `to_node`, multiplicity)
    /// Multiplicity: 1=single, 2=double, 3=triple
    bonds: Vec<(usize, usize, u8)>,
    /// Node degrees (connectivity in Dynkin diagram)
    degrees: Vec<usize>,
}

impl<const N: usize> DynkinDiagram<N> {
    /// Create Dynkin diagram from Cartan matrix
    ///
    /// Extracts bond structure using exact formula: multiplicity = |Cᵢⱼ × Cⱼᵢ|
    ///
    /// # Panics
    ///
    /// Panics if the computed multiplicity doesn't fit in `u8` (should never happen for valid Cartan matrices).
    #[must_use]
    pub fn from_cartan(cartan: &CartanMatrix<N>, group_name: &str) -> Self {
        let mut bonds = Vec::new();
        let mut degrees = vec![0; N];

        // Extract bonds from Cartan matrix
        // Only check upper triangle to avoid duplicates
        for i in 0..N {
            for j in (i + 1)..N {
                let c_ij = cartan.get(i, j);
                let c_ji = cartan.get(j, i);

                // Bond exists if both entries are non-zero
                if c_ij != 0 && c_ji != 0 {
                    // Multiplicity = |Cᵢⱼ × Cⱼᵢ| (exact integer arithmetic)
                    let product = i32::from(c_ij) * i32::from(c_ji);
                    let multiplicity = u8::try_from(product.unsigned_abs())
                        .expect("multiplicity should fit in u8");

                    bonds.push((i, j, multiplicity));

                    // Update degrees
                    degrees[i] += 1;
                    degrees[j] += 1;
                }
            }
        }

        Self { group_name: group_name.to_string(), rank: N, cartan: *cartan, bonds, degrees }
    }

    /// Get rank (number of simple roots)
    #[must_use]
    pub const fn rank(&self) -> usize {
        self.rank
    }

    /// Get group name
    #[must_use]
    pub fn group_name(&self) -> &str {
        &self.group_name
    }

    /// Get bonds: (`from_node`, `to_node`, multiplicity)
    #[must_use]
    pub fn bonds(&self) -> &[(usize, usize, u8)] {
        &self.bonds
    }

    /// Get node degree (number of bonds to this node)
    #[must_use]
    pub fn degree(&self, node: usize) -> usize {
        self.degrees[node]
    }

    /// Get all node degrees
    #[must_use]
    pub fn degrees(&self) -> &[usize] {
        &self.degrees
    }

    /// Get Cartan matrix
    #[must_use]
    pub const fn cartan_matrix(&self) -> &CartanMatrix<N> {
        &self.cartan
    }

    /// Check if diagram is connected
    #[must_use]
    pub fn is_connected(&self) -> bool {
        if N == 0 {
            return true;
        }

        // BFS to check connectivity
        let mut visited = vec![false; N];
        let mut queue = vec![0];
        visited[0] = true;
        let mut count = 1;

        while let Some(node) = queue.pop() {
            // Check all bonds involving this node
            for &(i, j, _) in &self.bonds {
                let neighbor = if i == node {
                    Some(j)
                } else if j == node {
                    Some(i)
                } else {
                    None
                };

                if let Some(n) = neighbor {
                    if !visited[n] {
                        visited[n] = true;
                        queue.push(n);
                        count += 1;
                    }
                }
            }
        }

        count == N
    }

    /// Get indices of branch nodes (nodes with degree ≥ 3)
    ///
    /// Branch nodes are the vertices where the Dynkin diagram branches.
    /// For E₆, E₇, E₈, there is exactly one branch node.
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::cartan::CartanMatrix;
    ///
    /// let e6 = CartanMatrix::e6();
    /// let dynkin = e6.to_dynkin_diagram("E₆");
    /// let branches = dynkin.branch_nodes();
    ///
    /// assert_eq!(branches.len(), 1, "E₆ has exactly 1 branch node");
    /// ```
    #[must_use]
    pub fn branch_nodes(&self) -> Vec<usize> {
        self.degrees
            .iter()
            .enumerate()
            .filter(|(_, &deg)| deg >= 3)
            .map(|(i, _)| i)
            .collect()
    }

    /// Get indices of endpoint nodes (nodes with degree 1)
    ///
    /// Endpoints are the terminal vertices of the Dynkin diagram.
    /// For E₆, there are 3 endpoints (the three arms of the diagram).
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::cartan::CartanMatrix;
    ///
    /// let e6 = CartanMatrix::e6();
    /// let dynkin = e6.to_dynkin_diagram("E₆");
    /// let endpoints = dynkin.endpoints();
    ///
    /// assert_eq!(endpoints.len(), 3, "E₆ has 3 endpoints");
    /// ```
    #[must_use]
    pub fn endpoints(&self) -> Vec<usize> {
        self.degrees
            .iter()
            .enumerate()
            .filter(|(_, &deg)| deg == 1)
            .map(|(i, _)| i)
            .collect()
    }

    /// Get indices of middle nodes (nodes with degree 2)
    ///
    /// Middle nodes are non-branching, non-terminal vertices.
    ///
    /// # Examples
    ///
    /// ```
    /// use atlas_embeddings::cartan::CartanMatrix;
    ///
    /// let e6 = CartanMatrix::e6();
    /// let dynkin = e6.to_dynkin_diagram("E₆");
    /// let middle = dynkin.middle_nodes();
    ///
    /// assert_eq!(middle.len(), 2, "E₆ has 2 middle nodes");
    /// ```
    #[must_use]
    pub fn middle_nodes(&self) -> Vec<usize> {
        self.degrees
            .iter()
            .enumerate()
            .filter(|(_, &deg)| deg == 2)
            .map(|(i, _)| i)
            .collect()
    }

    /// Generate ASCII diagram representation
    ///
    /// Creates a text visualization of the Dynkin diagram with proper bond notation:
    /// - Single bond: —
    /// - Double bond: ⇒
    /// - Triple bond: ≡
    #[must_use]
    pub fn to_ascii(&self) -> String {
        // Generate ASCII based on group structure
        // This matches the certified Python implementation's diagram format
        match self.group_name.as_str() {
            "G₂" => Self::ascii_g2(),
            "F₄" => Self::ascii_f4(),
            "E₆" => Self::ascii_e6(),
            "E₇" => Self::ascii_e7(),
            "E₈" => Self::ascii_e8(),
            _ => self.ascii_generic(),
        }
    }

    /// Generate G₂ ASCII diagram
    fn ascii_g2() -> String {
        "\nG₂ Dynkin Diagram (rank 2):\n\n  α₁ o≡≡≡o α₂\n\nTriple bond: |C₁₂ × C₂₁| = 3\n\
             Short root (α₁) connected to long root (α₂)\n"
            .to_string()
    }

    /// Generate F₄ ASCII diagram
    fn ascii_f4() -> String {
        "\nF₄ Dynkin Diagram (rank 4):\n\n  α₁ o---o α₂ ⇒ α₃ o---o α₄\n\n\
             Double bond (⇒): |C₂₃ × C₃₂| = 2\n\
             Arrow points from short to long roots\n"
            .to_string()
    }

    /// Generate E₆ ASCII diagram
    fn ascii_e6() -> String {
        "\nE₆ Dynkin Diagram (rank 6):\n\n          α₂\n          o\n          |\n  \
             α₁ o---o α₀ ---o α₃ ---o α₄ ---o α₅\n\n\
             Branching structure: central node (α₀) has degree 3\n\
             Simply-laced: all single bonds\n"
            .to_string()
    }

    /// Generate E₇ ASCII diagram
    fn ascii_e7() -> String {
        "\nE₇ Dynkin Diagram (rank 7):\n\n              α₆\n              o\n              |\n  \
             α₀ o---o α₁ ---o α₂ ---o α₃ ---o α₄ ---o α₅\n\n\
             Extended E₆ structure\n\
             Simply-laced: all single bonds\n"
            .to_string()
    }

    /// Generate E₈ ASCII diagram
    fn ascii_e8() -> String {
        "\nE₈ Dynkin Diagram (rank 8):\n\n                  α₇\n                  o\n                  |\n  \
             α₀ o---o α₁ ---o α₂ ---o α₃ ---o α₄ ---o α₅ ---o α₆\n\n\
             Largest exceptional group\n\
             Simply-laced: all single bonds\n".to_string()
    }

    /// Generate generic ASCII diagram (for unknown groups)
    fn ascii_generic(&self) -> String {
        use std::fmt::Write as _;
        let mut diagram = format!("\n{} Dynkin Diagram (rank {}):\n\n", self.group_name, N);

        // Simple linear representation
        diagram.push_str("  ");
        for i in 0..N {
            write!(diagram, "α{i}").unwrap();
            if i < N - 1 {
                diagram.push_str(" o");
                // Find bond to next node
                let bond = self
                    .bonds
                    .iter()
                    .find(|(a, b, _)| (*a == i && *b == i + 1) || (*a == i + 1 && *b == i));
                match bond {
                    Some((_, _, 1)) => diagram.push_str("---"),
                    Some((_, _, 2)) => diagram.push_str("==>"),
                    Some((_, _, 3)) => diagram.push_str("≡≡≡"),
                    _ => diagram.push_str("   "),
                }
                diagram.push_str("o ");
            }
        }
        diagram.push('\n');

        // List bonds
        if !self.bonds.is_empty() {
            diagram.push_str("\nBonds:\n");
            for (i, j, mult) in &self.bonds {
                writeln!(diagram, "  α{i} ↔ α{j} (multiplicity {mult})").unwrap();
            }
        }

        diagram
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_g2_cartan() {
        let g2 = CartanMatrix::g2();
        assert_eq!(g2.rank(), 2);
        assert!(g2.is_valid());
        assert!(!g2.is_simply_laced());
        assert!(!g2.is_symmetric());
        assert_eq!(g2.determinant(), 1);
        assert!(g2.is_connected());
    }

    #[test]
    fn test_f4_cartan() {
        let f4 = CartanMatrix::f4();
        assert_eq!(f4.rank(), 4);
        assert!(f4.is_valid());
        assert!(!f4.is_simply_laced());
        assert!(!f4.is_symmetric());
        assert_eq!(f4.determinant(), 1);
        assert!(f4.is_connected());
    }

    #[test]
    fn test_e6_cartan() {
        let e6 = CartanMatrix::e6();
        assert_eq!(e6.rank(), 6);
        assert!(e6.is_valid());
        assert!(e6.is_simply_laced());
        assert!(e6.is_symmetric());
        assert_eq!(e6.determinant(), 3);
        assert!(e6.is_connected());
    }

    #[test]
    fn test_e7_cartan() {
        let e7 = CartanMatrix::e7();
        assert_eq!(e7.rank(), 7);
        assert!(e7.is_valid());
        assert!(e7.is_simply_laced());
        assert!(e7.is_symmetric());
        assert_eq!(e7.determinant(), 2);
        assert!(e7.is_connected());
    }

    #[test]
    fn test_e8_cartan() {
        let e8 = CartanMatrix::e8();
        assert_eq!(e8.rank(), 8);
        assert!(e8.is_valid());
        assert!(e8.is_simply_laced());
        assert!(e8.is_symmetric());
        assert_eq!(e8.determinant(), 1);
        assert!(e8.is_connected());
    }

    #[test]
    fn test_cartan_validity() {
        // Invalid: diagonal not 2
        let invalid = CartanMatrix::new([[1, 0], [0, 2]]);
        assert!(!invalid.is_valid());

        // Invalid: positive off-diagonal
        let invalid2 = CartanMatrix::new([[2, 1], [1, 2]]);
        assert!(!invalid2.is_valid());

        // Invalid: asymmetric zeros
        let invalid3 = CartanMatrix::new([[2, 0], [-1, 2]]);
        assert!(!invalid3.is_valid());
    }

    #[test]
    fn test_simply_laced() {
        // Simply-laced: all off-diagonal in {0, -1}
        let sl = CartanMatrix::new([[2, -1], [-1, 2]]);
        assert!(sl.is_simply_laced());

        // Not simply-laced: has -2
        let nsl = CartanMatrix::new([[2, -2], [-1, 2]]);
        assert!(!nsl.is_simply_laced());

        // Not simply-laced: has -3
        let nsl2 = CartanMatrix::new([[2, -3], [-1, 2]]);
        assert!(!nsl2.is_simply_laced());
    }

    #[test]
    fn test_determinant_2x2() {
        let m = CartanMatrix::new([[2, -1], [-1, 2]]);
        assert_eq!(m.determinant(), 3);
    }

    #[test]
    fn test_connected_components() {
        // Disconnected: two A₁ components
        let disconnected = CartanMatrix::new([[2, 0], [0, 2]]);
        assert_eq!(disconnected.num_connected_components(), 2);
        assert!(!disconnected.is_connected());

        // Connected
        let connected = CartanMatrix::new([[2, -1], [-1, 2]]);
        assert_eq!(connected.num_connected_components(), 1);
        assert!(connected.is_connected());
    }

    // ========================================================================
    // Dynkin Diagram Tests
    // ========================================================================

    #[test]
    fn test_dynkin_g2_triple_bond() {
        let g2 = CartanMatrix::g2();
        let dynkin = g2.to_dynkin_diagram("G₂");

        assert_eq!(dynkin.rank(), 2);
        assert_eq!(dynkin.group_name(), "G₂");
        assert!(dynkin.is_connected());

        // G₂ has exactly 1 bond with multiplicity 3
        let bonds = dynkin.bonds();
        assert_eq!(bonds.len(), 1, "G₂ has 1 bond");
        assert_eq!(bonds[0].2, 3, "G₂ triple bond: |C₁₂ × C₂₁| = |-3 × -1| = 3");

        // Both nodes have degree 1 (single connection)
        assert_eq!(dynkin.degree(0), 1);
        assert_eq!(dynkin.degree(1), 1);

        // Verify ASCII output contains key elements
        let ascii = dynkin.to_ascii();
        assert!(ascii.contains("G₂"));
        assert!(ascii.contains("Triple bond"));
    }

    #[test]
    fn test_dynkin_f4_double_bond() {
        let f4 = CartanMatrix::f4();
        let dynkin = f4.to_dynkin_diagram("F₄");

        assert_eq!(dynkin.rank(), 4);
        assert_eq!(dynkin.group_name(), "F₄");
        assert!(dynkin.is_connected());

        // F₄ has 3 bonds: one double, two single
        let bonds = dynkin.bonds();
        assert_eq!(bonds.len(), 3, "F₄ has 3 bonds");

        // Find the double bond (multiplicity 2)
        let double_bond = bonds.iter().find(|(_, _, m)| *m == 2);
        assert!(double_bond.is_some(), "F₄ has a double bond");

        let double = double_bond.unwrap();
        assert_eq!(double.2, 2, "F₄ double bond: |C₂₃ × C₃₂| = |-2 × -1| = 2");

        // Verify node degrees: linear chain means middle nodes have degree 2
        assert_eq!(dynkin.degree(0), 1, "Endpoint");
        assert_eq!(dynkin.degree(1), 2, "Middle");
        assert_eq!(dynkin.degree(2), 2, "Middle");
        assert_eq!(dynkin.degree(3), 1, "Endpoint");

        // Verify ASCII output
        let ascii = dynkin.to_ascii();
        assert!(ascii.contains("F₄"));
        assert!(ascii.contains("Double bond"));
    }

    #[test]
    fn test_dynkin_e6_simply_laced() {
        let e6 = CartanMatrix::e6();
        let dynkin = e6.to_dynkin_diagram("E₆");

        assert_eq!(dynkin.rank(), 6);
        assert_eq!(dynkin.group_name(), "E₆");
        assert!(dynkin.is_connected());

        // E₆ tree structure: 6 nodes → 5 bonds (rank - 1)
        let bonds = dynkin.bonds();
        assert_eq!(bonds.len(), 5, "E₆ has 5 bonds (tree with 6 nodes)");

        // All bonds must be single (multiplicity 1)
        for &(_, _, mult) in bonds {
            assert_eq!(mult, 1, "E₆ is simply-laced: all bonds are single");
        }

        // E₆ Dynkin structure: 1 central node (degree 3), 3 endpoints (degree 1), 2 middle (degree 2)
        let degrees = dynkin.degrees();
        let deg_1_count = degrees.iter().filter(|&&d| d == 1).count();
        let deg_2_count = degrees.iter().filter(|&&d| d == 2).count();
        let deg_3_count = degrees.iter().filter(|&&d| d == 3).count();

        assert_eq!(deg_1_count, 3, "E₆ has 3 endpoints");
        assert_eq!(deg_2_count, 2, "E₆ has 2 middle nodes");
        assert_eq!(deg_3_count, 1, "E₆ has 1 branch node");

        // Verify ASCII output
        let ascii = dynkin.to_ascii();
        assert!(ascii.contains("E₆"));
        assert!(ascii.contains("Branching structure"));
    }

    #[test]
    fn test_dynkin_e7_simply_laced() {
        let e7 = CartanMatrix::e7();
        let dynkin = e7.to_dynkin_diagram("E₇");

        assert_eq!(dynkin.rank(), 7);
        assert!(dynkin.is_connected());

        // E₇ tree structure: 7 nodes → 6 bonds (rank - 1)
        let bonds = dynkin.bonds();
        assert_eq!(bonds.len(), 6, "E₇ has 6 bonds (tree with 7 nodes)");

        for &(_, _, mult) in bonds {
            assert_eq!(mult, 1, "E₇ is simply-laced");
        }

        // Verify ASCII output
        let ascii = dynkin.to_ascii();
        assert!(ascii.contains("E₇"));
    }

    #[test]
    fn test_dynkin_e8_simply_laced() {
        let e8 = CartanMatrix::e8();
        let dynkin = e8.to_dynkin_diagram("E₈");

        assert_eq!(dynkin.rank(), 8);
        assert!(dynkin.is_connected());

        // E₈ tree structure: 8 nodes → 7 bonds (rank - 1)
        let bonds = dynkin.bonds();
        assert_eq!(bonds.len(), 7, "E₈ has 7 bonds (tree with 8 nodes)");

        for &(_, _, mult) in bonds {
            assert_eq!(mult, 1, "E₈ is simply-laced");
        }

        // E₈ Dynkin structure: 3 endpoints, 4 middle, 1 branch
        let degrees = dynkin.degrees();
        let deg_1_count = degrees.iter().filter(|&&d| d == 1).count();
        let deg_2_count = degrees.iter().filter(|&&d| d == 2).count();
        let deg_3_count = degrees.iter().filter(|&&d| d == 3).count();

        assert_eq!(deg_1_count, 3, "E₈ has 3 endpoints");
        assert_eq!(deg_2_count, 4, "E₈ has 4 middle nodes");
        assert_eq!(deg_3_count, 1, "E₈ has 1 branch node");

        // Verify ASCII output
        let ascii = dynkin.to_ascii();
        assert!(ascii.contains("E₈"));
    }

    #[test]
    fn test_dynkin_bond_extraction_exact() {
        // Test exact formula: multiplicity = |C_ij × C_ji|

        // G₂: C[0,1] = -3, C[1,0] = -1 → |-3 × -1| = 3
        let g2 = CartanMatrix::g2();
        let g2_diagram = g2.to_dynkin_diagram("G₂");
        assert_eq!(g2_diagram.bonds()[0].2, 3);

        // F₄: C[1,2] = -2, C[2,1] = -1 → |-2 × -1| = 2
        let f4 = CartanMatrix::f4();
        let f4_diagram = f4.to_dynkin_diagram("F₄");
        let double = f4_diagram.bonds().iter().find(|(_, _, m)| *m == 2).unwrap();
        assert_eq!(double.2, 2);

        // E₆: all C[i,j] × C[j,i] = -1 × -1 = 1 (simply-laced)
        let e6 = CartanMatrix::e6();
        let e6_diagram = e6.to_dynkin_diagram("E₆");
        for &(i, j, mult) in e6_diagram.bonds() {
            let c_ij = e6.get(i, j);
            let c_ji = e6.get(j, i);
            let expected = u8::try_from((i32::from(c_ij) * i32::from(c_ji)).unsigned_abs())
                .expect("multiplicity should fit in u8");
            assert_eq!(mult, expected, "Bond ({i},{j}) multiplicity");
        }
    }

    #[test]
    fn test_dynkin_degrees_from_bonds() {
        // Verify that degrees are computed correctly from bonds

        // A₂: two nodes, one bond → both degree 1
        let a2 = CartanMatrix::new([[2, -1], [-1, 2]]);
        let dynkin = a2.to_dynkin_diagram("A₂");
        assert_eq!(dynkin.degree(0), 1);
        assert_eq!(dynkin.degree(1), 1);

        // A₃: three nodes in a line → endpoints degree 1, middle degree 2
        let a3 = CartanMatrix::new([[2, -1, 0], [-1, 2, -1], [0, -1, 2]]);
        let dynkin = a3.to_dynkin_diagram("A₃");
        assert_eq!(dynkin.degree(0), 1);
        assert_eq!(dynkin.degree(1), 2);
        assert_eq!(dynkin.degree(2), 1);
    }

    #[test]
    fn test_dynkin_connectivity() {
        // All exceptional group Dynkin diagrams are connected
        assert!(CartanMatrix::g2().to_dynkin_diagram("G₂").is_connected());
        assert!(CartanMatrix::f4().to_dynkin_diagram("F₄").is_connected());
        assert!(CartanMatrix::e6().to_dynkin_diagram("E₆").is_connected());
        assert!(CartanMatrix::e7().to_dynkin_diagram("E₇").is_connected());
        assert!(CartanMatrix::e8().to_dynkin_diagram("E₈").is_connected());

        // Disconnected example: A₁ × A₁
        let disconnected = CartanMatrix::new([[2, 0], [0, 2]]);
        let dynkin = disconnected.to_dynkin_diagram("A₁×A₁");
        assert!(!dynkin.is_connected(), "Disconnected Dynkin diagram");
    }

    #[test]
    fn test_dynkin_helper_methods() {
        // E₆: 1 branch, 3 endpoints, 2 middle
        let e6 = CartanMatrix::e6().to_dynkin_diagram("E₆");
        assert_eq!(e6.branch_nodes().len(), 1, "E₆ has 1 branch node");
        assert_eq!(e6.endpoints().len(), 3, "E₆ has 3 endpoints");
        assert_eq!(e6.middle_nodes().len(), 2, "E₆ has 2 middle nodes");

        // E₇: 1 branch, 3 endpoints, 3 middle
        let e7 = CartanMatrix::e7().to_dynkin_diagram("E₇");
        assert_eq!(e7.branch_nodes().len(), 1, "E₇ has 1 branch node");
        assert_eq!(e7.endpoints().len(), 3, "E₇ has 3 endpoints");
        assert_eq!(e7.middle_nodes().len(), 3, "E₇ has 3 middle nodes");

        // E₈: 1 branch, 3 endpoints, 4 middle
        let e8 = CartanMatrix::e8().to_dynkin_diagram("E₈");
        assert_eq!(e8.branch_nodes().len(), 1, "E₈ has 1 branch node");
        assert_eq!(e8.endpoints().len(), 3, "E₈ has 3 endpoints");
        assert_eq!(e8.middle_nodes().len(), 4, "E₈ has 4 middle nodes");

        // G₂: no branching (linear)
        let g2 = CartanMatrix::g2().to_dynkin_diagram("G₂");
        assert_eq!(g2.branch_nodes().len(), 0, "G₂ has no branch nodes");
        assert_eq!(g2.endpoints().len(), 2, "G₂ has 2 endpoints");

        // F₄: no branching (linear)
        let f4 = CartanMatrix::f4().to_dynkin_diagram("F₄");
        assert_eq!(f4.branch_nodes().len(), 0, "F₄ has no branch nodes");
        assert_eq!(f4.endpoints().len(), 2, "F₄ has 2 endpoints");
        assert_eq!(f4.middle_nodes().len(), 2, "F₄ has 2 middle nodes");
    }
}
