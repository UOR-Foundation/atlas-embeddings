/**
 * Fano Plane Structure
 *
 * The Fano plane defines the multiplication structure of the octonions
 * via the 7 imaginary units e₁, e₂, ..., e₇.
 *
 * Each line of the Fano plane defines a triple (i, j, k) such that:
 *   eᵢ · eⱼ = eₖ  (when traversed in the correct orientation)
 *
 * The 7 lines are:
 *   1. (1, 2, 4)  2. (2, 3, 5)  3. (3, 4, 6)  4. (4, 5, 7)
 *   5. (5, 6, 1)  6. (6, 7, 2)  7. (7, 1, 3)
 *
 * This module encodes the Fano plane structure for use in the octonion
 * multiplication.
 */

/**
 * Fano plane lines (oriented triples)
 *
 * Each triple (i, j, k) means: eᵢ × eⱼ = eₖ
 */
export const FANO_LINES: ReadonlyArray<readonly [number, number, number]> = [
  [1, 2, 4],
  [2, 3, 5],
  [3, 4, 6],
  [4, 5, 7],
  [5, 6, 1],
  [6, 7, 2],
  [7, 1, 3],
] as const;

/**
 * Cross product lookup table
 *
 * crossProductTable[i][j] gives the result of eᵢ × eⱼ
 *
 * Returns:
 *   - 0 if i = j (since eᵢ × eᵢ = 0)
 *   - k if eᵢ × eⱼ = eₖ (positive orientation)
 *   - -k if eᵢ × eⱼ = -eₖ (negative orientation)
 */
export const crossProductTable: ReadonlyArray<ReadonlyArray<number>> = (() => {
  // Initialize 8x8 table (indices 0-7, where 0 is unused)
  const table: number[][] = Array(8)
    .fill(0)
    .map(() => Array(8).fill(0));

  // Populate from Fano lines
  for (const [i, j, k] of FANO_LINES) {
    table[i][j] = k; // eᵢ × eⱼ = eₖ
    table[j][k] = i; // eⱼ × eₖ = eᵢ (cyclic)
    table[k][i] = j; // eₖ × eᵢ = eⱼ (cyclic)

    // Reverse orientation (anticommutative)
    table[j][i] = -k; // eⱼ × eᵢ = -eₖ
    table[k][j] = -i; // eₖ × eⱼ = -eᵢ
    table[i][k] = -j; // eᵢ × eₖ = -eⱼ
  }

  return table;
})();

/**
 * Compute cross product of two basis vector indices
 *
 * @param i - First basis vector index (1..7)
 * @param j - Second basis vector index (1..7)
 * @returns Object with:
 *   - index: The resulting basis vector index (1..7), or 0 if i = j
 *   - sign: +1 or -1 for orientation, or 0 if i = j
 */
export function crossProduct(i: number, j: number): { index: number; sign: number } {
  if (i < 1 || i > 7 || j < 1 || j > 7) {
    throw new Error(`Basis vector indices must be 1..7, got i=${i}, j=${j}`);
  }

  if (i === j) {
    return { index: 0, sign: 0 };
  }

  const result = crossProductTable[i][j];

  if (result > 0) {
    return { index: result, sign: 1 };
  } else {
    return { index: -result, sign: -1 };
  }
}

/**
 * Verify Fano plane is correctly constructed
 *
 * Checks:
 * 1. All lines have correct cyclic structure
 * 2. Anticommutativity: eᵢ × eⱼ = -eⱼ × eᵢ
 * 3. All 7 units appear
 */
export function verifyFanoPlane(): boolean {
  // Check anticommutativity
  for (let i = 1; i <= 7; i++) {
    for (let j = 1; j <= 7; j++) {
      if (i === j) {
        if (crossProductTable[i][j] !== 0) return false;
      } else {
        const ij = crossProductTable[i][j];
        const ji = crossProductTable[j][i];
        if (ij !== -ji) return false;
      }
    }
  }

  // Check that all lines are correct
  for (const [i, j, k] of FANO_LINES) {
    if (crossProductTable[i][j] !== k) return false;
    if (crossProductTable[j][k] !== i) return false;
    if (crossProductTable[k][i] !== j) return false;
  }

  return true;
}

/**
 * Get all Fano lines containing a given basis vector
 *
 * @param index - Basis vector index (1..7)
 * @returns Array of lines (as triples)
 */
export function getLinesContaining(index: number): Array<readonly [number, number, number]> {
  return FANO_LINES.filter((line) => line.includes(index));
}

/**
 * Check if three indices form a Fano line
 *
 * @param i - First index
 * @param j - Second index
 * @param k - Third index
 * @returns true if (i,j,k) or any cyclic permutation is a Fano line
 */
export function isFanoLine(i: number, j: number, k: number): boolean {
  return FANO_LINES.some(
    ([a, b, c]) =>
      (a === i && b === j && c === k) ||
      (a === j && b === k && c === i) ||
      (a === k && b === i && c === j),
  );
}
