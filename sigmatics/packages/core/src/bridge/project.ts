/**
 * Project: SGA Element → Class Index
 *
 * This module implements the project function that attempts to convert
 * SGA elements back to class indices.
 *
 * Only rank-1 basis elements can be projected back to classes.
 * Higher-grade elements return null.
 *
 * For rank-1 element E_{h,d,ℓ} = r^h ⊗ e_ℓ ⊗ τ^d:
 *   classIndex = 24*h + 8*d + ℓ
 */

import type { SgaElement } from '../sga/types';
import { EPSILON } from '../sga/types';
import { extractZ4Power, extractZ3Power } from '../sga/group-algebras';
import { componentsToClassIndex } from '../class-system/class';

/**
 * Extract the Clifford index ℓ from a Clifford element
 *
 * Returns:
 *   - 0 if the element is scalar (identity)
 *   - k (1..7) if the element is basis vector e_k
 *   - null otherwise
 */
function extractCliffordIndex(clifford: { grades: Map<string, number> }): number | null {
  const entries = Array.from(clifford.grades.entries());

  // Must have exactly one non-zero grade
  if (entries.length !== 1) return null;

  const [blade, coeff] = entries[0];

  // Coefficient must be 1 (or very close to 1)
  if (Math.abs(coeff - 1) >= EPSILON) return null;

  // Check if scalar
  if (blade === '1') return 0;

  // Check if basis vector e_k
  const match = blade.match(/^e(\d)$/);
  if (!match) return null;

  const index = parseInt(match[1], 10);
  if (index < 1 || index > 7) return null;

  return index;
}

/**
 * Project an SGA element to a class index
 *
 * Returns the class index if the element is a rank-1 basis element,
 * otherwise returns null.
 *
 * @param element - SGA element
 * @returns Class index (0..95) or null if not rank-1
 */
export function project(element: SgaElement): number | null {
  // Extract h from Z4 component
  const h = extractZ4Power(element.z4);
  if (h === null) return null;

  // Extract d from Z3 component
  const d = extractZ3Power(element.z3);
  if (d === null) return null;

  // Extract ℓ from Clifford component
  const l = extractCliffordIndex(element.clifford);
  if (l === null) return null;

  // Convert to class index
  return componentsToClassIndex({
    h2: h as 0 | 1 | 2 | 3,
    d: d as 0 | 1 | 2,
    l: l as 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7,
  });
}

/**
 * Check if an SGA element is a rank-1 basis element
 *
 * @param element - SGA element
 * @returns true if element is rank-1 (can be projected to a class)
 */
export function isRank1(element: SgaElement): boolean {
  return project(element) !== null;
}

/**
 * Project multiple SGA elements
 *
 * @param elements - Array of SGA elements
 * @returns Array of class indices (or null for non-rank-1 elements)
 */
export function projectMultiple(elements: SgaElement[]): (number | null)[] {
  return elements.map((e) => project(e));
}

/**
 * Project with error on non-rank-1
 *
 * Like project(), but throws an error instead of returning null
 * if the element is not rank-1.
 *
 * @param element - SGA element
 * @returns Class index (0..95)
 * @throws Error if element is not rank-1
 */
export function projectStrict(element: SgaElement): number {
  const result = project(element);
  if (result === null) {
    throw new Error('Cannot project non-rank-1 element to class index');
  }
  return result;
}
