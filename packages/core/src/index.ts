/**
 * Sigmatics Core Package
 * Main entry point - re-exports all modules
 */

// Main API
export { Atlas } from './api';
export { default } from './api';

// Types
export * from './types';

// Lexer
export * from './lexer';

// Parser
export * from './parser';

// Evaluator
export * from './evaluator';

// Class System
export * from './class-system';

// v0.3.0: SGA (Sigmatics Geometric Algebra)
export * as SGA from './sga';
export * as Bridge from './bridge';

// Re-export key SGA types
export type { SgaElement, Cl07Element, Z4Element, Z3Element, Rank1Basis } from './sga/types';
