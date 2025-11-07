/-
Copyright (c) 2025 Atlas Embeddings Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Atlas Embeddings: Exceptional Lie Groups from First Principles

This is a Lean 4 formalization of the exceptional Lie groups (G₂, F₄, E₆, E₇, E₈)
constructed from the Atlas of Resonance Classes using categorical operations.

**NO `sorry` POLICY**: Every theorem in this formalization is proven.
This is achievable because:
1. All data is explicitly constructed (240 E₈ roots, 96 Atlas vertices)
2. All properties are decidable on finite domains
3. Lean tactics (`decide`, `norm_num`, `fin_cases`, `rfl`) can verify automatically

## Module Structure

- `AtlasEmbeddings.Arithmetic` - Exact rational arithmetic (ℚ, half-integers, vectors)
- `AtlasEmbeddings.E8` - E₈ root system (240 roots, exact coordinates)
- `AtlasEmbeddings.Atlas` - Atlas graph (96 vertices from action functional)
- `AtlasEmbeddings.Embedding` - Atlas → E₈ embedding verification
- `AtlasEmbeddings.Category` - ResGraph category and initiality
- `AtlasEmbeddings.Groups` - Exceptional group constructions (G₂, F₄, E₆, E₇, E₈)
- `AtlasEmbeddings.ELayer` - E-layer extraspecial group and Heisenberg formalization

## Mathematical Foundation Modules

- `Math.Heisenberg.Core` - Heisenberg group H(n) with cocycle multiplication
- `Math.Heisenberg.StoneVonNeumannProof` - Stone-von Neumann theorem (axiomatized)
- `Math.Heisenberg.SanityTests` - Basic property verification
- `Math.Pauli.Commutator` - Pauli commutator relations
- `Math.Clifford.Normalizer` - Clifford normalizer and symplectic group
- `Math.Clifford.KernelProof` - Kernel theorem: Aut(H)/Inn ≅ Sp(2n, F₂)

## References

The Rust implementation serves as the computational certificate:
https://github.com/yourorg/atlas-embeddings
-/

-- Core modules (implemented in phases)
import AtlasEmbeddings.Arithmetic
import AtlasEmbeddings.E8
import AtlasEmbeddings.Atlas
import AtlasEmbeddings.Embedding
import AtlasEmbeddings.Groups
import AtlasEmbeddings.CategoricalFunctors
import AtlasEmbeddings.Completeness
import AtlasEmbeddings.ActionFunctional

-- Mathematical foundation modules for E-layer
import Math.Heisenberg.Core
import Math.Heisenberg.StoneVonNeumannProof
import Math.Heisenberg.SanityTests
import Math.Pauli.Commutator
import Math.Clifford.Normalizer
import Math.Clifford.KernelProof

-- E-layer connection to Atlas
import AtlasEmbeddings.ELayer
