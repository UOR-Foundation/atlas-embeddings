set_option autoImplicit true
namespace Formal

/-- Reflection-closure RC. -/
constant RC : ResGraph → ResGraph

/-- Resonance product ⊠. -/
constant Prod : ResGraph → ResGraph → ResGraph
infixl:70 " ⊠ " => Prod

/-- Quotient by symmetry family. -/
constant QuotientBy : ResGraph → ResGraph

/-- Filtration and augmentation. -/
constant FilterV : ResGraph → ResGraph
constant AugmentV : ResGraph → ResGraph

/-- Lemma stubs (to be proved later). -/
axiom RC_preserves_Phi (A : ResGraph) : (RC A).Φ = A.Φ
axiom Product_Phi_eq  (A B : ResGraph) : (A ⊠ B).Φ = A.Φ

end Formal
