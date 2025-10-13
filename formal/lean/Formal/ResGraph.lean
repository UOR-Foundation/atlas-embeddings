set_option autoImplicit true
namespace Formal
open Classical

structure ResGraph where
  V  : Type
  E  : V → V → Prop
  λ  : V → Vector8
  U  : Set V
  Φ  : Phi
  /-- Edge iff Φ(ip(λ u, λ v)). -/
  Φ_spec : ∀ u v, E u v ↔ Φ (ip (λ u) (λ v))

structure Morphism (A B : ResGraph) where
  f : A.V → B.V
  w : Vector8 → Vector8
  hom : ∀ u v, A.E u v → B.E (f u) (f v)
  label_compat : ∀ u, B.λ (f u) = w (A.λ u)
  unity : ∀ u, u ∈ A.U → f u ∈ B.U

end Formal
