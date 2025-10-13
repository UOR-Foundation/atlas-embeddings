set_option autoImplicit true
namespace Formal
open Classical

/-- E8 embedding theorem (shape only). -/
axiom Atlas_to_E8_embedding
  (A : ResGraph)
  (hΦ : A.Φ = PhiAtlas)
  (hV : Fintype A.V) :
  ∃ f : A.V → Vector8,
    Function.Injective f ∧
    (∀ u, RE8 (f u)) ∧
    (∀ u v, A.E u v ↔ ip (f u) (f v) = q_neg_one)

end Formal
