set_option autoImplicit true
namespace Formal
open Classical

/-- Set of E8 roots as abstract subset of Vector8. -/
constant RE8 : Set Vector8

/-- E8 axiom stubs. Fill later with concrete model. -/
axiom norm_two    : ∀ r ∈ RE8, ip r r = q_two
axiom ip_range    : ∀ {r s}, r ∈ RE8 → s ∈ RE8 → True

/-- +1 adjacency on a 96-subset view (auxiliary). -/
def AdjPlus1 (S : Set Vector8) (x y : Vector8) : Prop := True

end Formal
