set_option autoImplicit true
namespace Formal

/-- Stub rational type; swap to ℚ later. -/
constant Q : Type

/-- Distinguished elements mimicking -1 and 2. -/
constant q_neg_one : Q
constant q_two : Q

/-- 8D vectors over Q. -/
abbrev Vector8 := (Fin 8 → Q)

/-- Inner product, abstract. -/
constant ip : Vector8 → Vector8 → Q

/-- Predicate on Q (adjacency test). -/
abbrev Phi := Q → Prop

end Formal
