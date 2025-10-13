From Formal Require Import Prelude Types.

Parameter RE8 : Vector8 -> Prop.
Axiom norm_two : forall r, RE8 r -> ip r r = q_two.
Axiom ip_range : forall r s, RE8 r -> RE8 s -> True.

Definition AdjPlus1 (S : Vector8 -> Prop) (x y : Vector8) : Prop := True.
