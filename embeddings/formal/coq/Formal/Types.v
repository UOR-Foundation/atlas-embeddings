From Formal Require Import Prelude.

Definition Qformal := Q.
Notation Q := Qformal.
Definition Vector8 := list Q.  (* length 8 invariant left as a stub *)

Parameter q_neg_one : Q.
Parameter q_two : Q.
Parameter ip : Vector8 -> Vector8 -> Q.
Definition Phi := Q -> Prop.
