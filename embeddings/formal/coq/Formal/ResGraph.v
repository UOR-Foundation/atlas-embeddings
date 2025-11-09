From Formal Require Import Prelude Types.

Record ResGraph := {
  V  : Type;
  E  : V -> V -> Prop;
  λ  : V -> Vector8;
  U  : V -> Prop;
  Φ  : Phi;
  Φ_spec : forall u v, E u v <-> Φ (ip (λ u) (λ v))
}.

Record Morphism (A B : ResGraph) := {
  f : V A -> V B;
  w : Vector8 -> Vector8;
  hom : forall u v, E A u v -> E B (f u) (f v);
  label_compat : forall u, λ B (f u) = w (λ A u);
  unity : forall u, U A u -> U B (f u)
}.
