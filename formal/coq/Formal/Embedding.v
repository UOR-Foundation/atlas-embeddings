From Coq Require Import Logic.FunctionalExtensionality.
From Formal Require Import Prelude Types ResGraph Adjacency E8.

Axiom Atlas_to_E8_embedding :
  forall (A : ResGraph),
    Φ A = PhiAtlas ->
    (exists f : V A -> Vector8,
      (forall u v, f u = f v -> u = v) /\
      (forall u, RE8 (f u)) /\
      (forall u v, E A u v <-> ip (f u) (f v) = q_neg_one)).
