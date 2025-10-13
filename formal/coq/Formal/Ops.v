From Formal Require Import Prelude Types ResGraph.

Parameter RC : ResGraph -> ResGraph.
Parameter Prod : ResGraph -> ResGraph -> ResGraph.
Parameter QuotientBy : ResGraph -> ResGraph.
Parameter FilterV : ResGraph -> ResGraph.
Parameter AugmentV : ResGraph -> ResGraph.

Axiom RC_preserves_Phi : forall A, Φ (RC A) = Φ A.
Axiom Prod_Phi_eq : forall A B, Φ (Prod A B) = Φ A.
