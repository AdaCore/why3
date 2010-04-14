Declare ML Module "whytac".
Require Export ZArith.
Open Scope Z_scope.

Parameter foo : Set -> Set.
Definition t : Set := foo Z.
Definition u : Set := foo t.

Goal  forall x:u, x=x.
why.
