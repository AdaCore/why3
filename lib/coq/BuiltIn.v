Require Export ZArith.
Require Export Rbase.

Class WhyType T := why_inhabitant : T.

Notation int := Z.

Global Instance int_WhyType : WhyType int.
exact Z0.
Qed.

Notation real := R.

Global Instance real_WhyType : WhyType real.
exact R0.
Qed.

Global Instance tuple_WhyType : forall T {T' : WhyType T} U {U' : WhyType U}, WhyType (T * U).
now split.
Qed.

Global Instance unit_WhyType : WhyType unit.
exact tt.
Qed.

Global Instance bool_WhyType : WhyType bool.
exact false.
Qed.
