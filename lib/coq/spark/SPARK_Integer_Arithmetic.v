Require Import BuiltIn.
Require int.Int.
Require int.Abs.
Open Scope Z_scope.

Lemma div_mul_le : forall x y, 0 <= x -> 0 < y -> (x / y) * y <= x.
  intros.
  replace (x / y * y) with (y * (x / y)) by auto with zarith.
  apply (Z.mul_div_le _ _ H0).
Qed.

Lemma div_then_mult : forall x y z, 0 < y -> 0 <= z -> x <= z / y -> x * y <= z.
  intros.
  assert (0 <= y) as y_nat by auto with zarith.
  pose (Int.CompatOrderMult x (z / y) y H1 y_nat) as base_ineq.
  apply Int.Trans with (y := z / y * y).
  exact base_ineq.
  replace (z / y * y) with (y * (z / y)) by auto with zarith.
  apply (Z.mul_div_le _ _ H).
Qed.

Lemma mul_ratio : forall x y z, 0 <= x -> 0 <= y -> 0 < z -> y <= z -> x * y / z <= x.
  intros.
  destruct (Z.eq_dec y 0) as [y_zero|y_not_zero].
  * rewrite y_zero, Z.mul_0_r, Z.div_0_l by auto with zarith.
    exact H.
  * apply Int.Trans with (y := x * y / y).
    apply Z.div_le_compat_l; auto with zarith.
    rewrite Z.div_mul by auto.
    auto with zarith.
Qed.
