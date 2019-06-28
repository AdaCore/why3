theory ieee_float_Literals_ok_1
imports Why3.Why3
begin

why3_open "ieee_float_Literals_ok_1.xml"

why3_vc ok
(*proof -
  have "(round RNE ((tqtreal x) * (tqtreal fliteral))) = (tqtreal fliteral)"
    using Round_to_real fliteral_axiom_1 fliteral_axiom_2 by fastforce
  thus "eq (mul RNE x fliteral) fliteral"
*)
proof -
  have "in_range 0"
using fliteral_axiom_1 fliteral_axiom_2 is_finite by fastforce
  then show ?thesis
using Bounded_real_no_overflow \<open>ok.round RNE (tqtreal x * tqtreal fliteral) = tqtreal fliteral\<close> assms eq_to_real_finite fliteral_axiom_1 fliteral_axiom_2 mul_finite_1 mul_finite_rev_n_2 to_nearest_def by force
qed

why3_end

end
