theory Why3_Real
imports Complex_Main "~~/src/HOL/Decision_Procs/Approximation" Why3_Setup
begin

section {* Real numbers and the basic unary and binary operators *}

why3_open "real/Real.xml"

why3_vc infix_lseq_def by auto

why3_vc Assoc by auto

why3_vc Unit_def_l by auto

why3_vc Unit_def_r by auto

why3_vc Inv_def_l by auto

why3_vc Inv_def_r by auto

why3_vc Comm by simp

why3_vc Assoc1 by simp

why3_vc Mul_distr_l by (simp add: Fields.linordered_field_class.sign_simps)

why3_vc Mul_distr_r by (simp add: Rings.comm_semiring_class.distrib)

why3_vc infix_mn_def by auto

why3_vc Comm1 by auto

why3_vc Unitary by auto

why3_vc NonTrivialRing by auto

why3_vc Inverse by (simp add: assms)

why3_vc add_div by (simp add: Fields.division_ring_class.add_divide_distrib)

why3_vc sub_div by (simp add: Fields.division_ring_class.diff_divide_distrib)

why3_vc neg_div by auto

why3_vc assoc_mul_div by auto

why3_vc assoc_div_mul by auto

why3_vc assoc_div_div by auto

why3_vc Refl by auto

why3_vc Trans
  using assms
  by auto

why3_vc Antisymm
  using assms
  by auto

why3_vc Total by auto

why3_vc ZeroLessOne by auto

why3_vc CompatOrderAdd
  using assms
  by auto

why3_vc CompatOrderMult
  using assms
  by (simp add: Rings.ordered_semiring_class.mult_right_mono)

why3_vc infix_sl_def by (simp add: Real.divide_real_def)

why3_end

section {* Alternative Infix Operators *}

why3_open "real/RealInfix.xml"

why3_end

section {* Absolute Value *}

why3_open "real/Abs.xml"

why3_vc Abs_le by auto

why3_vc Abs_pos by auto

why3_vc Abs_sum by auto

why3_vc abs_def by (simp add: Real.abs_real_def)

why3_vc Abs_prod by (simp add: Rings.linordered_idom_class.abs_mult)

why3_vc triangular_inequality by (simp add: Real.abs_real_def)

why3_end

section {* Minimum and Maximum *}

why3_open "real/MinMax.xml"

why3_vc Max_l
  using assms
  by auto

why3_vc Min_r
  using assms
  by auto

why3_vc max_def by auto

why3_vc min_def by auto

why3_vc Max_comm by auto

why3_vc Min_comm by auto

why3_vc Max_assoc by auto

why3_vc Min_assoc by auto

why3_end

section {* Injection of integers into reals *}

why3_open "real/FromInt.xml"
  constants
    from_int = of_int

why3_vc Add by auto

why3_vc Mul by auto

why3_vc Neg by auto

why3_vc One by auto

why3_vc Sub by auto

why3_vc Zero by auto

why3_end

section {* Various truncation functions *}

(* truncate: rounds towards zero *)

definition truncate :: "real \<Rightarrow> int" where
  "truncate x = (if x \<ge> 0 then floor x else ceiling x)"

why3_open "real/Truncate.xml"
  constants
  truncate = truncate
  floor = floor
  ceil = ceiling

subsection {* Roundings up and down *}

why3_vc Ceil_up
proof -
  show ?C1 by linarith
  show ?C2 by (simp add:ceiling_def) (linarith)
qed

why3_vc Ceil_int by auto

why3_vc Floor_int by auto

why3_vc Floor_down
proof -
  show ?C1 by linarith
  show ?C2 by linarith
qed

why3_vc Ceil_monotonic
  using assms
  by (simp add:ceiling_mono)

why3_vc Floor_monotonic
  using assms
  by (simp add:floor_mono)

subsection {* Rounding towards zero *}

why3_vc Real_of_truncate
proof -
  show ?C1
    apply (simp add:ceiling_def truncate_def)
    apply (linarith)
    done
  show ?C2
    apply (simp add:ceiling_def truncate_def)
    apply (linarith)
    done
qed

why3_vc Truncate_int by (simp add:truncate_def)

why3_vc Truncate_up_neg
proof -
  show ?C1
    apply (simp add:ceiling_def truncate_def)
    apply (linarith)
    done
  show ?C2
    using assms
    unfolding truncate_def ceiling_def
    apply (simp)
    apply (linarith)
    done
qed

why3_vc Truncate_down_pos
proof -
  show ?C1
    using assms
    apply (simp add:ceiling_def truncate_def)
    apply (linarith)
    done
  show ?C2
    apply (simp add:ceiling_def truncate_def)
    apply (linarith)
    done
qed

why3_vc Truncate_monotonic
proof -
  { fix a b
    assume "\<not> a > (0::int)" and "(0::int) \<le> b"
    from this have "a \<le> b" by arith
  } note neg_lesseq_nonneg = this
  show ?C1 using assms
  unfolding truncate_def
  apply (simp add:floor_mono ceiling_mono neg_lesseq_nonneg)
  done
qed

why3_vc Truncate_monotonic_int1
proof -
  show ?C1 using assms
  apply (simp add:truncate_def)
  apply (linarith)
  done
qed

why3_vc Truncate_monotonic_int2
proof -
  show ?C1 using assms
  apply (simp add:truncate_def)
  apply (linarith)
  done
qed

why3_end

section {* Square and Square Root *}

why3_open "real/Square.xml"
  constants
    sqrt = sqrt

why3_vc Sqrt_le
  using assms
  by auto

why3_vc Sqrt_mul by (simp add: NthRoot.real_sqrt_mult)

why3_vc Sqrt_square
  using assms
  by (simp add: sqr_def)

why3_vc Square_sqrt
  using assms
  by auto

why3_vc Sqrt_positive
  using assms
  by auto

why3_end

section {* Exponential and Logarithm *}

why3_open "real/ExpLog.xml"
  constants
    exp = exp
    log = ln

why3_vc Exp_log
  using assms
  by auto

why3_vc Exp_sum by (simp add: Transcendental.exp_add)

why3_vc Log_exp by auto

why3_vc Log_mul
  using assms
  by (simp add: Transcendental.ln_mult)

why3_vc Log_one by auto

why3_vc Exp_zero by auto

why3_end

section {* Power of a real to an integer *}

(* TODO: clones int.Exponentiation which is not yet realized *)

why3_open "real/PowerInt.xml"

why3_vc Power_0 by auto

why3_vc Power_1 by auto

why3_vc Power_s
proof -
  { have "nat (n + 1) = Suc (nat n)" using assms by auto
  } note l1 = this
  show ?C1
  apply (simp add:l1)
  done
qed

why3_vc Power_sum
proof -
  { have "nat (n + m) = nat n + nat m" using assms by auto
  } note l2 = this
  show ?C1
  apply (simp add:l2 Power.monoid_mult_class.power_add)
  done
qed

why3_vc Pow_ge_one using assms by auto

why3_vc Power_mult
proof -
  { have "nat (n * m) = nat n * nat m"
    using assms
    by (simp add:Nat_Transfer.transfer_nat_int_functions)
  } note l3 = this
  show ?C1
  apply (simp add:l3 Power.monoid_mult_class.power_mult)
  done
qed

why3_vc Power_mult2 by (simp only:Power.comm_monoid_mult_class.power_mult_distrib)

why3_vc Power_s_alt
proof -
  { have "nat n = Suc (nat (n -1))" using assms by auto
  } note l4 = this
  show ?C1
  apply (simp add:l4)
  done
qed

why3_end

section {* Power of a real to a real exponent *}

(* TODO: no power to a real exponent in Isabelle? *)

section {* Trigonometric Functions *}

why3_open "real/Trigonometry.xml"
  constants
    cos = cos
    sin = sin
    pi = pi
    atan = arctan

why3_vc Cos_0 by auto

why3_vc Sin_0 by auto

why3_vc Cos_pi by auto

why3_vc Sin_pi by auto

why3_vc Cos_neg by auto

why3_vc Cos_pi2 by auto

why3_vc Cos_sum by (simp add: Transcendental.cos_add)

why3_vc Sin_neg by auto

why3_vc Sin_pi2 by auto

why3_vc Sin_sum by (simp add: Transcendental.sin_add)

why3_vc tan_def by (simp add: Transcendental.tan_def)

why3_vc Tan_atan by (simp add: Transcendental.tan_arctan)

why3_vc Cos_le_one by auto

why3_vc Sin_le_one by auto

why3_vc Cos_plus_pi by auto

why3_vc Pi_interval
proof -
  { have "3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196 < pi
" by (approximation 670)
  } note pi_greater = this
  { have "pi < 3.14159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038197
" by (approximation 670)
  } note pi_less = this
  (* explicitly remove exponentiation from the above lemmas *)
  have a: "10 ^ 200 = (100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000::real)" by simp
  from pi_less have pi_less': "pi < 314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038197 /
         100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
     by (simp only: a)
  also from pi_greater have pi_greater': "314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196 /
    100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
    < pi" by (simp only: a)
  (* the rest is easy *)
  show ?C1 by (simp only: pi_greater')
  show ?C2 by (simp only: pi_less')
qed

why3_vc Sin_plus_pi by auto

why3_vc Cos_plus_pi2 by (simp add: Transcendental.minus_sin_cos_eq)

why3_vc Sin_plus_pi2 by (simp add: sin_add)

why3_vc Pythagorean_identity
  by (simp add: sqr_def)

why3_end

section {* Hyperbolic Functions *}

(* TODO: missing acosh *)

section {* Polar Coordinates *}

(* TODO: missing atan2 *)

end
