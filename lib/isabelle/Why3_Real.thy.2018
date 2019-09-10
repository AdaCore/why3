theory Why3_Real
imports
  Why3_Setup
  Complex_Main
  "HOL-Decision_Procs.Approximation"
begin

section {* Real numbers and the basic unary and binary operators *}

why3_open "real/Real.xml"

why3_vc infix_lseqqtdef by auto

why3_vc Assoc by auto

why3_vc Unit_def_l by auto

why3_vc Unit_def_r by auto

why3_vc Inv_def_l by auto

why3_vc Inv_def_r by auto

why3_vc Comm by simp

why3_vc Assoc1 by simp

why3_vc Mul_distr_l by (simp add: algebra_simps)

why3_vc Mul_distr_r by (simp add: Rings.comm_semiring_class.distrib)

why3_vc infix_mnqtdef by auto

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

why3_vc infix_slqtdef by (simp add: Real.divide_real_def)

why3_end

section {* Alternative Infix Operators *}

why3_open "real/RealInfix.xml"

why3_end

section {* Absolute Value *}

why3_open "real/Abs.xml"

why3_vc Abs_le by auto

why3_vc Abs_pos by auto

why3_vc Abs_sum by auto

why3_vc absqtdef by (simp add: Real.abs_real_def)

why3_vc Abs_prod by (simp add: abs_mult)

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

why3_vc maxqtdef by auto

why3_vc minqtdef by auto

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

why3_vc Monotonic using assms by auto

why3_vc Injective using assms by auto

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
  by (simp_all add: ceiling_correct)

why3_vc Ceil_int by auto

why3_vc Floor_int by auto

why3_vc Floor_down
  by (simp_all add: floor_correct [simplified])

why3_vc Ceil_monotonic
  using assms
  by (simp add:ceiling_mono)

why3_vc Floor_monotonic
  using assms
  by (simp add:floor_mono)

subsection {* Rounding towards zero *}

why3_vc Real_of_truncate
  using floor_correct [of x] ceiling_correct [of x]
  by (simp_all add: truncate_def del: of_int_floor_le le_of_int_ceiling)

why3_vc Truncate_int by (simp add: truncate_def)

why3_vc Truncate_up_neg
  using assms ceiling_correct [of x]
  by (simp_all add: truncate_def)

why3_vc Truncate_down_pos
  using assms floor_correct [of x]
  by (simp_all add: truncate_def)

why3_vc Truncate_monotonic
  using assms
  unfolding truncate_def
  by (simp add: floor_mono ceiling_mono order_trans [of "\<lceil>x\<rceil>" 0 "\<lfloor>y\<rfloor>"])

why3_vc Truncate_monotonic_int1
  using assms
  by (simp add: truncate_def floor_le_iff ceiling_le_iff)

why3_vc Truncate_monotonic_int2
  using assms
  by (simp add: truncate_def le_floor_iff le_ceiling_iff)

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
  using assms
  by (simp add: nat_add_distrib)

why3_vc Power_sum
  using assms
  by (simp add: nat_add_distrib power_add)

why3_vc Pow_ge_one using assms by auto

why3_vc Power_mult
  using assms
  by (simp add: nat_mult_distrib power_mult)

why3_vc Power_comm1 by simp

why3_vc Power_comm2 by (simp add: semiring_normalization_rules(30))

why3_vc Power_s_alt
proof -
  have "nat n = Suc (nat (n - 1))" using assms by auto
  then show ?thesis by simp
qed

why3_end

section {* Power of a real to a real exponent *}

(* TODO: no power to a real exponent in Isabelle? *)

section {* Trigonometric Functions *}

abbreviation (input)
  "why3_divide \<equiv> divide"

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

why3_vc tanqtdef by (simp add: Transcendental.tan_def)

why3_vc Tan_atan by (simp add: Transcendental.tan_arctan)

why3_vc Cos_le_one by auto

why3_vc Sin_le_one by auto

why3_vc Cos_plus_pi by auto

why3_vc Pi_double_precision_bounds
proof -
  have "7074237752028440 / 2251799813685248 < pi"
    by (approximation 57)
  then show ?C1 by simp
  have "pi < 7074237752028441 / 2251799813685248"
    by (approximation 55)
  then show ?C2 by simp
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
