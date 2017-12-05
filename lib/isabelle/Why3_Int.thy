theory Why3_Int
imports Why3_Setup
begin

section {* Integers and the basic operators *}

why3_open "int/Int.xml"

why3_vc Comm by simp

why3_vc Comm1 by simp

why3_vc Assoc by simp

why3_vc Assoc1 by simp

why3_vc Unitary by simp

why3_vc Inv_def_l by simp

why3_vc Inv_def_r by simp

why3_vc Unit_def_l by simp

why3_vc Unit_def_r by simp

why3_vc Mul_distr_l by (simp add: ring_distribs)

why3_vc Mul_distr_r by (simp add: ring_distribs)

why3_vc infix_mn_def by simp

why3_vc NonTrivialRing by simp

why3_vc infix_lseq_def by auto

why3_vc Refl by simp

why3_vc Trans using assms by simp

why3_vc Total by auto

why3_vc Antisymm using assms by simp

why3_vc ZeroLessOne by simp

why3_vc CompatOrderAdd using assms by simp

why3_vc CompatOrderMult using assms by (rule mult_right_mono)

why3_end


section {* Absolute Value *}

why3_open "int/Abs.xml"

why3_vc abs_def by simp

why3_vc Abs_le by auto

why3_vc Abs_pos by simp

why3_end


section {* Minimum and Maximum *}

why3_open "int/MinMax.xml"

why3_vc Max_l using assms by simp

why3_vc Max_comm by simp

why3_vc Max_assoc by simp

why3_vc Min_r using assms by simp

why3_vc Min_comm by simp

why3_vc Min_assoc by simp

why3_vc max_def by auto

why3_vc min_def by auto

why3_end


section {* Euclidean Division *}

definition ediv :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "ediv" 70) where
  "a ediv b = sgn b * (a div \<bar>b\<bar>)"

definition emod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "emod" 70) where
  "a emod b = a mod \<bar>b\<bar>"

why3_open "int/EuclideanDivision.xml"
  constants
    div = ediv
    mod = emod

why3_vc Div_1 by (simp add: ediv_def)

why3_vc Div_1_left using assms by (simp add: ediv_def div_pos_pos_trivial)

why3_vc Div_inf using assms by (simp add: ediv_def div_pos_pos_trivial)

why3_vc Div_inf_neg
  using assms
  by (cases "x = y") (simp_all add: ediv_def
    zdiv_zminus1_eq_if div_pos_pos_trivial mod_pos_pos_trivial)

why3_vc Div_mod
  by (simp add: ediv_def emod_def mult.assoc [symmetric] abs_sgn)

why3_vc Div_mult using assms by (simp add: ediv_def add.commute)

why3_vc Div_bound
proof -
  from assms show ?C1
    by (simp add: ediv_def pos_imp_zdiv_nonneg_iff)

  show ?C2
  proof (cases "x = 0")
    case False
    show ?thesis
    proof (cases "y = 1")
      case False
      with assms `x \<noteq> 0` have "x div y < x"
        by (simp add: int_div_less_self)
      with assms show ?thesis by (simp add: ediv_def)
    qed (simp add: ediv_def)
  qed (simp add: ediv_def)
qed

why3_vc Div_minus1_left
  using assms
  by (simp only: zdiv_zminus1_eq_if ediv_def)
    (simp add: div_pos_pos_trivial mod_pos_pos_trivial)

why3_vc Mod_0 by (simp add: emod_def)

why3_vc Mod_1 by (simp add: emod_def)

why3_vc Mod_1_left using assms by (simp add: emod_def mod_pos_pos_trivial)

why3_vc Mod_minus1_left
  using assms
  by (simp only: emod_def zmod_zminus1_eq_if) (simp add: mod_pos_pos_trivial)

why3_vc Mod_mult using assms by (simp add: emod_def add.commute)

why3_vc Mod_bound using assms by (simp_all add: emod_def)

why3_vc Div_unique using assms
 proof -
  have h0: "y \<noteq> 0" using assms by auto
  have h1: "x = y * (x ediv y) + (x emod y)" using h0 Div_mod by blast
  have h2: "0 \<le> x emod y \<and> x emod y < y" using assms H1 h0 Mod_bound zabs_def
    by (metis abs_sgn monoid_mult_class.mult.right_neutral sgn_pos)
  have h3: "x - y < y * (x ediv y)" using h1 h2 by linarith
  have h4: "y * (x ediv y) \<le> x" using h1 h2 by linarith
  show ?thesis
  proof (cases "x ediv y > q")
   assume a:"q < x ediv y"
   have h5: "x ediv y \<ge> q + 1" using a by linarith
   have h6: "y * (x ediv y) >= y * (q + 1)" by (metis H1 h5 le_less mult_left_mono)
   have h7: "y * (x ediv y) >= q * y + y" by (metis Comm1 Mul_distr_l h6 monoid_mult_class.mult.right_neutral)
   thus "x ediv y = q" using H3 h1 h2 h7 by linarith
   next
   assume a:"\<not> q < x ediv y"
   show "x ediv y = q"
   proof (cases "x ediv y < q")
    assume b:"x ediv y < q"
    have h5: "x ediv y \<le> q - 1" using b by linarith
    have h6: "y * (x ediv y) <= y * (q - 1)" by (metis H1 h5 le_less mult_left_mono)
    have h7: "y * (x ediv y) <= q * y - y" by (metis Comm1 h6 int_distrib(4) monoid_mult_class.mult.right_neutral)
    thus "x ediv y = q" using H2 h3 h7 by linarith
    next
    assume b:"\<not> x ediv y < q"
    show ?thesis using a b by linarith
   qed
  qed
qed

why3_end

section {* Computer Division *}

definition cdiv :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "cdiv" 70) where
  "a cdiv b = sgn a * sgn b * (\<bar>a\<bar> div \<bar>b\<bar>)"

definition cmod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "cmod" 70) where
  "a cmod b = sgn a * (\<bar>a\<bar> mod \<bar>b\<bar>)"

why3_open "int/ComputerDivision.xml"
  constants
    div = cdiv
    mod = cmod

why3_vc Div_1 by (simp add: cdiv_def mult_sgn_abs)

why3_vc Div_inf using assms by (simp add: cdiv_def div_pos_pos_trivial)

why3_vc Div_sign_neg
  using assms
  by (cases "x = 0") (simp_all add: cdiv_def
    zdiv_zminus1_eq_if div_nonpos_pos_le0 pos_imp_zdiv_neg_iff)

why3_vc Div_sign_pos
  using assms
  by (cases "x = 0")
    (simp_all add: cdiv_def pos_imp_zdiv_nonneg_iff)

why3_vc Div_mod
proof -
  have "y * (sgn x * sgn y * (\<bar>x\<bar> div \<bar>y\<bar>)) + sgn x * (\<bar>x\<bar> mod \<bar>y\<bar>) =
    sgn x * (y * sgn y * (\<bar>x\<bar> div \<bar>y\<bar>) + \<bar>x\<bar> mod \<bar>y\<bar>)"
    by (simp add: ring_distribs)
  then show ?thesis
    by (cases "x = 0") (simp_all add: cdiv_def cmod_def abs_sgn
      sgn_mult [symmetric] order.strict_iff_order)
qed

why3_vc Div_mult
proof (cases "y = 0")
  case False
  with assms show ?thesis
    by (cases "z = 0")
      (simp_all add: cdiv_def add.commute add_pos_pos)
qed simp

why3_vc Div_bound
proof -
  from assms show ?C1
    by (simp add: cdiv_def pos_imp_zdiv_nonneg_iff sgn_if)

  show ?C2
  proof (cases "x = 0")
    case False
    show ?thesis
    proof (cases "y = 1")
      case False
      with assms `x \<noteq> 0` have "x div y < x"
        by (simp add: int_div_less_self)
      with assms show ?thesis by (simp add: cdiv_def sgn_if)
    qed (simp add: cdiv_def sgn_if)
  qed (simp add: cdiv_def)
qed

why3_vc Mod_1 by (simp add: cmod_def)

why3_vc Mod_inf using assms by (simp add: cmod_def mod_pos_pos_trivial sgn_if)

why3_vc Mod_mult
proof (cases "y = 0")
  case False
  with assms show ?thesis
    by (cases "z = 0") (simp_all add: cmod_def add.commute add_pos_pos)
qed simp

why3_vc Mod_bound
proof -
  from assms show ?C1
    by (auto simp add: cmod_def sgn_if intro: less_le_trans [of _ 0])

  from assms show ?C2
    by (auto simp add: cmod_def sgn_if intro: le_less_trans [of _ 0])
qed

why3_vc Mod_sign_neg using assms by (simp add: cmod_def sgn_if)

why3_vc Mod_sign_pos using assms by (simp add: cmod_def sgn_if)

why3_vc Rounds_toward_zero
proof (cases "x = 0")
  case False
  then have "\<bar>sgn x\<bar> = 1" by (simp add: sgn_if)
  have "sgn x * sgn y * (\<bar>x\<bar> div \<bar>y\<bar>) * y =
    sgn x * (y * sgn y * (\<bar>x\<bar> div \<bar>y\<bar>))" (is "?l = ?r")
    by simp
  then have "\<bar>?l\<bar> = \<bar>?r\<bar>" by (simp (no_asm_simp))
  also note abs_sgn [symmetric]
  also note abs_mult
  also have "\<bar>y\<bar> * (\<bar>x\<bar> div \<bar>y\<bar>) \<le> \<bar>y\<bar> * (\<bar>x\<bar> div \<bar>y\<bar>) + \<bar>x\<bar> mod \<bar>y\<bar>"
    by (rule add_increasing2) (simp_all add: assms)
  with assms have "\<bar>\<bar>y\<bar> * (\<bar>x\<bar> div \<bar>y\<bar>)\<bar> \<le> \<bar>\<bar>y\<bar> * (\<bar>x\<bar> div \<bar>y\<bar>) + \<bar>x\<bar> mod \<bar>y\<bar>\<bar>"
    by (simp add: pos_imp_zdiv_nonneg_iff)
  finally show ?thesis using `\<bar>sgn x\<bar> = 1`
    by (simp add: cdiv_def)
qed (simp add: cdiv_def)

why3_end


section {* Division by 2 *}

why3_open "int/Div2.xml"

why3_vc div2
  by (rule exI [of _ "x div 2"]) auto

why3_end


section {* Power of an integer to an integer *}

why3_open "int/Power.xml"

why3_vc Power_0 by simp

why3_vc Power_1 by simp

why3_vc Power_s using assms by (simp add: nat_add_distrib)

why3_vc Power_s_alt using assms by (simp add: nat_diff_distrib power_Suc [symmetric])

why3_vc Power_sum using assms by (simp add: nat_add_distrib power_add)

why3_vc Power_mult using assms by (simp add: nat_mult_distrib power_mult)

why3_vc Power_comm1 by (simp add: power_mult_distrib)

why3_vc Power_comm2 by (simp add: power_mult_distrib)

why3_vc Power_non_neg using assms by simp

why3_vc Power_monotonic using assms by (simp add: power_increasing)

why3_end

end
