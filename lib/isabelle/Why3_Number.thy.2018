theory Why3_Number
imports
  Why3_Int
  "HOL-Computational_Algebra.Primes"
begin

section {* Parity properties *}

why3_open "number/Parity.xml"

why3_vc evenqtdef by arith

why3_vc oddqtdef by arith

why3_vc even_or_odd by auto

why3_vc even_not_odd using assms by simp

why3_vc odd_not_even using assms by simp

why3_vc even_odd using assms by simp

why3_vc odd_even using assms by simp

why3_vc even_even using assms by simp

why3_vc odd_odd using assms by simp

why3_vc even_2k by simp

why3_vc odd_2k1 by simp

why3_vc even_mod2
  by (auto simp add: evenqtdef cmod_def sgn_if minus_equation_iff [of n])

why3_end


section {* Divisibility *}

why3_open "number/Divisibility.xml"

why3_vc dividesqtdef
  by (auto simp add: cmod_def sgn_if minus_equation_iff [of n])

why3_vc divides_refl by simp

why3_vc divides_1_n by simp

why3_vc divides_0 by simp

why3_vc divides_left using assms by simp

why3_vc divides_right using assms by simp

why3_vc divides_oppr using assms by simp

why3_vc divides_oppl using assms by simp

why3_vc divides_oppr_rev using assms by simp

why3_vc divides_oppl_rev using assms by simp

why3_vc divides_plusr using assms by simp

why3_vc divides_minusr using assms by simp

why3_vc divides_multl using assms by simp

why3_vc divides_multr using assms by simp

why3_vc divides_factorl by simp

why3_vc divides_factorr by simp

why3_vc divides_n_1 using assms by auto

why3_vc divides_antisym
  using assms
  by (auto dest: zdvd_antisym_abs)

why3_vc divides_trans using assms by (rule dvd_trans)

why3_vc divides_bounds using assms by (simp add: dvd_imp_le_int)

why3_vc mod_divides_euclidean
  using assms
  by (auto simp add: emod_def split: if_split_asm)

why3_vc divides_mod_euclidean
  using assms
  by (simp add: emod_def dvd_eq_mod_eq_0 zabs_def zmod_zminus2_eq_if)

why3_vc mod_divides_computer
  using assms
  by (auto simp add: cmod_def zabs_def sgn_0_0 zmod_zminus1_eq_if
    not_sym [OF less_imp_neq [OF pos_mod_bound]]
    split: if_split_asm)

why3_vc divides_mod_computer
  using assms
  by (simp add: cmod_def dvd_eq_mod_eq_0 zabs_def
    zmod_zminus1_eq_if zmod_zminus2_eq_if)

why3_vc even_divides ..

why3_vc odd_divides ..

why3_vc dividesqtspec
  by (simp add: dvd_def mult.commute)

why3_end


section {* Greatest Common Divisor *}

why3_open "number/Gcd.xml"

why3_vc gcd_nonneg by simp

why3_vc gcd_def1 by simp

why3_vc gcd_def2 by simp

why3_vc gcd_def3 using assms by (rule gcd_greatest)

why3_vc gcd_unique using assms
  by (simp add: gcd_unique_int [symmetric])

why3_vc Comm by (rule gcd.commute)

why3_vc Assoc by (rule gcd.assoc)

why3_vc gcd_0_pos using assms by simp

why3_vc gcd_0_neg using assms by simp

why3_vc gcd_opp by simp

why3_vc gcd_euclid
  using gcd_add_mult [of a "- q" b]
  by (simp add: algebra_simps)

why3_vc Gcd_computer_mod
  using assms gcd_add_mult [of b "- 1" "a mod b"]
  by (simp add: cmod_def zabs_def gcd_red_int [symmetric] sgn_if algebra_simps del: gcd_mod_right)
    (simp add: zmod_zminus2_eq_if gcd_red_int [of a b] del: gcd_mod_right)

why3_vc Gcd_euclidean_mod
  using assms gcd_add_mult [of b "- 1" "a mod b"]
  by (simp add: emod_def zabs_def gcd_red_int [symmetric] algebra_simps del: gcd_mod_right)
    (simp add: zmod_zminus2_eq_if gcd_red_int [of a b] del: gcd_mod_right)

why3_vc gcd_mult using assms
  by (simp add: gcd_mult_distrib_int [symmetric])

why3_end


section {* Prime numbers *}

why3_open "number/Prime.xml"

why3_vc primeqtdef
  by (auto simp add: prime_int_iff')

why3_vc not_prime_1 by simp

why3_vc prime_2 by simp

why3_vc prime_3 by simp

why3_vc prime_divisors
  using assms
  by (auto simp add: prime_int_altdef dest: spec [of _ "\<bar>d\<bar>"])

lemma small_divisors_aux:
  "1 < (n::nat) \<Longrightarrow> n < p \<Longrightarrow> n dvd p \<Longrightarrow> \<exists>d. prime d \<and> d * d \<le> p \<and> d dvd p"
proof (induct n rule: less_induct)
  case (less n)
  then obtain m where "p = n * m" by (auto simp add: dvd_def)
  show ?case
  proof (cases "prime n")
    case True
    show ?thesis
    proof (cases "n \<le> m")
      case True
      with `p = n * m` `prime n`
      show ?thesis by auto
    next
      case False
      then have "m < n" by simp
      moreover from `n < p` `p = n * m` have "1 < m" by simp
      moreover from `1 < n` `n < p` `p = n * m` have "m < p" by simp
      moreover from `p = n * m` have "m dvd p" by simp
      ultimately show ?thesis by (rule less)
    qed
  next
    case False
    with `1 < n` obtain k where "k dvd n" "k \<noteq> 1" "k \<noteq> n"
      by (auto simp add: prime_nat_iff)
    with `1 < n` have "k \<le> n" by (simp add: dvd_imp_le)
    with `k \<noteq> n` have "k < n" by simp
    moreover from `k dvd n` `1 < n` have "k \<noteq> 0" by (rule_tac notI) simp
    with `k \<noteq> 1` have "1 < k" by simp
    moreover from `k < n` `n < p` have "k < p" by simp
    moreover from `k dvd n` `n dvd p` have "k dvd p" by (rule dvd_trans)
    ultimately show ?thesis by (rule less)
  qed
qed

why3_vc small_divisors
  unfolding primeqtdef
proof
  show "2 \<le> p" by fact

  show "\<forall>n. 1 < n \<and> n < p \<longrightarrow> \<not> n dvd p"
  proof (intro strip)
    fix n
    assume "1 < n \<and> n < p"
    show "\<not> n dvd p"
    proof
      assume "n dvd p"
      with `1 < n \<and> n < p`
      have "1 < nat n" "nat n < nat p" "nat n dvd nat p"
        by (simp_all add: nat_dvd_iff)
      then have "\<exists>d. prime d \<and> d * d \<le> nat p \<and> d dvd (nat p)"
        by (rule small_divisors_aux)
      with `2 \<le> p` obtain d
        where d: "prime (int d)" "int d * int d \<le> p" "int d dvd p"
        by (auto simp add: int_dvd_int_iff [symmetric] le_nat_iff)
      from `prime (int d)` have "2 \<le> int d" by (simp add: prime_ge_2_int)
      then have "2 \<le> int d" by simp
      with `2 \<le> int d` have "2 * 2 \<le> int d * int d"
        by (rule mult_mono) simp_all
      with d assms `2 \<le> int d` show False by auto
    qed
  qed
qed

why3_vc even_prime
proof -
  from `prime p` have "0 \<le> p" by (simp add: primeqtdef)
  from `prime p` have "2 \<le> p" by (simp add: prime_ge_2_int)
  with `prime p` `even p` `0 \<le> p` show ?thesis
    by (auto simp add: order_le_less prime_odd_int)
qed

why3_vc odd_prime
proof -
  from `prime p` have "2 \<le> p" by (simp add: prime_ge_2_int)
  with `prime p` `3 \<le> p` show ?thesis
    by (auto simp add: order_le_less prime_odd_int)
qed

why3_end


section {* Coprime numbers *}

why3_open "number/Coprime.xml"

why3_vc coprimeqtdef by (rule coprime_iff_gcd_eq_1)

why3_vc prime_coprime
proof -
  have "(\<forall>n. 1 < n \<and> n < p \<longrightarrow> \<not> n dvd p) =
    (\<forall>n. 1 \<le> n \<and> n < p \<longrightarrow> coprime n p)"
  proof
    assume H: "\<forall>n. 1 < n \<and> n < p \<longrightarrow> \<not> n dvd p"
    show "\<forall>n. 1 \<le> n \<and> n < p \<longrightarrow> coprime n p"
    proof (intro strip)
      fix n
      assume H': "1 \<le> n \<and> n < p"
      {
        fix d
        assume "0 \<le> d" "d dvd n" "d dvd p"
        with H' have "d \<noteq> 0" by auto
        have "d = 1"
        proof (rule ccontr)
          assume "d \<noteq> 1"
          with `0 \<le> d` `d \<noteq> 0` have "1 < d" by simp
          moreover from `d dvd p` H' have "d \<le> p" by (auto dest: zdvd_imp_le)
          moreover from `d dvd n` H' have "d \<noteq> p" by (auto dest: zdvd_imp_le)
          ultimately show False using `d dvd p` H by auto
        qed
      }
      then show "coprime n p"
        by (auto simp add: coprime_iff_gcd_eq_1)
    qed
  next
    assume H: "\<forall>n. 1 \<le> n \<and> n < p \<longrightarrow> coprime n p"
    show "\<forall>n. 1 < n \<and> n < p \<longrightarrow> \<not> n dvd p"
    proof (intro strip notI)
      fix n
      assume H': "1 < n \<and> n < p" "n dvd p"
      then have "1 \<le> n \<and> n < p" by simp
      with H have "coprime n p" by simp
      with H' show False by (simp add: coprime_iff_gcd_eq_1)
    qed
  qed
  then show ?thesis by (simp add: primeqtdef)
qed

why3_vc Gauss
proof -
  from assms
  have "coprime a b" "a dvd c * b" by (simp_all add: mult.commute)
  then show ?thesis by (simp add: coprime_dvd_mult_left_iff)
qed

why3_vc Euclid
  using assms
  by (simp add: prime_dvd_multD)

why3_vc gcd_coprime
proof -
  have "gcd a (b * c) = gcd (b * c) a" by (simp add: gcd.commute)
  also from assms have "coprime a b" by (simp add: gcd.commute coprime_iff_gcd_eq_1)
  then have "gcd (b * c) a = gcd c a" by (simp add: gcd_mult_left_left_cancel)
  finally show ?thesis by (simp add: gcd.commute)
qed

why3_end

end
