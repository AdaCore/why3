theory Why3_Number
imports
  Why3_Int
  "~~/src/HOL/Number_Theory/Primes"
begin

section {* Parity properties *}

why3_open "number/Parity.xml"

why3_vc even_def by (simp add: even_equiv_def)

why3_vc odd_def by (simp add: odd_equiv_def)

why3_vc even_or_odd by auto

why3_vc even_not_odd using assms by simp

why3_vc odd_not_even using assms by simp

why3_vc even_odd using assms by simp

why3_vc odd_even using assms by simp

why3_vc even_even using assms by simp

why3_vc odd_odd using assms by simp

why3_vc even_2k by simp

why3_vc odd_2k1 by simp

why3_end


section {* Divisibility *}

why3_open "number/Divisibility.xml"

why3_vc divides_def by (simp add: dvd_def mult.commute)

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
  by (auto simp add: emod_def split add: split_if_asm)

why3_vc divides_mod_euclidean
  using assms
  by (simp add: emod_def dvd_eq_mod_eq_0 zabs_def zmod_zminus2_eq_if)

why3_vc mod_divides_computer
  using assms
  by (auto simp add: cmod_def zabs_def sgn_0_0 zmod_zminus1_eq_if
    not_sym [OF less_imp_neq [OF pos_mod_bound]]
    split add: split_if_asm)

why3_vc divides_mod_computer
  using assms
  by (simp add: cmod_def dvd_eq_mod_eq_0 zabs_def
    zmod_zminus1_eq_if zmod_zminus2_eq_if)

why3_vc even_divides by (rule even_iff_2_dvd)

why3_vc odd_divides by (simp add: even_iff_2_dvd)

why3_end


section {* Greatest Common Divisor *}

why3_open "number/Gcd.xml"

why3_vc gcd_nonneg by simp

why3_vc gcd_def1 by simp

why3_vc gcd_def2 by simp

why3_vc gcd_def3 using assms by (rule gcd_greatest_int)

why3_vc gcd_unique using assms
  by (simp add: gcd_unique_int [symmetric])

why3_vc Comm by (rule gcd_commute_int)

why3_vc Assoc by (rule gcd_assoc_int)

why3_vc gcd_0_pos using assms by simp

why3_vc gcd_0_neg using assms by simp

why3_vc gcd_opp by simp

why3_vc gcd_euclid
  using gcd_add_mult_int [of a "- q" b]
  by (simp add: sign_simps)

why3_vc Gcd_computer_mod
  using assms gcd_add_mult_int [of b "- 1" "a mod b"]
  by (simp add: cmod_def zabs_def gcd_red_int [symmetric] sgn_if sign_simps)
    (simp add: zmod_zminus2_eq_if gcd_red_int [of a b])

why3_vc Gcd_euclidean_mod
  using assms gcd_add_mult_int [of b "- 1" "a mod b"]
  by (simp add: emod_def zabs_def gcd_red_int [symmetric] sign_simps)
    (simp add: zmod_zminus2_eq_if gcd_red_int [of a b])

why3_vc gcd_mult using assms
  by (simp add: gcd_mult_distrib_int [symmetric])

why3_end


section {* Prime numbers *}

why3_open "number/Prime.xml"

why3_vc prime_def
  unfolding prime_def
proof
  assume "1 < nat p \<and> (\<forall>m. m dvd nat p \<longrightarrow> m = 1 \<or> m = nat p)"
  then have "1 < p" and H: "\<And>m. m \<ge> 0 \<Longrightarrow> m dvd p \<Longrightarrow> m = 1 \<or> m = p"
    by (auto simp add: dvd_int_iff)
  show "2 \<le> p \<and> (\<forall>n. 1 < n \<and> n < p \<longrightarrow> \<not> n dvd p)"
  proof
    from `1 < p` show "2 \<le> p" by simp

    show "\<forall>n. 1 < n \<and> n < p \<longrightarrow> \<not> n dvd p"
    proof (intro strip)
      fix n
      assume "1 < n \<and> n < p"
      with H [of n] show "\<not> n dvd p" by auto
    qed
  qed
next
  assume "2 \<le> p \<and> (\<forall>n. 1 < n \<and> n < p \<longrightarrow> \<not> n dvd p)"
  then have "2 \<le> p" and H: "\<And>n. 1 < n \<Longrightarrow> n < nat p \<Longrightarrow> \<not> n dvd p"
    by auto
  show "1 < nat p \<and> (\<forall>m. m dvd nat p \<longrightarrow> m = 1 \<or> m = nat p)"
  proof
    from `2 \<le> p` show "1 < nat p" by simp

    show "\<forall>m. m dvd nat p \<longrightarrow> m = 1 \<or> m = nat p"
    proof (intro strip)
      fix m
      assume "m dvd nat p"
      with `2 \<le> p` have "1 \<le> m" by (cases "m = 0") auto
      show "m = 1 \<or> m = nat p"
      proof (cases "m = 1")
        case False
        show ?thesis
        proof (cases "m = nat p")
          case False
          from `2 \<le> p` `m dvd nat p` have "m \<le> nat p" by (simp add: dvd_imp_le)
          with False `m \<noteq> 1` `1 \<le> m` `m dvd nat p` H show ?thesis by (simp add: int_dvd_iff)
        qed simp
      qed simp
    qed
  qed
qed

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
      by (auto simp add: prime_nat_def)
    with `1 < n` have "k \<le> n" by (simp add: dvd_imp_le)
    with `k \<noteq> n` have "k < n" by simp
    moreover from `k dvd n` `1 < n` have "k \<noteq> 0" by (rule_tac notI) simp
    with `k \<noteq> 1` have "1 < k" by simp
    moreover from `k < n` `n < p` have "k < p" by simp
    moreover from `k dvd n` `n dvd p` have "k dvd p" by (rule dvd.order_trans)
    ultimately show ?thesis by (rule less)
  qed
qed

why3_vc small_divisors
  unfolding prime_def
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
        by (simp_all add: transfer_nat_int_relations)
      then have "\<exists>d. prime d \<and> d * d \<le> nat p \<and> d dvd (nat p)"
        by (rule small_divisors_aux)
      with `2 \<le> p` obtain d
        where d: "prime d" "d * d \<le> p" "d dvd p"
        by (auto simp add: int_dvd_iff le_nat_iff int_mult)
      from `prime d` have "2 \<le> d" by auto
      then have "2 \<le> int d" by simp
      with `2 \<le> int d` have "2 * 2 \<le> int d * int d"
        by (rule mult_mono) simp_all
      with d assms `2 \<le> d` show False by auto
    qed
  qed
qed

why3_vc even_prime
proof -
  from `prime (nat p)` have "0 \<le> p" by (simp add: prime_def)
  from `prime (nat p)` have "2 \<le> nat p" by auto
  with `prime (nat p)` `even p` `0 \<le> p` show ?thesis
    by (auto simp add: order_le_less prime_odd_nat pos_int_even_equiv_nat_even)
qed

why3_vc odd_prime
proof -
  from `prime (nat p)` have "2 \<le> nat p" by auto
  with `prime (nat p)` `3 \<le> p` show ?thesis
    by (auto simp add: order_le_less prime_odd_nat pos_int_even_equiv_nat_even)
qed

why3_end


section {* Coprime numbers *}

why3_open "number/Coprime.xml"

why3_vc coprime_def ..

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
        by (auto simp add: coprime_int)
    qed
  next
    assume H: "\<forall>n. 1 \<le> n \<and> n < p \<longrightarrow> coprime n p"
    show "\<forall>n. 1 < n \<and> n < p \<longrightarrow> \<not> n dvd p"
    proof (intro strip notI)
      fix n
      assume H': "1 < n \<and> n < p" "n dvd p"
      then have "1 \<le> n \<and> n < p" by simp
      with H have "coprime n p" by simp
      with H' show False by (simp add: coprime_int)
    qed
  qed
  then show ?thesis by (simp add: prime_def)
qed

why3_vc Gauss
proof -
  from assms
  have "coprime a b" "a dvd c * b" by (simp_all add: mult.commute)
  then show ?thesis by (rule coprime_dvd_mult_int)
qed

why3_vc Euclid
proof -
  from `p dvd a * b` have "nat \<bar>p\<bar> dvd nat \<bar>a\<bar> * nat \<bar>b\<bar>"
    by (simp add: dvd_int_iff abs_mult nat_mult_distrib)
  moreover from `prime (nat p)` have "prime (nat \<bar>p\<bar>)"
    by (simp add: prime_def)
  ultimately show ?thesis by (simp add: dvd_int_iff)
qed

why3_vc gcd_coprime
proof -
  have "gcd a (b * c) = gcd (b * c) a" by (simp add: gcd_commute_int)
  also from assms have "coprime b a" by (simp add: gcd_commute_int)
  then have "gcd (b * c) a = gcd c a" by (simp add: gcd_mult_cancel_int)
  finally show ?thesis by (simp add: gcd_commute_int)
qed

why3_end

end
