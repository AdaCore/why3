theory Why3_BV
imports
  Why3_Int
  "HOL-Word.Word"
  "HOL-Word.Bit_Comparison"
begin

abbreviation (input) pow2 :: "int \<Rightarrow> int"
where "pow2 i \<equiv> 2 ^ nat i"

why3_open "bv/Pow2int.xml"
  constants
    pow2=pow2

why3_vc Power_0 by simp

why3_vc Power_s using assms by (simp add: Power_s)

why3_vc Power_1 by simp

why3_vc Power_sum using assms by (simp add: Power_sum)

why3_vc pow2pos using assms by simp

why3_vc pow2_0 by simp
why3_vc pow2_1 by simp
why3_vc pow2_2 by simp
why3_vc pow2_3 by simp
why3_vc pow2_4 by simp
why3_vc pow2_5 by simp
why3_vc pow2_6 by simp
why3_vc pow2_7 by simp
why3_vc pow2_8 by simp
why3_vc pow2_9 by simp
why3_vc pow2_10 by simp
why3_vc pow2_11 by simp
why3_vc pow2_12 by simp
why3_vc pow2_13 by simp
why3_vc pow2_14 by simp
why3_vc pow2_15 by simp
why3_vc pow2_16 by simp
why3_vc pow2_17 by simp
why3_vc pow2_18 by simp
why3_vc pow2_19 by simp
why3_vc pow2_20 by simp
why3_vc pow2_21 by simp
why3_vc pow2_22 by simp
why3_vc pow2_23 by simp
why3_vc pow2_24 by simp
why3_vc pow2_25 by simp
why3_vc pow2_26 by simp
why3_vc pow2_27 by simp
why3_vc pow2_28 by simp
why3_vc pow2_29 by simp
why3_vc pow2_30 by simp
why3_vc pow2_31 by simp
why3_vc pow2_32 by simp
why3_vc pow2_33 by simp
why3_vc pow2_34 by simp
why3_vc pow2_35 by simp
why3_vc pow2_36 by simp
why3_vc pow2_37 by simp
why3_vc pow2_38 by simp
why3_vc pow2_39 by simp
why3_vc pow2_40 by simp
why3_vc pow2_41 by simp
why3_vc pow2_42 by simp
why3_vc pow2_43 by simp
why3_vc pow2_44 by simp
why3_vc pow2_45 by simp
why3_vc pow2_46 by simp
why3_vc pow2_47 by simp
why3_vc pow2_48 by simp
why3_vc pow2_49 by simp
why3_vc pow2_50 by simp
why3_vc pow2_51 by simp
why3_vc pow2_52 by simp
why3_vc pow2_53 by simp
why3_vc pow2_54 by simp
why3_vc pow2_55 by simp
why3_vc pow2_56 by simp
why3_vc pow2_57 by simp
why3_vc pow2_58 by simp
why3_vc pow2_59 by simp
why3_vc pow2_60 by simp
why3_vc pow2_61 by simp
why3_vc pow2_62 by simp
why3_vc pow2_63 by simp
why3_vc pow2_64 by simp

why3_end


lemma rotate1_nth:
  assumes "0 < length xs"
  shows "rotate1 xs ! (i mod length xs) = xs ! (Suc i mod length xs)"
proof (cases xs)
  case Nil
  with `0 < length xs` show ?thesis by simp
next
  case (Cons y ys)
  with mod_less_divisor [of "Suc (length ys)" i]
  show ?thesis
    by (auto simp add: nth_append mod_Suc simp del: mod_less_divisor)
qed

lemma rotl_nth:
  "word_rotl j w !! ((i + j) mod len_of TYPE('a)) = (w::'a::len word) !! (i mod len_of TYPE('a))"
proof (induct j arbitrary: w i)
  case 0
  show ?case by simp
next
  case (Suc n)
  from Suc [of "of_bl (rotate1 (to_bl w))" "Suc i"]
    rotate1_nth [of "to_bl w" "len_of TYPE('a) - Suc (Suc i mod len_of TYPE('a))"]
  show ?case
    by (simp add: word_rotl_def rotate1_rotate_swap word_bl.Abs_inverse
      rev_nth test_bit_bl word_size Suc_diff_Suc)
      (simp add: mod_Suc)
qed

lemma rotater1_rotater_swap: "rotater1 (rotater n xs) = rotater n (rotater1 xs)"
  by (simp add: rotater_def funpow_swap1)

lemma length_rotater1 [simp]: "length (rotater1 xs) = length xs"
  by (simp add: rotater1_def split: list.split)

lemma rotater1_nth:
  assumes "0 < length xs"
  shows "rotater1 xs ! (Suc i mod length xs) = xs ! (i mod length xs)"
proof (cases xs rule: rev_cases)
  case Nil
  with `0 < length xs` show ?thesis by simp
next
  case (snoc ys y)
  with mod_less_divisor [of "Suc (length ys)" i]
  show ?thesis
    by (auto simp add: rotate1_rl' nth_append mod_Suc simp del: mod_less_divisor)
qed

lemma rotr_nth:
  "word_rotr j w !! (i mod len_of TYPE('a)) = (w::'a::len word) !! ((i + j) mod len_of TYPE('a))"
proof (induct j arbitrary: w)
  case 0
  show ?case by simp
next
  case (Suc n)
  from Suc [of "of_bl (rotater1 (to_bl w))"]
    rotater1_nth [of "to_bl w" "len_of TYPE('a) - Suc (Suc (i + n) mod len_of TYPE('a))", symmetric]
  show ?case
    by (simp add: word_rotr_def rotater1_rotater_swap word_bl.Abs_inverse
      rev_nth test_bit_bl word_size Suc_diff_Suc)
      (simp add: mod_Suc)
qed

lemma uint_pow: "uint ((b::'a::len word) ^ n) = uint b ^ n mod 2 ^ len_of TYPE('a)"
  by (induct n) (simp_all add: mod_pos_pos_trivial uint_word_ariths mod_mult_right_eq)


lemma eq_sub_equiv_aux:
  "(\<forall>j. uint i \<le> j \<and> j < uint i + uint n \<longrightarrow>
      (0 \<le> j \<and> a !! nat j) = (0 \<le> j \<and> b !! nat j)) =
   (b AND (mask (unat n) << unat i) = a AND (mask (unat n) << unat i))"
  apply (simp add: word_eq_iff word_ops_nth_size word_size nth_shiftl)
  apply (rule iffI)
  apply (rule allI)
  apply (drule_tac x="int na" in spec)
  apply (auto simp add: uint_nat)[1]
  apply (rule allI)
  apply (drule_tac x="nat j" in spec)
  apply (auto simp add: uint_nat test_bit_bin)
  done


lemma int_minus_mod: "((i::int) - j) mod n = (i + (n - j mod n)) mod n"
proof -
  have "(i + (n - j mod n)) mod n = (i mod n + (n - j mod n) mod n) mod n"
    by (simp only: mod_add_eq)
  also have "(n - j mod n) mod n = (n mod n - j mod n) mod n"
    by simp
  finally show ?thesis by (simp add: pull_mods [symmetric])
qed

lemma nat_minus_mod:
  assumes "0 < (n::nat)"
  shows "((n - i mod n) + i) mod n = 0"
proof -
  have "((n - i mod n) + i) mod n = (i + (n - i mod n)) mod n"
    by (simp add: add_ac)
  also have "\<dots> = (i mod n + (n - i mod n)) mod n"
    by (simp add: pull_mods [symmetric])
  also from assms have "\<dots> = (n mod n + (i mod n - i mod n)) mod n"
    by (simp add: add_ac)
  finally show ?thesis by simp
qed

lemma nat_minus_mod':
  assumes "0 < (n::nat)"
  shows "(i + (n - j mod n) + j) mod n = i mod n"
proof -
  have "(i + (n - j mod n) + j) mod n = (i + ((n - j mod n) + j)) mod n"
    by (simp add: add_ac)
  also have "\<dots> = (i mod n + ((n - j mod n) + j) mod n) mod n"
    by (simp add: pull_mods [symmetric])
  also note nat_minus_mod [OF assms]
  finally show ?thesis by simp
qed


definition bv_nth :: "'a::len0 word \<Rightarrow> int \<Rightarrow> bool"
where "bv_nth bv i \<equiv> 0 \<le> i \<and> bv !! nat i"

abbreviation (input) nth_bv :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> bool"
where "nth_bv bv bv' \<equiv> bv !! unat bv'"

abbreviation (input) lsr :: "'a::len0 word \<Rightarrow> int \<Rightarrow> 'a word"
where "lsr v i \<equiv> v >> nat i"

abbreviation (input) lsr_bv :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "lsr_bv v n \<equiv> v >> unat n"

abbreviation (input) asr :: "'a::len word \<Rightarrow> int \<Rightarrow> 'a word"
where "asr v i \<equiv> v >>> nat i"

abbreviation (input) asr_bv :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "asr_bv v n \<equiv> v >>> unat n"

abbreviation (input) lsl :: "'a::len0 word \<Rightarrow> int \<Rightarrow> 'a word"
where "lsl v i \<equiv> v << nat i"

abbreviation (input) lsl_bv :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "lsl_bv v n \<equiv> v << unat n"

abbreviation (input) rotate_left :: "'a::len0 word \<Rightarrow> int \<Rightarrow> 'a word"
where "rotate_left v n \<equiv> word_rotl (nat n) v"

abbreviation (input) rotate_right :: "'a::len0 word \<Rightarrow> int \<Rightarrow> 'a word"
where "rotate_right v n \<equiv> word_rotr (nat n) v"

abbreviation (input) rotate_left_bv :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "rotate_left_bv v n \<equiv> word_rotl (unat n) v"

abbreviation (input) rotate_right_bv :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "rotate_right_bv v n \<equiv> word_rotr (unat n) v"

definition eq_sub_bv :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
  eq_sub_bv_defn: "eq_sub_bv a b i n =
    (b AND (mask (unat n) << unat i) = a AND (mask (unat n) << unat i))"

definition size_bv :: "'a::len word" where
  "size_bv = of_nat LENGTH('a)"

definition is_signed_positive :: "'a::len word \<Rightarrow> bool" where
  "is_signed_positive w = (0 \<le> sint w)"

lemma to_int_eq:
  "sint (x::'a::len word) =
   (if is_signed_positive x then uint x else - (2 ^ LENGTH('a) - uint x))"
proof (cases "0 \<le> sint x")
  case True
  note sint_lt [of x]
  also have "(2::int) ^ (LENGTH('a) - 1) < 2 ^ LENGTH('a)"
    by (rule power_strict_increasing) simp_all
  finally have "sint x < 2 ^ LENGTH('a)" .
  with True show ?thesis
    by (simp add: is_signed_positive_def uint_sint bintrunc_mod2p mod_pos_pos_trivial)
next
  case False
  from sint_ge [of x]
  have "- sint x \<le> 2 ^ (LENGTH('a) - 1)" by simp
  also have "(2::int) ^ (LENGTH('a) - 1) < 2 ^ LENGTH('a)"
    by (rule power_strict_increasing) simp_all
  finally have "- sint x < 2 ^ LENGTH('a)" .
  then have "- (2 ^ LENGTH('a)) < sint x" by simp
  moreover from False have "0 < - sint x" by simp
  ultimately have "- sint x = - sint x mod 2 ^ LENGTH('a)"
    by (simp add: mod_pos_pos_trivial)
  also have "sint x mod 2 ^ LENGTH('a) \<noteq> 0"
  proof
    assume "sint x mod 2 ^ LENGTH('a) = 0"
    then obtain y where y: "sint x = y * 2 ^ LENGTH('a)" by auto
    with False have "\<not> 0 \<le> y" by auto
    then have "y \<le> - 1" by simp
    then have "y * 2 ^ LENGTH('a) \<le> - 1 * 2 ^ LENGTH('a)"
      by (rule mult_right_mono) simp
    with y have "sint x \<le> - (2 ^ LENGTH('a))" by simp
    with \<open>- (2 ^ LENGTH('a)) < sint x\<close> show False by simp
  qed
  then have "- sint x mod 2 ^ LENGTH('a) = 2 ^ LENGTH('a) - sint x mod 2 ^ LENGTH('a)"
    by (simp add: zmod_zminus1_eq_if)
  finally show ?thesis using False
    by (simp add: is_signed_positive_def uint_sint bintrunc_mod2p)
qed

type_synonym word8 = "8 word"

why3_open "bv/BV8.xml"
  constants
    zeros=zero_class.zero
    ones=max_word
    bw_and=bitAND
    bw_or=bitOR
    bw_xor=bitXOR
    bw_not=bitNOT
    add=plus
    sub=minus
    neg=uminus
    mul=times
    udiv=divide
    urem=modulo
    lsr=lsr
    asr=asr
    lsl=lsl
    lsr_bv=lsr_bv
    asr_bv=asr_bv
    lsl_bv=lsl_bv
    rotate_left=rotate_left
    rotate_right=rotate_right
    rotate_left_bv=rotate_left_bv
    rotate_right_bv=rotate_right_bv
    nth=bv_nth
    nth_bv=nth_bv
    tqtint=uint
    of_int=of_int
    eq_sub_bv=eq_sub_bv
    size_bv=size_bv
    one=one_class.one
    is_signed_positive=is_signed_positive
  types
    t=word8

why3_vc nth_out_of_bound
  using assms
  by (auto simp add: bv_nth_def test_bit_bin)

why3_vc Nth_zeros by (simp add: bv_nth_def)

why3_vc Nth_ones
  using assms
  by (simp add: bv_nth_def)

why3_vc Nth_bw_and
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_or
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_xor
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_not
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Lsr_nth_low
  using assms
  by (simp add: bv_nth_def nth_shiftr nat_add_distrib)

why3_vc Lsr_nth_high
  using assms
  by (simp add: bv_nth_def nth_shiftr)
    (simp add: test_bit_bin nat_add_distrib [symmetric] nat_less_iff)

why3_vc lsr_zeros by simp

why3_vc Asr_nth_low
  using assms
  by (simp add: bv_nth_def nth_sshiftr word_size)
    (simp add: nat_add_distrib [symmetric] le_nat_iff)

why3_vc Asr_nth_high
  using assms
  by (simp add: bv_nth_def nth_sshiftr word_size)
    (simp add: nat_add_distrib [symmetric] le_nat_iff nat_less_iff)

why3_vc asr_zeros by (simp add: sshiftr_def)

why3_vc Lsl_nth_high
  using assms
  by (simp add: bv_nth_def nth_shiftl nat_diff_distrib nat_less_iff nat_le_eq_zle)

why3_vc Lsl_nth_low
  using assms
  by (simp add: bv_nth_def nth_shiftl nat_le_eq_zle)

why3_vc lsl_zeros by simp

why3_vc to_uint_extensionality using assms by simp

why3_vc to_intqtdef by (simp add: to_int_eq)

why3_vc to_int_extensionality using assms by simp

why3_vc positive_is_ge_zeros
  by (simp add: is_signed_positive_def sge_def)

why3_vc to_uint_bounds
  using uint_lt [of v]
  by simp_all

why3_vc to_uint_of_int
  using assms
  by (simp add: uint_in_range_def word_of_int uint_word_of_int mod_pos_pos_trivial)

why3_vc nth_bv_def
  by (simp add: word_eq_iff word_ops_nth_size word_size nth_shiftr)

why3_vc Nth_bv_is_nth
  by (simp add: bv_nth_def unat_def)

why3_vc Nth_bv_is_nth2
  using assms
  by (simp add: bv_nth_def unat_def to_uint_of_int uint_in_range_def)

why3_vc to_uint_size_bv by (simp add: size_bv_def)

why3_vc to_uint_zeros by simp

why3_vc to_uint_one by simp

why3_vc to_uint_ones by (simp add: max_word_eq)

why3_vc to_uint_add
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_add_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_sub
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_sub_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_neg
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_mul
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_mul_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_udiv
  by (cases "uint v2 = 0")
    (simp_all add: uint_div ediv_def order.strict_iff_order)

why3_vc to_uint_urem
  by (simp add: uint_mod emod_def)

why3_vc Nth_rotate_left
  using assms rotl_nth [of "nat n" v "nat i + (size v - nat n mod size v)"]
  by (simp add: emod_def bv_nth_def word_size nat_minus_mod' int_minus_mod
    nat_mod_distrib nat_add_distrib nat_diff_distrib del: add_diff_assoc)

why3_vc Nth_rotate_right
  using assms rotr_nth [of "nat n" v "nat i"]
  by (simp add: emod_def bv_nth_def nat_mod_distrib nat_add_distrib)

why3_vc rotate_left_bv_is_rotate_left by (simp add: unat_def)

why3_vc rotate_right_bv_is_rotate_right by (simp add: unat_def)

why3_vc lsr_bv_is_lsr by (simp add: unat_def)

why3_vc to_uint_lsr
  by (simp add: ediv_def shiftr_div_2n unat_def)

why3_vc asr_bv_is_asr by (simp add: unat_def)

why3_vc lsl_bv_is_lsl by (simp add: unat_def)

why3_vc to_uint_lsl
  by (simp add: emod_def shiftl_t2n unat_def
    uint_word_ariths mult_ac uint_pow pull_mods [symmetric])

why3_vc Extensionality
  using assms
  by (simp add: eq_sub_def bv_nth_def word_eq_iff all_nat)

why3_vc eq_sub_equiv
  by (simp add: eq_sub_equiv_aux eq_sub_def eq_sub_bv_defn bv_nth_def)

why3_vc eq_sub_bv_def
  by (simp add: eq_sub_bv_defn mask_def)

why3_end


type_synonym word16 = "16 word"

why3_open "bv/BV16.xml"
  constants
    zeros=zero_class.zero
    ones=max_word
    bw_and=bitAND
    bw_or=bitOR
    bw_xor=bitXOR
    bw_not=bitNOT
    add=plus
    sub=minus
    neg=uminus
    mul=times
    udiv=divide
    urem=modulo
    lsr=lsr
    asr=asr
    lsl=lsl
    lsr_bv=lsr_bv
    asr_bv=asr_bv
    lsl_bv=lsl_bv
    rotate_left=rotate_left
    rotate_right=rotate_right
    rotate_left_bv=rotate_left_bv
    rotate_right_bv=rotate_right_bv
    nth=bv_nth
    nth_bv=nth_bv
    tqtint=uint
    of_int=of_int
    eq_sub_bv=eq_sub_bv
    size_bv=size_bv
    one=one_class.one
    is_signed_positive=is_signed_positive
  types
    t=word16

why3_vc nth_out_of_bound
  using assms
  by (auto simp add: bv_nth_def test_bit_bin)

why3_vc Nth_zeros by (simp add: bv_nth_def)

why3_vc Nth_ones
  using assms
  by (simp add: bv_nth_def)

why3_vc Nth_bw_and
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_or
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_xor
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_not
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Lsr_nth_low
  using assms
  by (simp add: bv_nth_def nth_shiftr nat_add_distrib)

why3_vc Lsr_nth_high
  using assms
  by (simp add: bv_nth_def nth_shiftr)
    (simp add: test_bit_bin nat_add_distrib [symmetric] nat_less_iff)

why3_vc lsr_zeros by simp

why3_vc Asr_nth_low
  using assms
  by (simp add: bv_nth_def nth_sshiftr word_size)
    (simp add: nat_add_distrib [symmetric] le_nat_iff)

why3_vc Asr_nth_high
  using assms
  by (simp add: bv_nth_def nth_sshiftr word_size)
    (simp add: nat_add_distrib [symmetric] le_nat_iff nat_less_iff)

why3_vc asr_zeros by (simp add: sshiftr_def)

why3_vc Lsl_nth_high
  using assms
  by (simp add: bv_nth_def nth_shiftl nat_diff_distrib nat_less_iff nat_le_eq_zle)

why3_vc Lsl_nth_low
  using assms
  by (simp add: bv_nth_def nth_shiftl nat_le_eq_zle)

why3_vc lsl_zeros by simp

why3_vc to_uint_extensionality using assms by simp

why3_vc to_intqtdef by (simp add: to_int_eq)

why3_vc to_int_extensionality using assms by simp

why3_vc positive_is_ge_zeros
  by (simp add: is_signed_positive_def sge_def)

why3_vc to_uint_bounds
  using uint_lt [of v]
  by simp_all

why3_vc to_uint_of_int
  using assms
  by (simp add: uint_in_range_def word_of_int uint_word_of_int mod_pos_pos_trivial)

why3_vc nth_bv_def
  by (simp add: word_eq_iff word_ops_nth_size word_size nth_shiftr)

why3_vc Nth_bv_is_nth
  by (simp add: bv_nth_def unat_def)

why3_vc Nth_bv_is_nth2
  using assms
  by (simp add: bv_nth_def unat_def to_uint_of_int uint_in_range_def)

why3_vc to_uint_size_bv by (simp add: size_bv_def)

why3_vc to_uint_zeros by simp

why3_vc to_uint_one by simp

why3_vc to_uint_ones by (simp add: max_word_eq)

why3_vc to_uint_add
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_add_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_sub
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_sub_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_neg
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_mul
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_mul_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_udiv
  by (cases "uint v2 = 0")
    (simp_all add: uint_div ediv_def order.strict_iff_order)

why3_vc to_uint_urem
  by (simp add: uint_mod emod_def)

why3_vc Nth_rotate_left
  using assms rotl_nth [of "nat n" v "nat i + (size v - nat n mod size v)"]
  by (simp add: emod_def bv_nth_def word_size nat_minus_mod' int_minus_mod
    nat_mod_distrib nat_add_distrib nat_diff_distrib del: add_diff_assoc)

why3_vc Nth_rotate_right
  using assms rotr_nth [of "nat n" v "nat i"]
  by (simp add: emod_def bv_nth_def nat_mod_distrib nat_add_distrib)

why3_vc rotate_left_bv_is_rotate_left by (simp add: unat_def)

why3_vc rotate_right_bv_is_rotate_right by (simp add: unat_def)

why3_vc lsr_bv_is_lsr by (simp add: unat_def)

why3_vc to_uint_lsr
  by (simp add: ediv_def shiftr_div_2n unat_def)

why3_vc asr_bv_is_asr by (simp add: unat_def)

why3_vc lsl_bv_is_lsl by (simp add: unat_def)

why3_vc to_uint_lsl
  by (simp add: emod_def shiftl_t2n unat_def
    uint_word_ariths mult_ac uint_pow pull_mods [symmetric])

why3_vc Extensionality
  using assms
  by (simp add: eq_sub_def bv_nth_def word_eq_iff all_nat)

why3_vc eq_sub_equiv
  by (simp add: eq_sub_equiv_aux eq_sub_def eq_sub_bv_defn bv_nth_def)

why3_vc eq_sub_bv_def
  by (simp add: eq_sub_bv_defn mask_def)

why3_end


type_synonym word32 = "32 word"

why3_open "bv/BV32.xml"
  constants
    zeros=zero_class.zero
    ones=max_word
    bw_and=bitAND
    bw_or=bitOR
    bw_xor=bitXOR
    bw_not=bitNOT
    add=plus
    sub=minus
    neg=uminus
    mul=times
    udiv=divide
    urem=modulo
    lsr=lsr
    asr=asr
    lsl=lsl
    lsr_bv=lsr_bv
    asr_bv=asr_bv
    lsl_bv=lsl_bv
    rotate_left=rotate_left
    rotate_right=rotate_right
    rotate_left_bv=rotate_left_bv
    rotate_right_bv=rotate_right_bv
    nth=bv_nth
    nth_bv=nth_bv
    tqtint=uint
    of_int=of_int
    eq_sub_bv=eq_sub_bv
    size_bv=size_bv
    one=one_class.one
    is_signed_positive=is_signed_positive
  types
    t=word32

why3_vc nth_out_of_bound
  using assms
  by (auto simp add: bv_nth_def test_bit_bin)

why3_vc Nth_zeros by (simp add: bv_nth_def)

why3_vc Nth_ones
  using assms
  by (simp add: bv_nth_def)

why3_vc Nth_bw_and
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_or
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_xor
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_not
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Lsr_nth_low
  using assms
  by (simp add: bv_nth_def nth_shiftr nat_add_distrib)

why3_vc Lsr_nth_high
  using assms
  by (simp add: bv_nth_def nth_shiftr)
    (simp add: test_bit_bin nat_add_distrib [symmetric] nat_less_iff)

why3_vc lsr_zeros by simp

why3_vc Asr_nth_low
  using assms
  by (simp add: bv_nth_def nth_sshiftr word_size)
    (simp add: nat_add_distrib [symmetric] le_nat_iff)

why3_vc Asr_nth_high
  using assms
  by (simp add: bv_nth_def nth_sshiftr word_size)
    (simp add: nat_add_distrib [symmetric] le_nat_iff nat_less_iff)

why3_vc asr_zeros by (simp add: sshiftr_def)

why3_vc Lsl_nth_high
  using assms
  by (simp add: bv_nth_def nth_shiftl nat_diff_distrib nat_less_iff nat_le_eq_zle)

why3_vc Lsl_nth_low
  using assms
  by (simp add: bv_nth_def nth_shiftl nat_le_eq_zle)

why3_vc lsl_zeros by simp

why3_vc to_uint_extensionality using assms by simp

why3_vc to_intqtdef by (simp add: to_int_eq)

why3_vc to_int_extensionality using assms by simp

why3_vc positive_is_ge_zeros
  by (simp add: is_signed_positive_def sge_def)

why3_vc to_uint_bounds
  using uint_lt [of v]
  by simp_all

why3_vc to_uint_of_int
  using assms
  by (simp add: uint_in_range_def word_of_int uint_word_of_int mod_pos_pos_trivial)

why3_vc nth_bv_def
  by (simp add: word_eq_iff word_ops_nth_size word_size nth_shiftr)

why3_vc Nth_bv_is_nth
  by (simp add: bv_nth_def unat_def)

why3_vc Nth_bv_is_nth2
  using assms
  by (simp add: bv_nth_def unat_def to_uint_of_int uint_in_range_def)

why3_vc to_uint_size_bv by (simp add: size_bv_def)

why3_vc to_uint_zeros by simp

why3_vc to_uint_one by simp

why3_vc to_uint_ones by (simp add: max_word_eq)

why3_vc to_uint_add
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_add_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_sub
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_sub_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_neg
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_mul
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_mul_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_udiv
  by (cases "uint v2 = 0")
    (simp_all add: uint_div ediv_def order.strict_iff_order)

why3_vc to_uint_urem
  by (simp add: uint_mod emod_def)

why3_vc Nth_rotate_left
  using assms rotl_nth [of "nat n" v "nat i + (size v - nat n mod size v)"]
  by (simp add: emod_def bv_nth_def word_size nat_minus_mod' int_minus_mod
    nat_mod_distrib nat_add_distrib nat_diff_distrib del: add_diff_assoc)

why3_vc Nth_rotate_right
  using assms rotr_nth [of "nat n" v "nat i"]
  by (simp add: emod_def bv_nth_def nat_mod_distrib nat_add_distrib)

why3_vc rotate_left_bv_is_rotate_left by (simp add: unat_def)

why3_vc rotate_right_bv_is_rotate_right by (simp add: unat_def)

why3_vc lsr_bv_is_lsr by (simp add: unat_def)

why3_vc to_uint_lsr
  by (simp add: ediv_def shiftr_div_2n unat_def)

why3_vc asr_bv_is_asr by (simp add: unat_def)

why3_vc lsl_bv_is_lsl by (simp add: unat_def)

why3_vc to_uint_lsl
  by (simp add: emod_def shiftl_t2n unat_def
    uint_word_ariths mult_ac uint_pow pull_mods [symmetric])

why3_vc Extensionality
  using assms
  by (simp add: eq_sub_def bv_nth_def word_eq_iff all_nat)

why3_vc eq_sub_equiv
  by (simp add: eq_sub_equiv_aux eq_sub_def eq_sub_bv_defn bv_nth_def)

why3_vc eq_sub_bv_def
  by (simp add: eq_sub_bv_defn mask_def)

why3_end


type_synonym word64 = "64 word"

why3_open "bv/BV64.xml"
  constants
    zeros=zero_class.zero
    ones=max_word
    bw_and=bitAND
    bw_or=bitOR
    bw_xor=bitXOR
    bw_not=bitNOT
    add=plus
    sub=minus
    neg=uminus
    mul=times
    udiv=divide
    urem=modulo
    lsr=lsr
    asr=asr
    lsl=lsl
    lsr_bv=lsr_bv
    asr_bv=asr_bv
    lsl_bv=lsl_bv
    rotate_left=rotate_left
    rotate_right=rotate_right
    rotate_left_bv=rotate_left_bv
    rotate_right_bv=rotate_right_bv
    nth=bv_nth
    nth_bv=nth_bv
    tqtint=uint
    of_int=of_int
    eq_sub_bv=eq_sub_bv
    size_bv=size_bv
    one=one_class.one
    is_signed_positive=is_signed_positive
  types
    t=word64

why3_vc nth_out_of_bound
  using assms
  by (auto simp add: bv_nth_def test_bit_bin)

why3_vc Nth_zeros by (simp add: bv_nth_def)

why3_vc Nth_ones
  using assms
  by (simp add: bv_nth_def)

why3_vc Nth_bw_and
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_or
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_xor
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Nth_bw_not
  using assms
  by (simp add: bv_nth_def word_ops_nth_size word_size)

why3_vc Lsr_nth_low
  using assms
  by (simp add: bv_nth_def nth_shiftr nat_add_distrib)

why3_vc Lsr_nth_high
  using assms
  by (simp add: bv_nth_def nth_shiftr)
    (simp add: test_bit_bin nat_add_distrib [symmetric] nat_less_iff)

why3_vc lsr_zeros by simp

why3_vc Asr_nth_low
  using assms
  by (simp add: bv_nth_def nth_sshiftr word_size)
    (simp add: nat_add_distrib [symmetric] le_nat_iff)

why3_vc Asr_nth_high
  using assms
  by (simp add: bv_nth_def nth_sshiftr word_size)
    (simp add: nat_add_distrib [symmetric] le_nat_iff nat_less_iff)

why3_vc asr_zeros by (simp add: sshiftr_def)

why3_vc Lsl_nth_high
  using assms
  by (simp add: bv_nth_def nth_shiftl nat_diff_distrib nat_less_iff nat_le_eq_zle)

why3_vc Lsl_nth_low
  using assms
  by (simp add: bv_nth_def nth_shiftl nat_le_eq_zle)

why3_vc lsl_zeros by simp

why3_vc to_uint_extensionality using assms by simp

why3_vc to_intqtdef by (simp add: to_int_eq)

why3_vc to_int_extensionality using assms by simp

why3_vc positive_is_ge_zeros
  by (simp add: is_signed_positive_def sge_def)

why3_vc to_uint_bounds
  using uint_lt [of v]
  by simp_all

why3_vc to_uint_of_int
  using assms
  by (simp add: uint_in_range_def word_of_int uint_word_of_int mod_pos_pos_trivial)

why3_vc nth_bv_def
  by (simp add: word_eq_iff word_ops_nth_size word_size nth_shiftr)

why3_vc Nth_bv_is_nth
  by (simp add: bv_nth_def unat_def)

why3_vc Nth_bv_is_nth2
  using assms
  by (simp add: bv_nth_def unat_def to_uint_of_int uint_in_range_def)

why3_vc to_uint_size_bv by (simp add: size_bv_def)

why3_vc to_uint_zeros by simp

why3_vc to_uint_one by simp

why3_vc to_uint_ones by (simp add: max_word_eq)

why3_vc to_uint_add
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_add_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_sub
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_sub_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_neg
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_mul
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p emod_def)

why3_vc to_uint_mul_bounded
  using assms
  by (simp add: uint_word_arith_bintrs bintrunc_mod2p mod_pos_pos_trivial)

why3_vc to_uint_udiv
  by (cases "uint v2 = 0")
    (simp_all add: uint_div ediv_def order.strict_iff_order)

why3_vc to_uint_urem
  by (simp add: uint_mod emod_def)

why3_vc Nth_rotate_left
  using assms rotl_nth [of "nat n" v "nat i + (size v - nat n mod size v)"]
  by (simp add: emod_def bv_nth_def word_size nat_minus_mod' int_minus_mod
    nat_mod_distrib nat_add_distrib nat_diff_distrib del: add_diff_assoc)

why3_vc Nth_rotate_right
  using assms rotr_nth [of "nat n" v "nat i"]
  by (simp add: emod_def bv_nth_def nat_mod_distrib nat_add_distrib)

why3_vc rotate_left_bv_is_rotate_left by (simp add: unat_def)

why3_vc rotate_right_bv_is_rotate_right by (simp add: unat_def)

why3_vc lsr_bv_is_lsr by (simp add: unat_def)

why3_vc to_uint_lsr
  by (simp add: ediv_def shiftr_div_2n unat_def)

why3_vc asr_bv_is_asr by (simp add: unat_def)

why3_vc lsl_bv_is_lsl by (simp add: unat_def)

why3_vc to_uint_lsl
  by (simp add: emod_def shiftl_t2n unat_def
    uint_word_ariths mult_ac uint_pow pull_mods [symmetric])

why3_vc Extensionality
  using assms
  by (simp add: eq_sub_def bv_nth_def word_eq_iff all_nat)

why3_vc eq_sub_equiv
  by (simp add: eq_sub_equiv_aux eq_sub_def eq_sub_bv_defn bv_nth_def)

why3_vc eq_sub_bv_def
  by (simp add: eq_sub_bv_defn mask_def)

why3_end


why3_open "bv/BVConverter_32_64.xml"
  constants
    toBig = ucast
    toSmall = ucast

why3_vc toSmall_to_uint
  using assms
  by (simp add: BV64.ule_def ucast_def uint_word_of_int mod_pos_pos_trivial)

why3_vc toBig_to_uint
  by (simp add: uint_up_ucast is_up)

why3_end


why3_open "bv/BVConverter_16_64.xml"
  constants
    toBig = ucast
    toSmall = ucast

why3_vc toSmall_to_uint
  using assms
  by (simp add: BV64.ule_def ucast_def uint_word_of_int mod_pos_pos_trivial)

why3_vc toBig_to_uint
  by (simp add: uint_up_ucast is_up)

why3_end


why3_open "bv/BVConverter_8_64.xml"
  constants
    toBig = ucast
    toSmall = ucast

why3_vc toSmall_to_uint
  using assms
  by (simp add: BV64.ule_def ucast_def uint_word_of_int mod_pos_pos_trivial)

why3_vc toBig_to_uint
  by (simp add: uint_up_ucast is_up)

why3_end


why3_open "bv/BVConverter_16_32.xml"
  constants
    toBig = ucast
    toSmall = ucast

why3_vc toSmall_to_uint
  using assms
  by (simp add: BV32.ule_def ucast_def uint_word_of_int mod_pos_pos_trivial)

why3_vc toBig_to_uint
  by (simp add: uint_up_ucast is_up)

why3_end


why3_open "bv/BVConverter_8_32.xml"
  constants
    toBig = ucast
    toSmall = ucast

why3_vc toSmall_to_uint
  using assms
  by (simp add: BV32.ule_def ucast_def uint_word_of_int mod_pos_pos_trivial)

why3_vc toBig_to_uint
  by (simp add: uint_up_ucast is_up)

why3_end


why3_open "bv/BVConverter_8_16.xml"
  constants
    toBig = ucast
    toSmall = ucast

why3_vc toSmall_to_uint
  using assms
  by (simp add: BV16.ule_def ucast_def uint_word_of_int mod_pos_pos_trivial)

why3_vc toBig_to_uint
  by (simp add: uint_up_ucast is_up)

why3_end

end