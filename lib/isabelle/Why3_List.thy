theory Why3_List
imports Why3_Setup
begin

section {* Length of a list *}

why3_open "list/Length.xml"

why3_vc lengthqtdef by (cases l) simp_all

why3_vc Length_nil by simp

why3_vc Length_nonnegative by simp

why3_end


section {* Membership in a list *}

why3_open "list/Mem.xml"

why3_vc memqtdef by (simp split: list.split)

why3_end


section {* Nth element of a list *}

why3_open "list/Nth.xml"

lemma nth_eq: "0 \<le> i \<Longrightarrow> nat i < length xs \<Longrightarrow> nth i xs = Some (xs ! nat i)"
  by (induct xs arbitrary: i) (auto simp add: nat_diff_distrib)

why3_vc is_noneqtspec
  by (simp add: is_none_def split: option.split)

why3_end


why3_open "list/NthNoOpt.xml"

why3_vc nth_cons_0 by simp

why3_vc nth_cons_n
  using assms
  by (simp add: nat_diff_distrib)

why3_end


why3_open "list/NthLength.xml"

why3_vc nth_none_1
  using assms
  by (induct l arbitrary: i) simp_all

why3_vc nth_none_2
  using assms
  by (induct l arbitrary: i) simp_all

why3_vc nth_none_3
  using assms
proof (induct l arbitrary: i)
  case Nil
  then show ?case by simp arith
next
  case (Cons x xs)
  show ?case
  proof (cases "i < 0")
    case False
    with Cons have "0 < i" by (simp split: if_split_asm)
    with Cons have "Nth.nth (i - 1) xs = None" by simp
    then have "i - 1 < 0 \<or> int (length xs) \<le> i - 1"
      by (rule Cons)
    with `0 < i` show ?thesis by auto
  qed simp
qed

why3_vc is_noneqtspec
  by (simp add: is_none_def split: option.split)

why3_end


section {* Head and tail *}

why3_open "list/HdTl.xml"

why3_vc is_noneqtspec
  by (simp add: is_none_def split: option.split)

why3_end


why3_open "list/HdTlNoOpt.xml"

why3_vc hd_cons by simp

why3_vc tl_cons by simp

why3_end


section {* Relation between head, tail, and nth *}

why3_open "list/NthHdTl.xml"

why3_vc Nth_tl
  using assms
  by (simp add: tl_def split: list.split_asm)

why3_vc Nth0_head
  by (simp add: hd_def split: list.split)

why3_vc is_noneqtspec
  by (simp add: is_none_def split: option.split)

why3_end


section {* Appending two lists *}

why3_open "list/Append.xml"

why3_vc infix_plplqtdef by (simp split: list.split)

why3_vc Append_assoc by simp

why3_vc Append_l_nil by simp

why3_vc Append_length by simp

why3_vc mem_append by simp

why3_vc mem_decomp
  using assms
  by (simp add: in_set_conv_decomp)

why3_end


why3_open "list/NthLengthAppend.xml"

why3_vc nth_append_1
proof (cases "0 \<le> i")
  case True
  with assms have "nat i < length l1" by simp
  with True show ?thesis
    by (simp add: nth_eq nth_append)
next
  case False
  then show ?thesis by (simp add: nth_none_1)
qed

why3_vc nth_append_2
proof (cases "nat i < length (l1 @ l2)")
  case True
  with assms show ?thesis
    by (auto simp add: nth_eq nth_append nat_diff_distrib)
next
  case False
  with assms show ?thesis by (simp add: nth_none_2)
qed

why3_vc is_noneqtspec
  by (simp add: is_none_def split: option.split)

why3_end


section {* Reversing a list *}

why3_open "list/Reverse.xml"

why3_vc reverseqtdef by (simp split: list.split)

why3_vc Reverse_length by simp

why3_vc reverse_append by simp

why3_vc reverse_reverse by simp

why3_vc reverse_mem by simp

why3_vc reverse_cons by simp

why3_vc cons_reverse by simp

why3_end


section {* Reverse append *}

why3_open "list/RevAppend.xml"

why3_vc rev_append_append_l
  by (induct r arbitrary: t) simp_all

why3_vc rev_append_append_r
proof (induct s arbitrary: r)
  case (Cons x xs)
  show ?case by (simp add: Cons [symmetric])
qed simp

why3_vc rev_append_length
  by (induct s arbitrary: t) simp_all

why3_vc rev_append_def
  by (induct r arbitrary: s) simp_all

why3_end


section {* Zip *}

why3_open "list/Combine.xml"

why3_end


section {* List with pairwise distinct elements *}

why3_open "list/Distinct.xml"

why3_vc distinct_zero by simp

why3_vc distinct_one by simp

why3_vc distinct_many using assms by simp

why3_vc distinct_append using assms by auto

why3_end


section {* Number of occurrences in a list *}

why3_open "list/NumOcc.xml"

why3_vc Num_Occ_NonNeg
  by (induct l) simp_all

why3_vc Mem_Num_Occ
proof (induct l)
  case (Cons y ys)
  from Num_Occ_NonNeg [of y ys]
  have "0 < 1 + num_occ y ys" by simp
  with Cons show ?case by simp
qed simp

why3_vc Append_Num_Occ
  by (induct l1) simp_all

why3_vc reverse_num_occ
  by (induct l) (simp_all add: Append_Num_Occ)

why3_end


section {* Permutation of lists *}

why3_open "list/Permut.xml"

why3_vc Permut_refl by (simp add: permut_def)

why3_vc Permut_sym using assms by (simp add: permut_def)

why3_vc Permut_trans using assms by (simp add: permut_def)

why3_vc Permut_cons using assms by (simp add: permut_def)

why3_vc Permut_swap by (simp add: permut_def)

why3_vc Permut_cons_append by (simp add: permut_def Append_Num_Occ)

why3_vc Permut_assoc by (simp add: permut_def)

why3_vc Permut_append using assms by (simp add: permut_def Append_Num_Occ)

why3_vc Permut_append_swap by (simp add: permut_def Append_Num_Occ)

why3_vc Permut_mem using assms by (simp add: permut_def Mem_Num_Occ)

why3_vc Permut_length
  using assms
proof (induct l1 arbitrary: l2)
  case Nil
  then show ?case
  proof (cases l2)
    case (Cons x xs)
    with Nil Num_Occ_NonNeg [of x xs]
    show ?thesis by (auto simp add: permut_def dest: spec [of _ x])
  qed simp
next
  case (Cons x xs)
  from `permut (x # xs) l2` have "x \<in> set l2"
    by (rule Permut_mem) simp
  then obtain ys zs where "l2 = ys @ x # zs"
    by (auto simp add: in_set_conv_decomp)
  with Cons have "permut (x # xs) (ys @ x # zs)" by simp
  moreover have "permut (ys @ x # zs) ((x # zs) @ ys)"
    by (rule Permut_append_swap)
  ultimately have "permut (x # xs) ((x # zs) @ ys)"
    by (rule Permut_trans)
  then have "permut xs (zs @ ys)" by (simp add: permut_def)
  then have "int (length xs) = int (length (zs @ ys))" by (rule Cons)
  with `l2 = ys @ x # zs` show ?case by simp
qed

why3_end

end
