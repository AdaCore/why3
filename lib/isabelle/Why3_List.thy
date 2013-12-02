theory Why3_List
imports Why3_Setup
begin

section {* Length of a list *}

why3_open "Length.xml"

why3_vc length_def by (cases l) simp_all

why3_vc Length_nil by simp

why3_vc Length_nonnegative by simp

why3_end


section {* Membership in a list *}

why3_open "Mem.xml"

why3_vc mem_def by (simp split add: list.split)

why3_end


section {* Nth element of a list *}

why3_open "Nth.xml"

lemma nth_eq: "0 \<le> i \<Longrightarrow> nat i < length xs \<Longrightarrow> nth i xs = Some (xs ! nat i)"
  by (induct xs arbitrary: i) (auto simp add: nat_diff_distrib)

why3_end


why3_open "NthNoOpt.xml"

why3_vc nth_cons_0 by simp

why3_vc nth_cons_n
  using assms
  by (simp add: nat_diff_distrib)

why3_end


why3_open "NthLength.xml"

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
    with Cons have "0 < i" by (simp split add: split_if_asm)
    with Cons have "Nth.nth (i - 1) xs = None" by simp
    then have "i - 1 < 0 \<or> int (length xs) \<le> i - 1"
      by (rule Cons)
    with `0 < i` show ?thesis by auto
  qed simp
qed

why3_end


section {* Head and tail *}

why3_open "HdTl.xml"

why3_end


section {* Relation between head, tail, and nth *}

why3_open "NthHdTl.xml"

why3_vc Nth_tl
  using assms
  by (simp add: tl_def split add: list.split_asm)

why3_vc Nth0_head
  by (simp add: hd_def split add: list.split)

why3_end


section {* Appending two lists *}

why3_open "Append.xml"

why3_vc infix_plpl_def by (simp split add: list.split)

why3_vc Append_assoc by simp

why3_vc Append_l_nil by simp

why3_vc Append_length by simp

why3_vc mem_append by simp

why3_vc mem_decomp
  using assms
  by (simp add: in_set_conv_decomp)

why3_end


why3_open "NthLengthAppend.xml"

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

why3_end


section {* Reversing a list *}

why3_open "Reverse.xml"

why3_vc reverse_def by (simp split add: list.split)

why3_vc Reverse_length by simp

why3_vc reverse_append by simp

why3_vc reverse_reverse by simp

why3_end

end
