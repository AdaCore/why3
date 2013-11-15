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

end
