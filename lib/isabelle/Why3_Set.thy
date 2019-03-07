theory Why3_Set
imports
  Why3_Setup
  Why3_Map
  "HOL-Library.FSet"
begin

section {* Potentially infinite sets *}

definition complement :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "complement S v = Not (S v)"

why3_open "set/Set.xml"
  constants
    empty = bot
    add = insert
    remove = Set.remove
    union = sup
    inter = inf
    diff = minus
    complement = complement
    choose = Eps
    all = top

why3_vc add_spec by (auto simp add: mem_def)

why3_vc diff_def by simp

why3_vc diff_spec by (simp add: mem_def)

why3_vc inter_def by simp

why3_vc is_empty_empty by (simp add: const_def mem_def set.Set.is_empty_def)

why3_vc union_def by simp

why3_vc add_remove
  using assms
  by (simp add: fun_upd_idem_iff mem_def)

why3_vc inter_spec by (simp add: mem_def)

why3_vc remove_add by auto

why3_vc union_spec
  by (simp add: mem_def)

why3_vc choose_spec
  using assms
  by (auto simp add: mem_def is_empty_def intro: someI_ex)

why3_vc remove_spec
  by (simp add: mem_def)

why3_vc subset_diff
  by (simp add: diff_spec subset_def)

why3_vc subset_refl
  by (simp add: subset_def)

why3_vc subset_trans
  using assms
  by (simp add: subset_def)

why3_vc subset_remove
  by (simp add: remove_spec subset_def)

why3_vc complement_def
  by (simp add: complement_def)

why3_vc extensionality
  using assms
  by (auto simp add: infix_eqeq_def mem_def)

why3_end


section {* Finite sets *}

definition fremove :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "fremove x A = A - {|x|}"

definition fchoose :: "'a fset \<Rightarrow> 'a" where
  "fchoose S = (\<some>x. x |\<in>| S)"

definition is_empty :: "'a fset \<Rightarrow> bool" where
  "is_empty S = (S = fempty)"

why3_open "set/Fset.xml"
  constants
    mem = fmember
    empty = bot
    add = finsert
    remove = fremove
    union = sup
    inter = inf
    diff = minus
    choose = fchoose
    all = top
    infix_eqeq = HOL.eq
    subset = fsubset_eq
    is_empty = is_empty
  types
    set = fset

why3_vc add_spec by simp

why3_vc add_remove
  using assms
  by (auto simp add: fremove_def)

why3_vc remove_add by (simp add: fremove_def)

why3_vc empty_def by (simp add: is_empty_def)

why3_vc inter_spec by simp

why3_vc union_spec by simp

why3_vc remove_spec by (auto simp add: fremove_def)

why3_vc subset_diff by auto

why3_vc subset_refl by simp

why3_vc subset_trans
  using assms
  by simp

why3_vc subset_remove by (auto simp add: fremove_def)

why3_vc subset_eq
  using assms fcard_seteq by fastforce

why3_vc subset_spec by auto

why3_vc infix_eqeq_spec
  by (simp add: fset_eq_iff)

why3_vc extensionality
  using assms
  by simp

why3_vc cardinal1
proof (cases s rule: fset_strong_cases)
  case 1
  with assms
  show ?thesis by (simp add: fcard_fempty)
next
  case (2 s' x)
  show ?thesis
  proof (cases s' rule: fset_strong_cases)
    case 1
    with `s = finsert x s'` assms
    show ?thesis by (simp add: fchoose_def)
  next
    case (2 s'' y)
    with `s = finsert x s'` assms
    show ?thesis by (auto simp add: fcard_finsert_if fchoose_def
      split: if_split_asm)
  qed
qed

why3_vc cardinal_add
  using assms
  by (simp add: fcard_finsert_disjoint)

why3_vc cardinal_empty by (simp add: is_empty_def)

why3_vc cardinal_nonneg by simp

why3_vc cardinal_remove
proof -
  from assms
  have "1 \<le> fcard s"
    by (cases s rule: fset_strong_cases)
      (auto simp add: fcard_finsert_disjoint)
  with assms show ?thesis
    by (simp add: fremove_def)
qed

why3_vc cardinal_subset
  using assms
  by (simp add: fcard_mono)

why3_vc diff_spec by simp

why3_vc choose_spec
  using assms
  by (auto simp add: fchoose_def is_empty_def intro: someI_ex)

why3_vc is_empty_spec
  by (simp add: Why3_Set.is_empty_def)

why3_end

end
