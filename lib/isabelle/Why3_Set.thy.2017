theory Why3_Set
imports
  Why3_Setup
  Why3_Map
  "HOL-Library.FSet"
begin

section {* Potentially infinite sets *}

definition choose_elt :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "choose_elt S = (\<some>x. S x)"

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
    choose = choose_elt
    all = top

why3_vc add_spec by (auto simp add: mem_def)

why3_vc diff_def by simp

why3_vc diff_spec by (simp add: mem_def)

why3_vc inter_def by simp

why3_vc mem_empty by (simp add: const_def mem_def set.Set.is_empty_def)

why3_vc union_def by simp

why3_vc add_remove
  using assms
  by (simp add: fun_upd_idem_iff mem_def)

why3_vc inter_spec by (simp add: mem_def)

why3_vc remove_add by auto

why3_vc union_spec
  by (simp add: mem_def)

why3_vc choose_spec
  by (metis assms choose_elt_def mem_def set.Set.is_empty_def tfl_some)

why3_vc remove_spec
  by (simp add: mem_def)

why3_vc subset_diff
  by (simp add: diff_spec subset_def)

why3_vc subset_refl
  by (simp add: subset_def)

why3_vc subset_trans
  by (meson H1 H2 subset_def)

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

definition ext_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "ext_eq S1 S2 = (S1 = S2)"

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
    infix_eqeq = ext_eq
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
  using assms ext_eq_def fcard_seteq by fastforce

why3_vc subset_spec by auto

why3_vc infix_eqeq_spec
  by (metis ext_eq_def fsubset_antisym subset_spec)

why3_vc extensionality
  using assms
  by (auto simp add: ext_eq_def)

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
  using Why3_Set.is_empty_def
  by (metis (full_types) ex_fin_conv fchoose_def someI_ex)

why3_vc is_empty_spec
  by (simp add: Why3_Set.is_empty_def)

why3_end

end
