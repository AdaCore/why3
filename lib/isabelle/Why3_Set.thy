theory Why3_Set
imports
  Why3_Setup
  Why3_Map
  "HOL-Library.FSet"
begin

section {* Potentially infinite sets *}

definition complement :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "complement S v = Not (S v)"

definition mapi :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)" where
  "mapi f s x = Set.member x (image f (Collect s))"

why3_open "set/Set.xml"
  constants
    empty = bot
    add = insert
    remove = Set.remove
    union = sup
    inter = inf
    diff = minus
    complement = complement
    pick = Eps
    all = top
    map = mapi

why3_vc diffqtdef by (simp add: mem_def)

why3_vc interqtdef by (simp add: mem_def)

why3_vc is_empty_empty by (simp add: constqtdef mem_def set.Set.is_empty_def)

why3_vc unionqtdef by (simp add: mem_def)

why3_vc add_remove
  using assms
  by (simp add: fun_upd_idem_iff mem_def)

why3_vc remove_add by auto

why3_vc pick_def
  using assms
  by (auto simp add: mem_def is_empty_def intro: someI_ex)

why3_vc subset_diff
  by (simp add: mem_def diffqtdef subset_def)

why3_vc subset_refl
  by (simp add: subset_def)

why3_vc subset_trans
  using assms
  by (simp add: subset_def)

why3_vc subset_remove
  by (simp add: mem_def remove_def subset_def)

why3_vc complementqtdef
  by (simp add: mem_def complement_def)

why3_vc extensionality
  using assms
  by (auto simp add: infix_eqeq_def mem_def)

why3_vc mapqtdef by (simp add: mem_def mapi_def image_iff)

why3_vc mem_map
  using assms
  by (meson facts.mapqtdef mem_def)

why3_vc mem_singleton
  by (metis assms constqtdef fun_upd_other mem_def) 

why3_vc empty_is_empty
  using assms
  by (meson extensionality infix_eqeq_def is_empty_empty set.Set.is_empty_def)

why3_vc subset_inter_1
  by (simp add: set.Set.subset_def mem_def)

why3_vc subset_inter_2
  by (simp add: set.Set.subset_def mem_def)

why3_vc subset_union_1
  by (simp add: set.Set.subset_def mem_def)

why3_vc subset_union_2
  by (simp add: set.Set.subset_def mem_def)

why3_vc disjoint_diff_eq
  by (smt diffqtdef disjoint_def extensionality infix_eqeq_def mem_def)

why3_vc disjoint_diff_s2
  by (simp add: disjoint_def mem_def)

why3_vc disjoint_inter_empty
  by (simp add: disjoint_def mem_def set.Set.is_empty_def)

why3_end


section {* Finite sets *}

definition fremove :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "fremove x A = A - {|x|}"

definition fchoose :: "'a fset \<Rightarrow> 'a" where
  "fchoose S = (\<some>x. x |\<in>| S)"

definition is_empty :: "'a fset \<Rightarrow> bool" where
  "is_empty S = (S = fempty)"

definition filter :: "'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a fset" where
  "filter S p = ffilter p S"

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
    pick = fchoose
    filter = filter
    map = fimage
  types
    fset = fset

why3_vc add_def by auto

why3_vc add_remove
  using assms
  by (auto simp add: fremove_def)

why3_vc remove_add by (simp add: fremove_def)

why3_vc map_def by auto

why3_vc mem_map by (simp add: assms)

why3_vc inter_def by simp

why3_vc union_def by simp

why3_vc remove_def by (auto simp add: fremove_def)

why3_vc diff_def by auto

why3_vc pick_def
  using assms
  by (auto simp add: fchoose_def is_empty_def intro: someI_ex)

why3_vc subset_diff by (simp add: Fset.subset_def)

why3_vc subset_refl by (simp add: Fset.subset_def)

why3_vc subset_trans 
  using assms
  by (simp add: Fset.subset_def)

why3_vc subset_remove by (auto simp add: Fset.subset_def fremove_def)

why3_vc subset_eq
  using assms fcard_seteq
  by (metis Fset.subset_def eq_imp_le fsubsetI of_nat_eq_iff)

why3_vc extensionality
  using assms
  by (simp add:  Fset.infix_eqeq_def fset_eqI)

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

why3_vc cardinal_add by (auto simp add: fcard_finsert_if finsert_absorb)

why3_vc cardinal_empty by (simp add: is_empty_def)

why3_vc cardinal_nonneg by simp

lemma cardinal_remove_in: 
  "x |\<in>| s \<longrightarrow> int (fcard (fremove x s)) = int (fcard s) - 1"
  by (smt cardinal_add(2) fminus_finsert_absorb fremove_def set_finsert)

lemma cardinal_remove_out:
  "x |\<notin>| s \<longrightarrow> int (fcard (fremove x s)) = int (fcard s)"
  by (simp add: fremove_def)

why3_vc cardinal_remove by (auto simp add: cardinal_remove_out cardinal_remove_in)

why3_vc cardinal_subset
  using assms
  by (simp add: Fset.subset_def fcard_mono fsubsetI)

why3_vc filter_def by (simp add: Why3_Set.filter_def)

why3_vc cardinal_map
  apply (simp add: fcard_def card_def)
  by (metis card_def card_image_le finite_fset)

why3_vc cardinal_diff
  by (metis fcard_funion_fsubset fcard_mono fminus_finter2 inf.idem inf_commute inf_sup_ord(1) of_nat_diff)
(*  by (smt fcard_funion_fsubset fcard_mono finter_lower1 fminus_finter2 inf.idem inf_commute int_ops(6) of_nat_mono)*)

why3_vc mem_singleton
  using assms by auto

why3_vc subset_filter
  by (simp add: Fset.subset_def Why3_Set.filter_def)

why3_vc cardinal_union
  by (smt fcard_funion_finter of_nat_add)

why3_vc empty_is_empty
  by (meson Fset.is_empty_def assms bot.extremum_uniqueI fsubsetI)

why3_vc is_empty_empty
  by (simp add: cardinal_empty)

why3_vc subset_inter_1
  by (simp add: Fset.subset_def)

why3_vc subset_inter_2
  by (simp add: Fset.subset_def)

why3_vc subset_union_1
  by (simp add: Fset.subset_def)

why3_vc subset_union_2
  by (simp add: Fset.subset_def)

why3_vc cardinal_filter
  using cardinal_subset subset_filter by blast

why3_vc disjoint_diff_eq
  by (smt Fset.disjoint_def Fset.facts.diff_def fsubsetI fsubset_antisym)

why3_vc  disjoint_diff_s2
  by (simp add: Fset.facts.disjoint_diff_eq)

why3_vc disjoint_inter_empty
  by (metis Fset.facts.disjoint_diff_eq Fset.facts.empty_is_empty Fset.facts.is_empty_empty fminus_disjoint fminus_triv) 

why3_vc cardinal_inter_disjoint
  by (meson Fset.facts.disjoint_inter_empty assms cardinal_empty)

why3_end

end
