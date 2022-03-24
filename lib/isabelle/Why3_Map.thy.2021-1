theory Why3_Map
imports Why3_Setup
begin

section {* Generic Maps *}

why3_open "map/Map.xml"

why3_vc setqtdef by auto

why3_end


section {* Constant Maps *}

definition abs_const :: "'a \<Rightarrow> ('b \<Rightarrow> 'a)" where
  "abs_const v y = v"

why3_open "map/Const.xml"
  constants
    const=abs_const

why3_vc constqtdef
  by (simp add: abs_const_def)

why3_end

section {* Number of occurrences *}

definition occ :: "'a \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "occ v m l u = int (card (m -` {v} \<inter> {l..<u}))"

why3_open "map/Occ.xml"
  constants
    occ = occ

why3_vc occ_empty
  using assms
  by (simp add: occ_def)

why3_vc occ_right_no_add
proof -
  from assms have "{l..<u} = {l..<u - 1} \<union> {u - 1}" by auto
  with assms show ?thesis by (simp add: occ_def)
qed

why3_vc occ_right_add
proof -
  from assms have "{l..<u} = {l..<u - 1} \<union> {u - 1}" by auto
  with assms show ?thesis by (simp add: occ_def)
qed

why3_vc occ_bounds
proof -
  have "card ({l..<u} \<inter> m -` {v}) \<le> card {l..<u}"
    by (blast intro: card_mono)
  moreover have "card ({l..<u} - m -` {v}) = card {l..<u} - card ({l..<u} \<inter> m -` {v})"
    by (blast intro: card_Diff_subset_Int)
  ultimately have "card {l..<u} = card ({l..<u} - m -` {v}) + card ({l..<u} \<inter> m -` {v})"
    by simp
  with assms show ?C2
    by (simp add: occ_def Int_commute)
qed (simp add: occ_def)

why3_vc occ_append
proof -
  from assms have "{l..<u} = {l..<mid} \<union> {mid..<u}"
    by (simp add: ivl_disj_un)
  moreover have "m -` {v} \<inter> {l..<mid} \<inter> (m -` {v} \<inter> {mid..<u}) =
    m -` {v} \<inter> ({l..<mid} \<inter> {mid..<u})"
    by auto
  ultimately show ?thesis
    by (simp add: occ_def Int_Un_distrib card_Un_disjoint)
qed

why3_vc occ_neq
  using assms
  by (auto simp add: occ_def)

why3_vc occ_exists
  using assms
  by (auto simp add: occ_def card_gt_0_iff)

why3_vc occ_pos
  using assms
  by (auto simp add: occ_def card_gt_0_iff)

why3_vc occ_eq
proof -
  from assms have "m1 -` {v} \<inter> {l..<u} = m2 -` {v} \<inter> {l..<u}" by auto
  then show ?thesis by (simp add: occ_def)
qed

lemma vimage_update:
  "m(i := x) -` {z} = (if x = z then m -` {z} \<union> {i} else m -` {z} - {i})"
  by auto

why3_vc occ_exchange
  using assms
  by (simp add: occ_def vimage_update insert_Diff_if card.insert_remove)
    (auto simp add: Diff_Int_distrib2 card_Diff_subset_Int)

why3_vc occ_left_add
proof -
  from assms have "{l..<u} = {l} \<union> {l + 1..<u}" by auto
  with assms show ?thesis by (simp add: occ_def)
qed

why3_vc occ_left_no_add
proof -
  from assms have "{l..<u} = {l} \<union> {l + 1..<u}" by auto
  with assms show ?thesis by (simp add: occ_def)
qed

why3_end

why3_open "map/MapPermut.xml"

why3_vc permut_trans
  using assms
  by (simp add: permut_def)

why3_vc permut_exists
proof -
  from assms have "0 < occ (a2 i) a1 l u"
    by (simp add: permut_def occ_pos)
  then show ?thesis by (auto dest: occ_exists)
qed

why3_end


section {* Injectivity and surjectivity for maps (indexed by integers) *}

why3_open "map/MapInjection.xml"

why3_vc injective_surjective
proof -
  have "finite {0..<n}" by simp
  moreover from assms have "a ` {0..<n} \<subseteq> {0..<n}"
    by (auto simp add: range_def)
  moreover from assms have "inj_on a {0..<n}"
    by (force intro!: inj_onI simp add: injective_def)
  ultimately have "a ` {0..<n} = {0..<n}" by (rule endo_inj_surj)
  then have "{0..<n} \<subseteq> a ` {0..<n}" by simp
  then show ?thesis by (force simp add: surjective_def)
qed

why3_vc injection_occ
  unfolding injective_def occ_def
proof
  assume H: "\<forall>i j. 0 \<le> i \<and> i < n \<longrightarrow> 0 \<le> j \<and> j < n \<longrightarrow> i \<noteq> j \<longrightarrow> m i \<noteq> m j"
  show "\<forall>v. int (card (m -` {v} \<inter> {0..<n})) \<le> 1"
  proof
    fix v
    let ?S = "m -` {v} \<inter> {0..<n}"
    show "int (card ?S) \<le> 1"
    proof (rule ccontr)
      assume "\<not> int (card ?S) \<le> 1"
      with card_le_Suc_iff [of 1 ?S]
      obtain x S where "?S = insert x S"
        "x \<notin> S" "1 \<le> card S" "finite S"
        by auto
      with card_le_Suc_iff [of 0 S]
      obtain x' S' where "S = insert x' S'" by auto
      with `?S = insert x S` `x \<notin> S`
      have "m x = v" "m x' = v" "x \<noteq> x'" "0 \<le> x" "x < n" "0 \<le> x'" "x' < n"
        by auto
      with H show False by auto
    qed
  qed
next
  assume H: "\<forall>v. int (card (m -` {v} \<inter> {0..<n})) \<le> 1"
  show "\<forall>i j. 0 \<le> i \<and> i < n \<longrightarrow> 0 \<le> j \<and> j < n \<longrightarrow> i \<noteq> j \<longrightarrow> m i \<noteq> m j"
  proof (intro strip notI)
    fix i j
    let ?S = "m -` {m i} \<inter> {0..<n}"
    assume "0 \<le> i \<and> i < n" "0 \<le> j \<and> j < n" "i \<noteq> j" "m i = m j"
    have "finite ?S" by simp
    moreover from `0 \<le> i \<and> i < n` have "i \<in> ?S" by simp
    ultimately have S: "card ?S = Suc (card (?S - {i}))"
      by (rule card.remove)
    have "finite (?S - {i})" by simp
    moreover from `0 \<le> j \<and> j < n` `i \<noteq> j` `m i = m j`
    have "j \<in> ?S - {i}" by simp
    ultimately have "card (?S - {i}) = Suc (card (?S - {i} - {j}))"
      by (rule card.remove)
    with S have "\<not> int (card ?S) \<le> 1" by simp
    with H show False by simp
  qed
qed

why3_end

end
