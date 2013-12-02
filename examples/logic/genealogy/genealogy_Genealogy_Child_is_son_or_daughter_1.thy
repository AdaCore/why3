theory genealogy_Genealogy_Child_is_son_or_daughter_1
imports Why3
begin

why3_open "genealogy_Genealogy_Child_is_son_or_daughter_1.xml"

why3_vc Child_is_son_or_daughter
proof -
  have "parent p c \<longrightarrow> son c p \<or> gender1 c = Female"
    using gender.exhaust son_def by auto
  thus "parent p c = (son c p \<or> daughter c p)"
    using daughter_def son_def by auto
qed

why3_end

end
