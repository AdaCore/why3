theory Why3_Map
imports Why3_Setup
begin

why3_open "Map.xml"

why3_vc Const by simp

why3_vc Select_eq
  using assms
  by simp

why3_vc Select_neq
  using assms
  by simp

why3_end

end
