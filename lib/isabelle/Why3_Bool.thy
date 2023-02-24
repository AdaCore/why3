theory Why3_Bool
imports Why3_Setup
begin

section \<open> Basic theory of Booleans \<close>

why3_open "bool/Bool.xml"

why3_vc andbqtdef by (simp split: bool.split)

why3_vc orbqtdef by (simp split: bool.split)

why3_vc xorbqtdef by (simp split: bool.split)

why3_vc notbqtdef by (simp split: bool.split)

why3_vc implbqtdef by (simp split: bool.split)

why3_end

end
