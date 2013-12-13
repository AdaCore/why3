theory genealogy_Genealogy_Sibling_is_brother_or_sister_1
imports Why3
begin

why3_open "genealogy_Genealogy_Sibling_is_brother_or_sister_1.xml"

why3_vc Sibling_is_brother_or_sister
by (metis brother_def gender.exhaust sister_def)

why3_end

end
