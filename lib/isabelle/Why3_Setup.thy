theory Why3_Setup
imports Main
keywords
  "why3_open" :: thy_load and
  "why3_end" "why3_consts" "why3_types" "why3_thms" "why3_defs" :: thy_decl and
  "why3_vc" :: thy_goal and "why3_status" :: diag
begin

ML_file "why3.ML"

setup Why3.setup

end
