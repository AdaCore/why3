theory Why3_Setup
imports Main
keywords
  "why3_open" "why3_end" :: thy_decl and
  "why3_vc" :: thy_goal and "why3_status" :: diag
begin

ML_file "why3.ML"

setup Why3.setup

end
