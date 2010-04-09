
let x = Why.Ident.id_fresh "x"

let whytac gl =
  Tactics.admit_as_an_axiom gl

let _ =
  Tacinterp.overwriting_add_tactic "Why" (fun _ -> whytac);
  Egrammar.extend_tactic_grammar "Why" [[Egrammar.TacTerm "why"]]

