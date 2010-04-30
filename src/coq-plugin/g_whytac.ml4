
(*i camlp4deps: "parsing/grammar.cma" i*)

open Whytac

TACTIC EXTEND Why
  [ "why" string(s) ] -> [ whytac s ]
END
