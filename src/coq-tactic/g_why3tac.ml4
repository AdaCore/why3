(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Why3tac

TACTIC EXTEND Why3
  [ "why3" string(s) ] -> [ why3tac s ]
| [ "why3" string(s) "timelimit" integer(n) ] -> [ why3tac ~timelimit:n s ]
END
