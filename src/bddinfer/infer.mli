(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(**

{1 The core abstract interpretation engine}

*)

(* open Why3 *)
(* to comment out when inside Why3 *)


type interp_report = {
    final_state : Abstract.t;
    invariants : Abstract.t Wstdlib.Mstr.t;
    entry_states : Abstract.t Wstdlib.Mstr.t;
    checks : (bool * string * Ast.condition * bool) Wstdlib.Mstr.t;
    widenings : int;
  }
(** The datatype for results of abstract interpretation. [final_state]
   is the abstract state and the end of the execution of the
   program. [invariants] is the set of invariants generated for each
   loop. It is a map indexed by the tags of loop
   statements. [entry_states] is also a map indexed by statements
   tags: for each statement annotated with a tag, the abstract state
   *before* the execution of this statement is provided by this
   map. [checks] is the report on the set of checks that were
   performed. It is again a map indexed by statement tags, associating
   to each statements a 4-uple [(is_inv, name, cond,
   result)]. [is_inv] is true when the check concerns a user-provided
   loop invariant, and [false] when it is a assert statement. [name]
   is the tag of the condition if any, [cond] is the condition itself
   and [result] is the result of the check, true meaning that the
   condition [cond] holds for any execution.  *)

val interp_prog :
  Ast.why1program -> interp_report
(** The main entry point for interpreting a program. It returns a
   report as defined above.  *)

val report : verbosity:int -> interp_report -> unit
(** provides a readable report on standard output. verbosity level 0
   will only report whether the user invariant and assertions are
   validated by the infered ones. Level 2 report the generated
   invariants. Level 3 reports abstract states computed *)
