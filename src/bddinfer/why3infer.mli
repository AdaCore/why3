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

{1 Inference of loop invariants for WhyML code, using BDDinfer
   subcomponent}

*)

(* open Why3 *)
(* to comment out when inside Why3 *)


val infer_loop_invs :
  Ident.Sattr.t ->
  Env.env ->
  Decl.known_map ->
  Pdecl.known_map ->
  Expr.expr -> Ity.cty -> (Expr.expr * Term.term) list
(** [infer_loop_invs ~verbose_level attrs env tkn mkn e cty] infers
   loop invariants for the given WhyML expression [e]. [e] is assumed
   to be the body of a WhyML function which attributes are [attrs] and
   computation type is [cty]. The other parameters [env], [tkn] and
   [mkn] are respectively the environment, the theory known map and
   the module known map of that function.

  The set [attrs] is checked for the presence of the [[\@bddinfer]]
  attribute. Without it, the empty list is immediately returned.  If
  that [[\@bddinfer]] attribute is followed by a colon and a number,
  like [[\@bddinfer:1]], that number is taken as the verbosity level
  (see below).

  The environment [env] is needed to access the builtin functions such
   as the integer operators.

  The known maps [tkn] and [mkn] are needed to access to the contracts
   of the WhyML functions called inside [e].

  The type [cty] is needed to get the preconditions of the execution
   of [e].

  The returned list contains pairs [(ei,ti)] where the [ei] are each
   of the loops occuring inside [e] and [ti] is the corresonding loop
   invariant generated.

  The inference does not support the full WhyML language. If any
  unsupported feature is met, this function will just return the empty
  list. The reason should be inspected using [register_hook] function
  below, that should be called before.

 *)

val verbose_level : int ref
(** Controls informative messages that will be printed in standard
    output during execution of [infer_loop_invs]. default is 0: no
    messages, 1 prints inferred invariants and domains for loops.  2
    also prints inferred states before any statement annotated with an
    attribute starting with "bddinfer:".  3 will print the WhyML
    expressions on which inference of invariants is attempted,
    together with the translated "Why1" code. level 4 corresponds the
    more debugging messages that should be used only during
    development. *)

type domains = Abstract.domain Term.Mvs.t

type engine_report = {
  engine_error : (string * string) option;
  (* An exception possibly raised by the engine *)
  engine_running_time : float;
  (* The cpu time spent in inference *)
  engine_num_bool_vars : int;
  (* The number of Boolean variables used *)
  engine_invariants_and_domains : (Term.term * domains) Wstdlib.Mstr.t;
  (* The invariants that were produced *)
  engine_subreport : Infer.interp_report option;
  (* The low-level report of inference sub-engine *)
}

val report : verbosity:int -> engine_report -> unit
(** prints the report on standard output. The parameter [verbosity]
   controls which information is reported. It should not be confused
   with the global parameter [verbose_level]. The level 0 corresponds
   to printing only the generated invariants and the domains. The
   level 1 adds the information provided by [Infer.report] *)

val register_hook : (engine_report -> unit) -> unit
(** registers a function to be applied on the report *)
