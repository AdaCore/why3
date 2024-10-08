(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 WhyML Program Interpreter} *)

open Term
open Expr
open Pinterp_core
open Value

(** {2 Interpreter configuration} *)

val init_real : int * int * int -> unit
(** Give a precision on real computation. *)

(** {2 Execution context} *)

(** The execution context *)
type ctx

val mk_empty_env : Env.env -> Pmodule.pmodule -> Pinterp_core.env
(** {!Pinterp_core.env} repeated here for convenience. *)

val mk_rac : ?ignore_incomplete:bool -> check_term -> rac
(** {!Pinterp_core.mk_rac} repeated here for convenience. *)

val mk_ctx :
  Pinterp_core.env ->
  limits:Call_provers.resource_limits ->
  ?giant_steps:bool ->
  ?do_rac:bool ->
  ?rac:rac ->
  ?oracle:Pinterp_core.oracle ->
  ?compute_term:(Pinterp_core.env -> Term.term -> Term.term) ->
  unit -> ctx
(** Create an execution context.

    @param env variable environments and others
    @param timelimit timeout in seconds for execution (disabled by default)
    @param steplimit steplimit for execution (disabled by default)
    @param giant_steps execute function calls and loops with giant steps ([false] by default)
    @param do_rac enable runtime-assertion checking (RAC) ([false] by default)
    @param rac the RAC engine ({!Pinterp_core.rac_dummy} by default)
    @param oracle for values when they are needed (program parameters and giant steps
    @param compute_term callback to compute terms in pure expressions *)

val get_env : ctx -> env
(** Return the environment of an execution context. *)

val get_do_rac : ctx -> bool
(** Return true if RAC is enabled in the execution context. *)

val get_rac : ctx -> rac
(** Return the RAC engine of the execution context. *)

val get_giant_steps : ctx -> bool
(** Return true if the execution context is configured with giant steps. *)

(** {2 Execution results} *)

(** An execution may terminate normally, with an exception, or with an
     irreducible expression. *)
type result =
  | Normal of Value.value
  | Excep of Ity.xsymbol * value
  | Irred of Expr.expr

val print_logic_result : result Pp.pp

(** {2 Execution functions} *)

val exec_rs : ctx -> rsymbol -> result * ctx
(** [eval_rs ~rac env pm rs] evaluates the definition of [rs] and returns an
    evaluation result and a final environment.

    @raise Fail if an assertion was violated during RAC

    @raise Stuck if an assumption was violated during RAC or a giant step.

    @raise Incomplete if there is an unsopported feature or some term could not be
    reduced. *)

val exec_global_fundef :
  ctx -> (rsymbol * cexp) list -> rec_defn list option -> expr ->
  result * value Mvs.t * value Lazy.t Mrs.t
(** [eval_global_fundef ~rac env pkm dkm rcl rdl e] evaluates [e] and returns an
    evaluation result and a final variable environment (for both local and global
    variables).

    Same exceptions as [exec_global_fundef]. *)

(** {2 Reporting, i.e. pretty printing} *)

val report_eval_result :
  expr -> Format.formatter -> result * value Mvs.t * value Lazy.t Mrs.t -> unit
(** Report an evaluation result *)

val report_cntr : (cntr_ctx * Term.term) Pp.pp

(**/**)

(** {2 Configuration by debug flags} *)

val debug_disable_builtin_mach : Debug.flag
(** Don't register builtins for machine-dependent modules under stdlib/mach. *)

val debug_rac_values : Debug.flag
(* print debug information about the values that are imported during
   interpretation *)
