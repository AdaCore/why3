(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Wstdlib
open Ident
open Term
open Ity
open Expr

(** {1 Interpreter values} *)

type value

module Mv : Map.S with type key = value

val v_ty : value -> Ty.ty

(* non defensive API for building value: there are no checks that ity
   is compatible with the value being built *)
(* TODO: make it defensive? *)
val int_value : string -> value
val range_value : ity -> string -> value
val string_value : string -> value
val bool_value : bool -> value
val constr_value : ity -> rsymbol -> value list -> value
val purefun_value : result_ity:ity -> arg_ity:ity -> value Mv.t -> value -> value

val default_value_of_type : Env.env -> Pdecl.known_map -> ity -> value

val print_value : Format.formatter -> value -> unit

(** {2 Interpreter log} *)

type exec_kind = ExecAbstract | ExecConcrete

type log_entry_desc = private
  | Val_assumed of (ident * value)
  (** values imported/assumed during interpretation *)
  | Exec_call of (rsymbol option * value Mvs.t  * exec_kind)
  (** executed function call or lambda if no rsymbol,
      arguments, execution type*)
  | Exec_pure of (lsymbol * exec_kind)
  (** executed pure function call *)
  | Exec_any of value
  (** execute any function call *)
  | Exec_loop of exec_kind
  (** execute loop *)
  | Exec_stucked of (string * value Mid.t)
  (** stucked execution information *)
  | Exec_failed of (string * value Mid.t)
  (** failed execution information *)
  | Exec_ended
  (** execution terminated normally *)

type log_entry = private {
    log_desc : log_entry_desc;
    log_loc  : Loc.position option;
}

type exec_log
type log_uc

val empty_log_uc : unit -> log_uc
val empty_log : exec_log
val close_log : log_uc -> exec_log
val sort_log_by_loc : exec_log -> log_entry list Mint.t Mstr.t
val print_log : json:bool -> exec_log Pp.pp

(** {3 Interpreter configuration} *)

val init_real : int * int * int -> unit
(** Give a precision on real computation. *)

type rac_prover
(** The configuration of the prover used for reducing terms in RAC *)

val rac_prover : command:string -> Driver.driver -> Call_provers.resource_limit -> rac_prover

type rac_reduce_config
(** The configuration for RAC, including (optionally) a transformation for reducing terms
   (usually: compute_in_goal), and a prover to be used if the transformation does not
   yield a truth value. When neither transformation nor prover are defined, then RAC does
   not progress. *)

val rac_reduce_config :
  ?trans:Task.task Trans.tlist ->
  ?prover:rac_prover ->
  unit -> rac_reduce_config

val rac_reduce_config_lit :
  Whyconf.config ->
  Env.env ->
  Call_provers.rac_reduce_config_lit ->
  rac_reduce_config

type rac_config = private {
  do_rac              : bool;
  rac_abstract        : bool;
  skip_cannot_compute : bool; (* skip when it cannot compute, if possible*)
  rac_reduce          : rac_reduce_config;
  get_value           : ?name:string -> ?loc:Loc.position ->
                        ity -> value option;
  log_uc              : log_uc;
}

val rac_config :
  do_rac:bool ->
  abstract:bool ->
  ?skip_cannot_compute:bool ->
  ?reduce:rac_reduce_config ->
  ?get_value:(?name:string -> ?loc:Loc.position -> ity -> value option) ->
  unit -> rac_config

(** {4 Interpreter environment and results} *)

(** Context for the interpreter *)
type env = private {
  mod_known   : Pdecl.known_map;
  th_known    : Decl.known_map;
  funenv      : cexp Mrs.t;
  vsenv       : value Mvs.t;
  rsenv       : value Mrs.t; (* global constants *)
  env         : Env.env;
  rac         : rac_config;
}

(** Result of the interpreter **)
type result = private
  | Normal of value
  | Excep of xsymbol * value
  | Irred of expr
  | Fun of rsymbol * pvsymbol list * int

(** Context of a contradiction during RAC *)
type cntr_ctx = private {
  c_desc: string;
  c_trigger_loc: Loc.position option;
  c_env: env
}

exception CannotCompute of {reason: string}
(** raised when interpretation cannot continue due to unsupported
   feature *)
exception Contr of cntr_ctx * term
(** raised when a contradiction is detected during RAC. *)
exception RACStuck of env * Loc.position option
(** raised when an assumed property is not satisfied *)

(** {5 Interpreter} *)

val eval_global_fundef :
  rac_config ->
  Env.env ->
  Pdecl.known_map ->
  Decl.known_map ->
  (rsymbol * cexp) list ->
  expr ->
  result * value Mvs.t * value Mrs.t
(* TODO update comment *)
(** [eval_global_fundef ~rac env disp_ctx known def] evaluates a function definition and
   returns an evaluation result and a final variable environment.

    During RAC, annotations are first reduced by applying transformation [rac_trans], and
   if the transformation doesn't return to a trivial formula ([true]/[false]), the prover
   [rac_prover] is applied. Pure expressions and pure executions are reduced only using
   [rac_trans]. When neither [rac_trans] or [rac_prover] are defined, RAC does not
    progress.

    @raise Contr RAC is enabled and a contradiction was found *)

val report_cntr : Format.formatter -> cntr_ctx * term -> unit
val report_cntr_body : Format.formatter -> cntr_ctx * term -> unit
(** Report a contradiction context and term *)

val report_eval_result :
  expr -> Format.formatter -> result * value Mvs.t * value Mrs.t -> unit
(** Report an evaluation result *)

val eval_rs : rac_config -> Env.env -> Pmodule.pmodule -> rsymbol -> result * env
(** [eval_rs rac_config env km pm rs] interprets [rs] *)
