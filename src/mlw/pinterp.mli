(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {2 Interpretation of Why3 programs} *)

open Wstdlib
open Ident
open Term
open Ity
open Expr

(** {2 Interpreter values} *)

type float_mode
type big_float

module rec Value : sig
  type value
  type field
  type value_desc = private
    | Vconstr of rsymbol * rsymbol list * field list
    | Vnum of BigInt.t
    | Vreal of Big_real.real
    | Vfloat_mode of float_mode
    | Vfloat of big_float
    | Vstring of string
    | Vbool of bool
    | Vproj of lsymbol * value
    | Varray of value array
    | Vfun of value Mvs.t (* closure *) * vsymbol * expr
    | Vpurefun of Ty.ty (* keys *) * value Mv.t * value
    | Vterm of term (* ghost values *)
    | Vundefined
end
and Mv : Extmap.S with type key = Value.value

open Value

val v_ty : value -> Ty.ty
val v_desc : value -> value_desc

(** non defensive API for building [value]s: there are no checks that
   [ity] is compatible with the [value] being built *)
(* TODO: make it defensive? *)
val bool_value : bool -> value
val int_value : BigInt.t -> value
val string_value : string -> value

val constr_value : ity -> rsymbol -> rsymbol list -> value list -> value
val purefun_value : result_ity:ity -> arg_ity:ity -> value Mv.t -> value -> value
val unit_value : value
val undefined_value : ity -> value

val range_value : ity -> BigInt.t -> value
(** @raise CannotCompute when the value is not in the range *)

val proj_value : ity -> lsymbol -> value -> value
(** @raise CannotCompute when the lsymbol is the projection from a range type to
    int, and the value is an integer outside the bounds of the range *)

val field : value -> field
val field_get : field -> value
val field_set : field -> value -> unit

val default_value_of_type : Env.env -> Pdecl.known_map -> ity -> value

val print_value : Format.formatter -> value -> unit

(** {2 Interpreter log} *)

module type Log = sig
  type exec_kind = ExecAbstract | ExecConcrete

  type log_entry_desc = private
    | Val_assumed of (ident * value)
    | Const_init of ident
    | Exec_call of (rsymbol option * value Mvs.t  * exec_kind)
    | Exec_pure of (lsymbol * exec_kind)
    | Exec_any of (rsymbol option * value Mvs.t)
    | Iter_loop of exec_kind
    | Exec_main of (rsymbol * value Mvs.t * value Mrs.t)
    | Exec_stucked of (string * value Mid.t)
    | Exec_failed of (string * value Mid.t)
    | Exec_ended

  type log_entry = private {
    log_desc : log_entry_desc;
    log_loc  : Loc.position option;
  }

  type exec_log
  type log_uc

  val log_val : log_uc -> ident -> value -> Loc.position option -> unit
  val log_const : log_uc -> ident -> Loc.position option -> unit
  val log_call : log_uc -> rsymbol option -> value Mvs.t ->
                 exec_kind -> Loc.position option -> unit
  val log_pure_call : log_uc -> lsymbol -> exec_kind ->
                      Loc.position option -> unit
  val log_any_call : log_uc -> rsymbol option -> value Mvs.t
                     -> Loc.position option -> unit
  val log_iter_loop : log_uc -> exec_kind -> Loc.position option -> unit
  val log_exec_main : log_uc -> rsymbol -> value Mvs.t -> value Mrs.t ->
                      Loc.position option -> unit
  val log_failed : log_uc -> string -> value Mid.t ->
                   Loc.position option -> unit
  val log_stucked : log_uc -> string -> value Mid.t ->
                    Loc.position option -> unit
  val log_exec_ended : log_uc -> Loc.position option -> unit
  val empty_log_uc : unit -> log_uc
  val empty_log : exec_log
  val close_log : log_uc -> exec_log
  val sort_log_by_loc : exec_log -> log_entry list Mint.t Mstr.t
  val print_log : ?verb_lvl:int -> json:bool -> exec_log Pp.pp
end

module Log : Log

(** {2 Interpreter configuration} *)

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
  ?trans:Task.task Trans.tlist -> ?prover:rac_prover -> ?try_negate:bool ->
  unit -> rac_reduce_config

(** [rac_reduce_config_lit cnf env ?trans ?prover ?try_negate ()] configures the term
   reduction of RAC. [trans] is the name of a transformation (usually "compute_in_goal").
   [prover] is a prover string with optional, space-sparated time limit and memory limit.
   And with [~try_negate:true] the negated term is dispatched to the prover if the prover
   didn't return a result for the positive form. *)
val rac_reduce_config_lit :
  Whyconf.config -> Env.env -> ?trans:string -> ?prover:string -> ?try_negate:bool ->
  unit -> rac_reduce_config

type get_value =
  ?loc:Loc.position -> (ity -> value -> unit) -> ident -> ity -> value option
(** [get_value ?loc check id ity] tries to retrive a value from the oracle. The
    [check] is called on the value and every component.

    @raise CannotCompute if the value or any component is invalid (e.g., a range
    value outside its bounds). *)

type rac_config = private {
  do_rac : bool;
  (** check assertions *)
  rac_abstract : bool;
  (** interpret abstractly *)
  skip_cannot_compute : bool;
  (** continue when term cannot be checked *)
  rac_reduce : rac_reduce_config;
  (** configuration for reducing terms *)
  get_value : get_value;
  (** import values when they are needed *)
  log_uc : Log.log_uc;
  (** log *)
  timelimit : float option;
  (** Timeout in seconds for RAC execution *)
}

val rac_config :
  do_rac:bool ->
  abstract:bool ->
  ?skip_cannot_compute:bool ->
  ?reduce:rac_reduce_config ->
  ?get_value:get_value ->
  ?timelimit:float ->
  unit -> rac_config

(** {2 Interpreter environment and results} *)

(** Context for the interpreter *)
type env = private {
  pmodule : Pmodule.pmodule;
  funenv  : cexp Mrs.t;
  vsenv   : value Mvs.t;
  (** An environment of local variables *)
  rsenv   : value Mrs.t;
  (** An environment of global constants. The values are lazy and only forced
      when needed in the execution or in the task, to avoid the categorisation
      of counterexamples as bad, when they contain invalid values for irrelevant
      constants. *)
  premises: term list list ref list ref;
  (** The (stateful) set of checked terms in the execution context *)
  env     : Env.env;
  rac     : rac_config;
}

(** Result of the interpreter **)
type result = private
  | Normal of value
  | Excep of xsymbol * value
  | Irred of expr

(** Context of a contradiction during RAC *)
type cntr_ctx = private {
  c_attr: Ident.attribute; (** Related VC attribute *)
  c_desc: string option; (** Additional context *)
  c_loc: Loc.position option; (** Position if different than term *)
  c_vsenv: value Mvs.t;
  c_log_uc: Log.log_uc;
}

val describe_cntr_ctx : cntr_ctx -> string

exception CannotCompute of {reason: string}
(** raised when interpretation cannot continue due to unsupported
   feature *)
exception Contr of cntr_ctx * term
(** raised when a contradiction is detected during RAC. *)
exception RACStuck of env * Loc.position option
(** raised when an assumed property is not satisfied *)

(** {2 Interpreter} *)

val eval_global_fundef :
  rac_config ->
  Env.env ->
  Pmodule.pmodule ->
  (rsymbol * cexp) list ->
  expr ->
  result * value Mvs.t * value Mrs.t
(** [eval_global_fundef ~rac env pkm dkm rcl e] evaluates [e] and
   returns an evaluation result and a final variable environment (for
   both local and global variables).

   During RAC, annotations are first reduced by applying
   transformation [rac.rac_trans], and if the transformation doesn't
   return to a trivial formula ([true]/[false]), the prover
   [rac.rac_prover] is applied. Pure expressions and pure executions
   are reduced only using [rac.rac_trans]. When neither [ra.rac_trans]
   or [rac.rac_prover] are defined, RAC does not progress.

   raises [Contr _] if [rac.rac] and a an assertion was violated.

   raises [CannotCompute _] if some term could not be reduced due to
   unsopported feature.

   raises [Failure _] if there is an unsopported feature.

   raises [RACStuck _] if a property that should be assumed is not
   satisfied in the current enviroment. *)

val report_cntr : Format.formatter -> cntr_ctx * term -> unit
val report_cntr_body : Format.formatter -> cntr_ctx * term -> unit
(** Report a contradiction context and term *)

val report_eval_result :
  expr -> Format.formatter -> result * value Mvs.t * value Mrs.t -> unit
(** Report an evaluation result *)

val eval_rs : rac_config -> Env.env -> Pmodule.pmodule -> rsymbol -> result * env
(** [eval_rs ~rac env pm rs] evaluates the definition of [rs] and
   returns an evaluation result and a final environment.

  raises [Contr _] if [rac.rac] and a an assertion was violated.

  raises [CannotCompute _] if some term could not be reduced due to
   unsopported feature.

  raises [Failure _] if there is an unsopported feature.

  raises [RACStuck _] if a property that should be assumed is not
   satisfied in the current enviroment. *)

(**/**)

(** {2 Some auxilaries that are shared with module [Counterexample]} *)

(** [ty_app_arg ts n ty] returns the [n]-th argument of the type application of [ts] in
   [ty]. Fails if [ty] is not an type application of [ts] *)
val ty_app_arg : Ty.tysymbol -> int -> Ty.ty -> Ty.ty

(** Gets the components of an ity *)
val ity_components : Ity.ity -> Ity.itysymbol * Ity.ity list * Ity.ity list

(** Checks if the argument is a range type *)
val is_range_ty : Ty.ty -> bool

(** {2 Configuration by debug flags} *)

val debug_disable_builtin_mach : Debug.flag
(** Don't register builtins for machine-dependent modules under stdlib/mach. *)

val debug_array_as_update_chains_not_epsilon : Debug.flag
(** Parameter for the conversion of arrays to terms in RAC. Normally, an array
   [a] of length [n] is converted to [(epsilon v. v.length =n /\ v[0] = a[0] /\
   ... /\ a[n-1] = a[n-1])]. As an update chain, it is instead converted into a
   formula [(make n undefined)[0 <- a[0]]... [n-1 <- a[n-1]]] *)

val debug_rac_values : Debug.flag
(* print debug information about the values that are imported during
   interpretation *)
