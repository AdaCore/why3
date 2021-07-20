
(** {1 Basic definitions for Pinterp and Rac}

{[
          Pinterp_core
             /    \
            /      \
       Pinterp     Rac
            \      /
             \    /
            Check_ce
]}
  *)

(** {2 Basic definitions for Pinterp} *)

(** {3 Values} *)

(** (Mutable) values used in [Pinterp] *)
module rec Value : sig

  type float_mode = Mlmpfr_wrapper.mpfr_rnd_t

  type big_float = Mlmpfr_wrapper.mpfr_float

  type value = private {
    v_desc: value_desc;
    v_ty: Ty.ty;
  }
  and field
  and value_desc =
    | Vconstr of Expr.rsymbol * Expr.rsymbol list * field list
    (** A record or variant *)
    | Vnum of BigInt.t
    (** Any integer number *)
    | Vreal of Big_real.real
    | Vfloat_mode of float_mode
    | Vfloat of big_float
    | Vstring of string
    | Vbool of bool
    | Vproj of Term.lsymbol * value
    (** [Vproj (ls, v)] is af model projection, i.e.
        {!const:Model_parser.model_value.Proj} originating from an meta
        [model_projection]). The only valid operation is applying [ls],
        resulting in [v]. *)
    | Varray of value array
    (** An array created in code *)
    | Vpurefun of Ty.ty (* type of the keys *) * value Mv.t * value
    (** A pure, unary function is used to represent arrays from the prover
        model/candidate counterexample. See {!type:Model_parser.model_array}. *)
    | Vfun of value Term.Mvs.t (* closure values *) * Term.vsymbol * Expr.expr
    (** A function value *)
    | Vterm of Term.term
    (** The result of a pure expression *)
    | Vundefined
    (** An undefined value; unreducible *)
end

(** A map with values as keys *)
and Mv : Extmap.S with type key = Value.value

open Value

val print_value : Format.formatter -> value -> unit

val compare_values : value -> value -> int

(** {4 Accessors} *)

val v_ty : value -> Ty.ty
val v_desc : value -> value_desc

val field : value -> field
val field_get : field -> value
val field_set : field -> value -> unit

(** {4 Constructors}

    Non defensive API for building [value]s: there are no checks that
    [ity] is compatible with the [value] being built. *)

(* TODO: make it defensive? *)
val bool_value : bool -> value
val int_value : BigInt.t -> value
val string_value : string -> value
val num_value : Ity.ity -> BigInt.t -> value
val float_value : Ity.ity -> big_float -> value
val real_value : Big_real.real -> value

val constr_value : Ity.ity -> Expr.rsymbol -> Expr.rsymbol list -> value list -> value
val purefun_value : result_ity:Ity.ity -> arg_ity:Ity.ity -> value Mv.t -> value -> value
val unit_value : value
val undefined_value : Ity.ity -> value

val range_value : Ity.ity -> BigInt.t -> value option
(** Returns a range value, or [None] if the value is outside the range. *)

val proj_value : Ity.ity -> Term.lsymbol -> value -> value option
(** Returns a range value, or [None] if the type is a range, the value is
   outside. *)

(** {4 Snapshots}

    Values are mutable, the following functions make deep-copies. *)

val snapshot : value -> value

val snapshot_vsenv : value Term.Mvs.t -> value Term.Mvs.t

val snapshot_oldies :
  Ity.pvsymbol Ity.Mpv.t -> value Term.Mvs.t -> Value.value Term.Mvs.t
(** Used for checking function variants *)

(** {3 Interpreter log} *)

module Log : sig
  type exec_mode = Exec_giant_steps | Exec_normal

  type value_or_invalid = Value of value | Invalid

  type log_entry_desc = private
    | Val_assumed of (Ident.ident * value)
    | Res_assumed of (Expr.rsymbol option * value)
    | Const_init of Ident.ident
    | Exec_call of (Expr.rsymbol option * value Term.Mvs.t  * exec_mode)
    | Exec_pure of (Term.lsymbol * exec_mode)
    | Exec_any of (Expr.rsymbol option * value Term.Mvs.t)
    | Iter_loop of exec_mode
    | Exec_main of (Expr.rsymbol * value Term.Mvs.t * value_or_invalid Expr.Mrs.t)
    | Exec_stucked of (string * value Ident.Mid.t)
    | Exec_failed of (string * value Ident.Mid.t)
    | Exec_ended

  type log_entry = private {
    log_desc : log_entry_desc;
    log_loc  : Loc.position option;
  }

  type exec_log
  type log_uc

  val log_val : log_uc -> Ident.ident -> value -> Loc.position option -> unit
  val log_const : log_uc -> Ident.ident -> Loc.position option -> unit
  val log_call : log_uc -> Expr.rsymbol option -> value Term.Mvs.t ->
                 exec_mode -> Loc.position option -> unit
  val log_pure_call : log_uc -> Term.lsymbol -> exec_mode ->
                      Loc.position option -> unit
  val log_any_call : log_uc -> Expr.rsymbol option -> value Term.Mvs.t
                     -> Loc.position option -> unit
  val log_iter_loop : log_uc -> exec_mode -> Loc.position option -> unit
  val log_exec_main : log_uc -> Expr.rsymbol -> value Term.Mvs.t -> value Lazy.t Expr.Mrs.t ->
                      Loc.position option -> unit
  val log_failed : log_uc -> string -> value Ident.Mid.t ->
                   Loc.position option -> unit
  val log_stucked : log_uc -> string -> value Ident.Mid.t ->
                    Loc.position option -> unit
  val log_exec_ended : log_uc -> Loc.position option -> unit
  val empty_log_uc : unit -> log_uc
  val empty_log : exec_log
  val get_log : log_uc -> exec_log (** Get the log *)
  val flush_log : log_uc -> exec_log (** Get the log and empty the log_uc *)
  val sort_log_by_loc : exec_log -> log_entry list Wstdlib.Mint.t Wstdlib.Mstr.t
  val print_log : ?verb_lvl:int -> json:bool -> exec_log Pp.pp
end

(** {3 Premises} *)

type premises
(** The premises during RAC, i.e. the assertions in the execution context that
    have been checked. The premises are a stack of scopes, where a scope contains
    a set of checks. *)

val with_push_premises : premises -> (unit -> 'a) -> 'a
(** [with_push_premises p f] calls [f] in a new scope of premises in [p]. The
    scope is removed again after [with_push_premises] ends. *)

val add_premises : Term.term list -> premises -> unit
(** [add_premises ts p] adds the terms ts to the premises. *)

val fold_premises : ('a -> Term.term -> 'a) -> premises -> 'a -> 'a
(** Fold the terms in the premises. *)

(** {3 The execution environment} *)

type env = {
  why_env  : Env.env;
  pmodule  : Pmodule.pmodule;
  funenv   : (Expr.cexp * Expr.rec_defn list option) Expr.Mrs.t;
  (** local functions *)
  vsenv    : value Term.Mvs.t;
  (** local variables *)
  rsenv    : value Lazy.t Expr.Mrs.t;
  (** global variables *)
  premises : premises;
  log_uc   : Log.log_uc;
}
(** The parts of the execution environment in {!Pinterp} which are relevant for
   {!Rac}. *)

val mk_empty_env : Env.env -> Pmodule.pmodule -> env

val get_vs : env -> Term.Mvs.key -> Value.value

val get_pvs : env -> Ity.pvsymbol -> Value.value

val bind_vs : Term.Mvs.key -> value -> env -> env

val bind_rs : Expr.Mrs.key -> value Lazy.t -> env -> env

val bind_pvs : ?register:(Ident.ident -> value -> unit) ->
  Ity.pvsymbol -> value -> env -> env

val multibind_pvs : ?register:(Ident.ident -> value -> unit) ->
  Ity.pvsymbol list -> value list -> env -> env

(** {3 Exception for incomplete execution (and RAC)} *)

exception Incomplete of string
(** Raised when the execution in [Pinterp] is incomplete (not implemented or not
    possible), or when a check cannot be decided during the RAC. *)

(** @raise Incomplete with the formatted string as reason *)
val incomplete : ('a, Format.formatter, unit, 'b) format4 -> 'a

(** {3 Term of value} *)

val term_of_value : ?ty_mt:Ty.ty Ty.Mtv.t -> env ->
  (Term.vsymbol * Term.term) list -> Value.value ->
  (Term.vsymbol * Term.term) list * Term.term
(** Convert a value into a term. The first component of the result are
    additional bindings from closures. *)

(** {3 Compute term} *)

type compute_term = env -> Term.term -> Term.term
(** Reduce a term (for RAC or for computing ghost expressions). An
    implementation based on Why3 transformations is available at
    {!Rac.Why.mk_compute_term} and {!Rac.Why.mk_compute_term_lit}. *)

val compute_term_dummy : compute_term
(** An implementation that is just the identity, i.e. it does {e not} reduce the
    term. *)

(** {4 Default values} *)

val default_value_of_type : env -> Ity.ity -> value
(** Return the default value of the given type. *)

(** {3 Oracles} *)

type oracle =
  ?loc:Loc.position -> env -> (Ity.ity -> Value.value -> unit) ->
    Ident.ident -> Ity.ity -> Value.value option
(** An oracle provides values during execution in {!Pinterp} for program
    parameters and during giant steps.

    See {!Check_ce.oracle_of_model} for an implementation.

    @raise Stuck if the value or any component is invalid (e.g., a range
    value outside its bounds). *)

val oracle_dummy : oracle
(** Always returns in [None]. *)

(** {3 Log functions} *)

val register_used_value : env -> Loc.position option -> Ident.ident -> value -> unit

val register_res_value : env -> Loc.position -> Expr.rsymbol option -> value -> unit

val register_const_init : env -> Loc.position option -> Ident.ident -> unit

val register_call : env -> Loc.position option -> Expr.rsymbol option -> value Term.Mvs.t -> Log.exec_mode -> unit

val register_pure_call : env -> Loc.position option -> Term.lsymbol -> Log.exec_mode -> unit

val register_any_call : env -> Loc.position option -> Expr.rsymbol option -> value Term.Mvs.t -> unit

val register_iter_loop : env -> Loc.position option -> Log.exec_mode -> unit

val register_exec_main : env -> Expr.rsymbol -> unit

val register_failure : env -> Loc.position option -> string -> value Ident.Mid.t -> unit

val register_stucked : env -> Loc.position option -> string -> value Ident.Mid.t -> unit

val register_ended : env -> Loc.position option -> unit

(** {2 Basic definitions for RAC}

    Interfaces for runtime-assertion checking (RAC), implemented in module
    {!module:Rac}. *)

(** {3 The contradiction context} *)

type cntr_ctx = {
  attr     : Ident.attribute; (** Some attribute [Vc.expl_*] *)
  desc     : string option;
  loc      : Loc.position option;
  attrs    : Ident.Sattr.t;
  cntr_env : env;
}
(** A contradiction context carries all necessary information
    about a contradiction (with snapshot'ed values). *)

val mk_cntr_ctx :
  env -> ?loc:Loc.position -> ?attrs:Ident.Sattr.t -> ?desc:string ->
  Ident.attribute -> cntr_ctx
(** Construct a new {!cntr_ctx} with a snapshot of the environment [env]. *)

val describe_cntr_ctx : cntr_ctx -> string
val report_cntr_title : (cntr_ctx * string) Pp.pp
val report_cntr_head : (cntr_ctx * string * Term.term) Pp.pp
val report_cntr_body : (cntr_ctx * Term.term) Pp.pp
val report_cntr : (cntr_ctx * string * Term.term) Pp.pp

(** {3 Exceptions for failures in RAC} *)

exception Fail of cntr_ctx * Term.term
(** Invalid assertions raise the exception [Fail] *)

exception Stuck of cntr_ctx * Loc.position option * string
(** Invalid assumptions raise the exception [Stuck] *)

val stuck : ?loc:Loc.position -> cntr_ctx ->
  ('a, Format.formatter, unit, 'b) format4 -> 'a
(** Raise an exception {!Stuck} with a formatted string. *)

val stuck_for_fail : ?loc:Loc.position -> cntr_ctx -> Term.term -> 'a
(** Raise an exception {!Stuck} and register in the log for a [Fail (cntr_ctx,
    t)]. *)


(** {3 A RAC engine} *)

type check_term =
  ?vsenv:(Term.vsymbol * Term.term) list -> cntr_ctx -> Term.term -> unit
(** A function of type [check_term] comprises a RAC engine.

    @raise Fail when the term is invalid
    @raise Incomplete when the validity of the term cannot be decided. *)

val check_term_dummy : check_term
(** Always raise {!Incomplete} *)

type rac = {
  check_term        : check_term;
  ignore_incomplete : bool;
}
(** RAC is defined by a single function {!type:check_term}. When the flag
    [ignore_incomplete] is true, the functions under "RAC checks"
    ignore incomplete checks and output only a warning. *)

val mk_rac : ?ignore_incomplete:bool -> check_term -> rac
(** Plain constructor for {!rac}, [ignore_incomplete] is false by default. *)

val rac_dummy : rac
(** Dummy RAC that always raises [Failure]. *)

(** {3 RAC checks}

    The following functions use {!recfield:rac.check_term} to check assertions
    and assumptions. If {!rac.ignore_incomplete} is true, incomplete checks do
    not raise an exception {!Incomplete} but trigger only a warning. *)

val check_term :
  rac -> ?vsenv:(Term.vsymbol * Term.term) list -> cntr_ctx -> Term.term -> unit
(** @raise Fail when the term is invalid *)

val check_assume_term : rac -> cntr_ctx -> Term.term -> unit
(** @raise Stuck when the term is invalid. *)

val check_terms : rac -> cntr_ctx -> Term.term list -> unit
(** @raise Fail when one of the terms is invalid *)

val check_assume_terms : rac -> cntr_ctx -> Term.term list -> unit
(** @raise Stuck when one of the terms is invalid. *)

val check_post : rac -> cntr_ctx -> Value.value -> Ity.post -> unit
(** Check a post-condition [t] by binding the result variable to
    the term [vt] representing the result value.

    @raise Fail when the postcondition is invalid for the given value *)

val check_posts : rac -> cntr_ctx -> Value.value -> Ity.post list -> unit
(** @raise Fail when one of the postconditions is invalid for the given value *)

val check_assume_posts : rac -> cntr_ctx -> Value.value -> Ity.post list -> unit
(** @raise Stuck when one of the postconditions is invalid for the given return
    value. *)

val check_type_invs : rac -> ?loc:Loc.position -> env -> Ity.ity -> Value.value -> unit
(** @raise Fail when one of the type invariant of the type is invalid for the
    given value *)

val check_assume_type_invs : rac -> ?loc:Loc.position ->
  env -> Ity.ity -> Value.value -> unit
(** @raise Stuck when the type invariant for the given type is invalid for the
    given value. *)

val oldify_varl : env -> (Term.term * Term.lsymbol option) list ->
  (Term.term * Term.lsymbol option) list * Value.value Term.Mvs.t
(** Prepare a variant for later call with {!check_variant}. *)

val check_variant : rac -> Ident.Sattr.elt -> Loc.position option -> env ->
  (Term.term * Term.lsymbol option) list * Value.value Term.Mvs.t ->
  (Term.term * Term.lsymbol option) list -> unit
(** @raise Fail when the variant is invalid. *)

(** {2 Auxilaries} *)

val t_undefined : Ty.ty -> Term.term

val ty_app_arg : Ty.tysymbol -> int -> Ty.ty -> Ty.ty
(** [ty_app_arg ts n ty] returns the [n]-th argument of the type application of
    [ts] in [ty]. Fails if [ty] is not an type application of [ts] *)

val ity_components : Ity.ity -> Ity.itysymbol * Ity.ity list * Ity.ity list
(** Gets the components of an ity *)

val is_range_ty : Ty.ty -> bool
(** Checks if the argument is a range type *)

val debug_array_as_update_chains_not_epsilon : Debug.flag
(** The debug parameter ["rac-array-as-update-chains"], a parameter for the
    conversion of arrays to terms in RAC. Normally, an array [a] of length [n] is
    converted to:

    [(epsilon v. v.length = n /\ v[0] = a[0] /\ ... /\ a[n-1] = a[n-1])].

    As an update chain, it is instead converted into a formula:

    [(make n undefined)[0 <- a[0]]... [n-1 <- a[n-1]]]. *)

(**/**)

val pp_bindings :
?sep:unit Pp.pp -> ?pair_sep:unit Pp.pp -> ?delims:unit Pp.pp * unit Pp.pp ->
'a Pp.pp -> 'b Pp.pp -> ('a * 'b) list Pp.pp

val pp_env : 'a Pp.pp -> 'b Pp.pp -> Format.formatter -> ('a * 'b) list -> unit

val value : Ty.ty -> value_desc -> value
(** Untyped value constructor. *)
