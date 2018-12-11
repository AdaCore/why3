(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Terms and Formulas *)

open Ident
open Ty

(** {1 Terms and Formulas} *)

(** {2 Variable symbols} *)

type vsymbol = private {
  vs_name : ident;
  vs_ty   : ty;
}

module Mvs : Extmap.S with type key = vsymbol
module Svs : Extset.S with module M = Mvs
module Hvs : Exthtbl.S with type key = vsymbol
module Wvs : Weakhtbl.S with type key = vsymbol

val vs_compare : vsymbol -> vsymbol -> int
val vs_equal : vsymbol -> vsymbol -> bool
val vs_hash : vsymbol -> int

val create_vsymbol : preid -> ty -> vsymbol

(** {2 Function and predicate symbols} *)

type lsymbol = private {
  ls_name   : ident;
  ls_args   : ty list;
  ls_value  : ty option;
  ls_constr : int;
}

module Mls : Extmap.S with type key = lsymbol
module Sls : Extset.S with module M = Mls
module Hls : Exthtbl.S with type key = lsymbol
module Wls : Weakhtbl.S with type key = lsymbol

val ls_compare : lsymbol -> lsymbol -> int
val ls_equal : lsymbol -> lsymbol -> bool
val ls_hash : lsymbol -> int

val create_lsymbol : ?constr:int -> preid -> ty list -> ty option -> lsymbol

val create_fsymbol : ?constr:int -> preid -> ty list -> ty -> lsymbol
(** ~constr is the number of constructors of the type in which the
   symbol is a constructor otherwise it must be the default 0. *)

val create_psymbol : preid -> ty list -> lsymbol

val ls_ty_freevars : lsymbol -> Stv.t

(** {2 Exceptions} *)

exception EmptyCase
exception DuplicateVar of vsymbol
exception UncoveredVar of vsymbol
exception BadArity of lsymbol * int
exception FunctionSymbolExpected of lsymbol
exception PredicateSymbolExpected of lsymbol
exception ConstructorExpected of lsymbol
exception InvalidIntegerLiteralType of ty
exception InvalidRealLiteralType of ty

(** {2 Patterns} *)

type pattern = private {
  pat_node : pattern_node;
  pat_vars : Svs.t;
  pat_ty   : ty;
}

and pattern_node =
  | Pwild
  | Pvar of vsymbol
  | Papp of lsymbol * pattern list
  | Por  of pattern * pattern
  | Pas  of pattern * vsymbol

(** Smart constructors for patterns *)

val pat_wild : ty -> pattern
val pat_var : vsymbol -> pattern
val pat_app : lsymbol -> pattern list -> ty -> pattern
val pat_or  : pattern -> pattern -> pattern
val pat_as  : pattern -> vsymbol -> pattern

(** Generic traversal functions *)

val pat_map : (pattern -> pattern) -> pattern -> pattern
val pat_fold : ('a -> pattern -> 'a) -> 'a -> pattern -> 'a
val pat_all : (pattern -> bool) -> pattern -> bool
val pat_any : (pattern -> bool) -> pattern -> bool

(** {2 Terms and Formulas} *)

type quant =
  | Tforall
  | Texists

type binop =
  | Tand
  | Tor
  | Timplies
  | Tiff

type term = private {
  t_node  : term_node;
  t_ty    : ty option;
  t_attrs : Sattr.t;
  t_loc   : Loc.position option;
}

and term_node =
  | Tvar of vsymbol
  | Tconst of Number.constant
  | Tapp of lsymbol * term list
  | Tif of term * term * term
  | Tlet of term * term_bound
  | Tcase of term * term_branch list
  | Teps of term_bound
  | Tquant of quant * term_quant
  | Tbinop of binop * term * term
  | Tnot of term
  | Ttrue
  | Tfalse

and term_bound
and term_branch
and term_quant

and trigger = term list list

module Mterm : Extmap.S with type key = term
module Sterm : Extset.S with module M = Mterm
module Hterm : Exthtbl.S with type key = term

(** {2 Term equality modulo alpha-equivalence and location} *)

val t_compare : term -> term -> int
val t_equal : term -> term -> bool
val t_hash : term -> int
(* Equality modulo attributes and triggers *)
val t_equal_nt_na : term -> term -> bool
module Hterm_nt_na : Exthtbl.S with type key = term

(** {2 Bindings} *)

(** close bindings *)

val t_close_bound : vsymbol -> term -> term_bound
val t_close_branch : pattern -> term -> term_branch
val t_close_quant : vsymbol list -> trigger -> term -> term_quant

(** open bindings *)

val t_open_bound : term_bound -> vsymbol * term
val t_open_branch : term_branch -> pattern * term
val t_open_quant : term_quant -> vsymbol list * trigger * term

val t_open_bound_with : term -> term_bound -> term
(** [t_open_bound_with t tb] opens the binding [tb] and immediately
    replaces the corresponding bound variable with [t] *)

val t_clone_bound_id : term_bound -> preid

(** open bindings with optimized closing callbacks *)

val t_open_bound_cb :
  term_bound -> vsymbol * term * (vsymbol -> term -> term_bound)

val t_open_branch_cb :
  term_branch -> pattern * term * (pattern -> term -> term_branch)

val t_open_quant_cb :
  term_quant -> vsymbol list * trigger * term *
              (vsymbol list -> trigger -> term -> term_quant)

(** {2 Type checking} *)

exception TermExpected of term
exception FmlaExpected of term

val t_type : term -> ty
(** [t_type t] checks that [t] is value-typed and returns its type *)

val t_prop : term -> term
(** [t_prop t] checks that [t] is prop-typed and returns [t] *)

val t_ty_check : term -> ty option -> unit
(** [t_ty_check t ty] checks that the type of [t] is [ty] *)

(** {2 Smart constructors for terms and formulas} *)

val t_app  : lsymbol -> term list -> ty option -> term
val fs_app : lsymbol -> term list -> ty -> term
val ps_app : lsymbol -> term list -> term

val t_app_infer : lsymbol -> term list -> term
val ls_arg_inst : lsymbol -> term list -> ty Mtv.t
val ls_app_inst : lsymbol -> term list -> ty option -> ty Mtv.t

val check_literal : Number.constant -> ty -> unit

val t_var : vsymbol -> term
val t_const : Number.constant -> ty -> term
val t_if : term -> term -> term -> term
val t_let : term -> term_bound -> term
val t_case : term -> term_branch list -> term
val t_eps : term_bound -> term
val t_quant : quant -> term_quant -> term
val t_forall : term_quant -> term
val t_exists : term_quant -> term
val t_binary : binop -> term -> term -> term
val t_and : term -> term -> term
val t_or : term -> term -> term
val t_implies : term -> term -> term
val t_iff : term -> term -> term
val t_not : term -> term
val t_true : term
val t_false : term

val t_nat_const : int -> term
(** [t_nat_const n] builds the constant integer term [n],
    n must be non-negative *)
val t_bigint_const : BigInt.t -> term

val stop_split : attribute
val asym_split : attribute

val t_and_l : term list -> term
val t_or_l : term list -> term

val t_and_asym : term -> term -> term
val t_or_asym : term -> term -> term

val t_and_asym_l : term list -> term
val t_or_asym_l : term list -> term

val t_let_close : vsymbol -> term -> term -> term
val t_eps_close : vsymbol -> term -> term
val t_case_close : term -> (pattern * term) list -> term
val t_quant_close : quant -> vsymbol list -> trigger -> term -> term
val t_forall_close : vsymbol list -> trigger -> term -> term
val t_exists_close : vsymbol list -> trigger -> term -> term

val t_attr_set : ?loc:Loc.position -> Sattr.t -> term -> term
val t_attr_add : attribute -> term -> term
val t_attr_remove : attribute -> term -> term
val t_attr_copy : term -> term -> term

(** Constructors with propositional simplification *)

val t_if_simp : term -> term -> term -> term
val t_let_simp : term -> term_bound -> term
val t_case_simp : term -> term_branch list -> term
val t_quant_simp : quant -> term_quant -> term
val t_forall_simp : term_quant -> term
val t_exists_simp : term_quant -> term
val t_binary_simp : binop -> term -> term -> term
val t_and_simp : term -> term -> term
val t_and_simp_l : term list -> term
val t_or_simp : term -> term -> term
val t_or_simp_l : term list -> term
val t_implies_simp : term -> term -> term
val t_iff_simp : term -> term -> term
val t_not_simp : term -> term

val t_and_asym_simp : term -> term -> term
val t_and_asym_simp_l : term list -> term
val t_or_asym_simp : term -> term -> term
val t_or_asym_simp_l : term list -> term

val t_let_close_simp : vsymbol -> term -> term -> term
val t_case_close_simp : term -> (pattern * term) list -> term
val t_quant_close_simp : quant -> vsymbol list -> trigger -> term -> term
val t_forall_close_simp : vsymbol list -> trigger -> term -> term
val t_exists_close_simp : vsymbol list -> trigger -> term -> term

val t_forall_close_merge : vsymbol list -> term -> term
val t_exists_close_merge : vsymbol list -> term -> term
(** [t_forall_close_merge vs f] puts a universal quantifier over [f];
    merges variable lists if [f] is already universally quantified;
    reuses triggers of [f], if any, otherwise puts no triggers. *)

(** {2 Built-in symbols} *)

val ps_equ : lsymbol
(** equality predicate *)

val t_equ : term -> term -> term
val t_neq : term -> term -> term

val t_equ_simp : term -> term -> term
val t_neq_simp : term -> term -> term

val fs_bool_true  : lsymbol
val fs_bool_false : lsymbol

val t_bool_true  : term
val t_bool_false : term

val fs_tuple : int -> lsymbol   (* n-tuple *)
val t_tuple : term list -> term

val is_fs_tuple : lsymbol -> bool
val is_fs_tuple_id : ident -> int option

val fs_func_app : lsymbol  (* higher-order application symbol *)

val t_func_app : term -> term -> term  (* value-typed application *)
val t_pred_app : term -> term -> term  (* prop-typed application *)

val t_func_app_l : term -> term list -> term  (* value-typed application *)
val t_pred_app_l : term -> term list -> term  (* prop-typed application *)

(** {2 Lambda-term manipulation} *)

val t_lambda : vsymbol list -> trigger -> term -> term
(** [t_lambda vl tr e] produces a term [eps f. (forall vl [tr]. f\@vl = e)]
    or [eps f. (forall vl [tr]. f\@vl = True <-> e] if [e] is prop-typed.
    If [vl] is empty, [t_lambda] returns [e] or [if e then True else False],
    if [e] is prop-typed. *)

val t_open_lambda : term -> vsymbol list * trigger * term
(** [t_open_lambda t] returns a triple [(vl,tr,e)], such that [t] is equal
    to [t_lambda vl tr e]. If [t] is not a lambda-term, then [vl] is empty,
    [tr] is empty, and [e] is [t]. The term [e] may be prop-typed. *)

val t_open_lambda_cb : term -> vsymbol list * trigger * term *
                             (vsymbol list -> trigger -> term -> term)
(** the same as [t_open_lambda] but returns additionally an instance of
    [t_lambda] that restores the original term if applied to the physically
    same arguments. Should be used in mapping functions. *)

val t_is_lambda : term -> bool
(** [t_is_lambda t] returns [true] if [t] is a lambda-term. Do not use
    this function if you call [t_open_lambda] afterwards. Internally,
    [t_is_lambda] opens binders itself, so you will pay twice the price.
    It is better to optimistically call [t_open_lambda] on any [Teps],
    and handle the generic case if an empty argument list is returned. *)

val t_closure : lsymbol -> ty list -> ty option -> term
(** [t_closure ls tyl oty] returns a type-instantiated lambda-term
    [\xx:tyl.(ls xx : oty)], or [ls : oty] if [ls] is a constant.
    The length of [tyl] must be equal to that of [ls.ls_args], and
    [oty] should be [None] if and only if [ls] is a predicate symbol. *)

val t_app_partial : lsymbol -> term list -> ty list -> ty option -> term
(** [t_app_partial ls tl tyl oty] produces a closure of [ls] and applies
    it to [tl] using [t_func_app]. The type signature of the closure is
    obtained by prepending the list of types of terms in [tl] to [tyl].
    The resulting list must have the same length as [ls.ls_args], and
    [oty] should be [None] if and only if [ls] is a predicate symbol.
    If the symbol is fully applied ([tyl] is empty), the [Tapp] term
    is returned. Otherwise, no beta-reduction is performed, in order
    to preserve the closure. *)

val t_func_app_beta : term -> term -> term
(** [t_func_app_beta f a] applies [f] to [a] performing beta-reduction
    when [f] is a lambda-term. Always returns a value-typed term, even
    if [f] is a lambda-term built on top of a formula. *)

val t_pred_app_beta : term -> term -> term
(** [t_pred_app_beta f a] applies [f] to [a] performing beta-reduction
    when [f] is a lambda-term. Always returns a formula, even if [f] is
    a lambda-term built on top of a bool-typed term. *)

val t_func_app_beta_l : term -> term list -> term
val t_pred_app_beta_l : term -> term list -> term

(** {2 Term library} *)

(** One-level (non-recursive) term traversal *)

val t_map : (term -> term) -> term -> term
val t_fold : ('a -> term -> 'a) -> 'a -> term -> 'a
val t_iter : (term -> unit) -> term -> unit
val t_map_fold : ('a -> term -> 'a * term) -> 'a -> term -> 'a * term

val t_all : (term -> bool) -> term -> bool
val t_any : (term -> bool) -> term -> bool

(** Special maps *)

val t_map_simp : (term -> term) -> term -> term
(** [t_map_simp] reconstructs the term using simplification constructors *)

val t_map_sign : (bool -> term -> term) -> bool -> term -> term
(** [t_map_sign] passes a polarity parameter, unfolds if-then-else and iff *)

val t_map_cont : ((term -> 'a) -> term -> 'a) -> (term -> 'a) -> term -> 'a
(** [t_map_cont] is [t_map] in continuation-passing style *)

val list_map_cont: (('a -> 'b) -> 'c -> 'b) -> ('a list -> 'b) -> 'c list -> 'b

(** Trigger traversal *)

val tr_equal : trigger -> trigger -> bool
val tr_map : (term -> term) -> trigger -> trigger
val tr_fold : ('a -> term -> 'a) -> 'a -> trigger -> 'a
val tr_map_fold : ('a -> term -> 'a * term) -> 'a -> trigger -> 'a * trigger

(** Traversal with separate functions for value-typed and prop-typed terms *)

module TermTF : sig

  val t_select : (term -> 'a) -> (term -> 'a) -> term -> 'a
  (** [t_select fnT fnF t] is [fnT t] if [t] is a value, [fnF t] otherwise *)

  val t_selecti : ('a -> term -> 'b) -> ('a -> term -> 'b) -> 'a -> term -> 'b
  (** [t_selecti fnT fnF acc t] is [t_select (fnT acc) (fnF acc) t] *)

  val t_map : (term -> term) -> (term -> term) -> term -> term
  (** [t_map fnT fnF = t_map (t_select fnT fnF)] *)

  val t_fold : ('a -> term -> 'a) -> ('a -> term -> 'a) -> 'a -> term -> 'a
  (** [t_fold fnT fnF = t_fold (t_selecti fnT fnF)] *)

  val t_map_fold : ('a -> term -> 'a * term) ->
    ('a -> term -> 'a * term) -> 'a -> term -> 'a * term

  val t_all : (term -> bool) -> (term -> bool) -> term -> bool
  val t_any : (term -> bool) -> (term -> bool) -> term -> bool

  val t_map_simp : (term -> term) -> (term -> term) -> term -> term

  val t_map_sign : (bool -> term -> term) ->
    (bool -> term -> term) -> bool -> term -> term

  val t_map_cont : ((term -> 'a) -> term -> 'a) ->
    ((term -> 'a) -> term -> 'a) -> (term -> 'a) -> term -> 'a

  val tr_map : (term -> term) -> (term -> term) -> trigger -> trigger

  val tr_fold : ('a -> term -> 'a) -> ('a -> term -> 'a) -> 'a -> trigger -> 'a

  val tr_map_fold : ('a -> term -> 'a * term) ->
    ('a -> term -> 'a * term) -> 'a -> trigger -> 'a * trigger
end

(** {2 Map/fold over free variables} *)

val t_v_map : (vsymbol -> term) -> term -> term
val t_v_fold : ('a -> vsymbol -> 'a) -> 'a -> term -> 'a
val t_v_all : (vsymbol -> bool) -> term -> bool
val t_v_any : (vsymbol -> bool) -> term -> bool

val t_v_count : ('a -> vsymbol -> int -> 'a) -> 'a -> term -> 'a

val t_v_occurs : vsymbol -> term -> int

(** {2 Variable substitution} *)

val t_subst_single : vsymbol -> term -> term -> term
(** [t_subst_single v t1 t2] substitutes variable [v] in [t2] by [t1] *)

val t_subst : term Mvs.t -> term -> term
(** [t_subst m t] substitutes variables in [t] by the variable mapping [m] *)

val t_ty_subst : ty Mtv.t -> term Mvs.t -> term -> term
(** [t_ty_subst mt mv t] substitutes simultaneously type variables by
    mapping [mt] and term variables by mapping [mv] in term [t] *)

val t_subst_types : ty Mtv.t -> term Mvs.t -> term -> term Mvs.t * term
(** [t_subst_types mt mv t] substitutes type variables of term [t] by
    mapping [mt]. This operation may rename the variables in [t], and
    the same renaming is simultaneously applied to the variables of
    the substitution [mv] (both domain and codomain).
    Example: [t_subst_types {'a -> int} {x:'a -> t:'a} (f x)]
       returns ({z:int -> t:int},(f z))   *)

(** {2 Find free variables and type variables} *)

val t_closed : term -> bool

val t_vars : term -> int Mvs.t

val t_freevars : int Mvs.t -> term -> int Mvs.t

val t_ty_freevars : Stv.t -> term -> Stv.t

(** {2 Map/fold over types and logical symbols in terms and patterns} *)

val t_gen_map :
  (ty -> ty) -> (lsymbol -> lsymbol) -> vsymbol Mvs.t -> term -> term

val t_s_map : (ty -> ty) -> (lsymbol -> lsymbol) -> term -> term
val t_s_fold : ('a -> ty -> 'a) -> ('a -> lsymbol -> 'a) -> 'a -> term -> 'a

val t_s_all : (ty -> bool) -> (lsymbol -> bool) -> term -> bool
val t_s_any : (ty -> bool) -> (lsymbol -> bool) -> term -> bool

val t_ty_map : (ty -> ty) -> term -> term
val t_ty_fold : ('a -> ty -> 'a) -> 'a -> term -> 'a

(** Map/fold over applications in terms (but not in patterns!) *)

val t_app_map :
  (lsymbol -> ty list -> ty option -> lsymbol) -> term -> term

val t_app_fold :
  ('a -> lsymbol -> ty list -> ty option -> 'a) -> 'a -> term -> 'a

(** {2 Subterm occurrence check and replacement} *)

val t_occurs  : term -> term -> bool
val t_replace : term -> term -> term -> term
