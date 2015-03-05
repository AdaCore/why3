(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Term
open Ity

(** {2 Routine symbols} *)

type rsymbol = private {
  rs_name  : ident;
  rs_cty   : cty;
  rs_ghost : bool;
  rs_logic : rs_logic;
  rs_field : pvsymbol option;
}

and rs_logic =
  | RLnone            (* non-pure symbol *)
  | RLpv of pvsymbol  (* local let-function *)
  | RLls of lsymbol   (* top-level let-function or let-predicate *)
  | RLlemma           (* top-level or local let-lemma *)

module Mrs : Extmap.S with type key = rsymbol
module Srs : Extset.S with module M = Mrs
module Hrs : Exthtbl.S with type key = rsymbol
module Wrs : Weakhtbl.S with type key = rsymbol

val rs_compare : rsymbol -> rsymbol -> int
val rs_equal : rsymbol -> rsymbol -> bool
val rs_hash : rsymbol -> int

type rs_kind =
  | RKnone    (* non-pure symbol *)
  | RKlocal   (* local let-function *)
  | RKfunc    (* top-level let-function *)
  | RKpred    (* top-level let-predicate *)
  | RKlemma   (* top-level or local let-lemma *)

val create_rsymbol : preid -> ?ghost:bool -> ?kind:rs_kind -> cty -> rsymbol
(** If [?kind] is supplied and is not [RKnone], then [cty]
    must have no effects except for resets which are ignored.
    If [?kind] is [RKnone] or [RKlemma], external mutable reads
    are allowed, otherwise [cty.cty_freeze.isb_reg] must be empty.
    If [?kind] is [RKlocal], the type variables in [cty] are frozen
    but regions are instantiable. If [?kind] is [RKpred] the result
    type must be [ity_bool]. If [?kind] is [RKlemma] and the result
    type is not [ity_unit], an existential premise is generated. *)

val create_constructor :
  constr:int -> preid -> itysymbol -> pvsymbol list -> rsymbol

val create_field : preid -> itysymbol -> pvsymbol -> rsymbol

val restore_rs : lsymbol -> rsymbol
(** raises [Not_found] if the argument is not a [rs_logic] *)

(** {2 Program patterns} *)

type prog_pattern = private {
  pp_pat   : pattern;
  pp_ity   : ity;
  pp_ghost : bool;
}

type pre_pattern =
  | PPwild
  | PPvar of preid
  | PPapp of rsymbol * pre_pattern list
  | PPor  of pre_pattern * pre_pattern
  | PPas  of pre_pattern * preid

exception ConstructorExpected of rsymbol

val create_prog_pattern :
  pre_pattern -> ?ghost:bool -> ity -> pvsymbol Mstr.t * prog_pattern

(** {2 Program expressions} *)

type lazy_op = Eand | Eor

type assertion_kind = Assert | Assume | Check

type for_direction = To | DownTo

type for_bounds = pvsymbol * for_direction * pvsymbol

type invariant = term

type variant = term * lsymbol option (** tau * (tau -> tau -> prop) *)

type assign = pvsymbol * rsymbol * pvsymbol (* region * field * value *)

type vty =
  | VtyI of ity
  | VtyC of cty

type val_decl =
  | ValV of pvsymbol
  | ValS of rsymbol

type expr = private {
  e_node   : expr_node;
  e_vty    : vty;
  e_ghost  : bool;
  e_effect : effect;
  e_vars   : Spv.t;
  e_syms   : Srs.t;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node = private
  | Evar    of pvsymbol
  | Esym    of rsymbol
  | Econst  of Number.constant
  | Eapp    of expr * pvsymbol list * cty
  | Efun    of expr
  | Elet    of let_defn * expr
  | Erec    of rec_defn * expr
  | Enot    of expr
  | Elazy   of lazy_op * expr * expr
  | Eif     of expr * expr * expr
  | Ecase   of expr * (prog_pattern * expr) list
  | Eassign of assign list
  | Ewhile  of expr * invariant list * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant list * expr
  | Etry    of expr * (xsymbol * pvsymbol * expr) list
  | Eraise  of xsymbol * expr
  | Eghost  of expr
  | Eassert of assertion_kind * term
  | Epure   of term
  | Eabsurd
  | Etrue
  | Efalse
  | Eany

and let_defn = private {
  let_sym  : val_decl;
  let_expr : expr;
}

and rec_defn = private {
  rec_defn : fun_defn list;
  rec_decr : lsymbol option;
}

and fun_defn = {
  fun_sym  : rsymbol; (* exported symbol *)
  fun_rsym : rsymbol; (* internal symbol *)
  fun_expr : expr;    (* Efun *)
  fun_varl : variant list;
}

val e_label : ?loc:Loc.position -> Slab.t -> expr -> expr
val e_label_add : label -> expr -> expr
val e_label_copy : expr -> expr -> expr

exception ItyExpected of expr
exception CtyExpected of expr

val ity_of_expr : expr -> ity
val cty_of_expr : expr -> cty

val check_expr : expr -> unit
(** [check_expr e] verifies that [e] does not perform bad
    ghost writes nor contains stale (i.e., reset) regions.
    This function must be called for any expression which
    is used outside of an [Efun]-closure. *)

val e_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a

val e_find_minimal : (expr -> bool) -> expr -> expr
(** [e_find_minimal pr e] looks for a minimal sub-expression
    of [e] satisfying [pr], raises [Not_found] if none found. *)

val proxy_label : label

(** {2 Smart constructors} *)

val e_var : pvsymbol -> expr
val e_sym : rsymbol  -> expr

val e_const : Number.constant -> expr
val e_nat_const : int -> expr

val create_let_defn_pv :
  preid -> ?ghost:bool -> expr -> let_defn * pvsymbol

val create_let_defn_rs :
  preid -> ?ghost:bool -> ?kind:rs_kind -> expr -> let_defn * rsymbol

val create_let_defn :
  preid -> ?ghost:bool -> ?kind:rs_kind -> expr -> let_defn

val create_rec_defn :
  (rsymbol * expr (* Efun *) * variant list * rs_kind) list -> rec_defn

val e_fun :
  pvsymbol list -> pre list -> post list -> post list Mexn.t -> expr -> expr

val e_let : let_defn -> expr -> expr
val e_rec : rec_defn -> expr -> expr

val e_app : expr -> expr list -> ity list -> ity -> expr

val e_assign : (expr * rsymbol * expr) list -> expr

val e_ghost : expr -> expr
val e_ghostify : expr -> expr

val e_if : expr -> expr -> expr -> expr
val e_lazy : lazy_op -> expr -> expr -> expr
val e_not : expr -> expr
val e_true : expr
val e_false : expr

val e_raise : xsymbol -> expr -> ity -> expr

val e_try : expr -> (xsymbol * pvsymbol * expr) list -> expr

val e_case : expr -> (prog_pattern * expr) list -> expr

val e_while : expr -> invariant list -> variant list -> expr -> expr

val e_for :
  pvsymbol -> expr -> for_direction -> expr -> invariant list -> expr -> expr

val e_pure : term -> expr

val e_assert : assertion_kind -> term -> expr

val e_absurd : ity -> expr

val e_any : cty -> expr

(** {2 Built-in symbols} *)

val rs_bool_true  : rsymbol
val rs_bool_false : rsymbol

val e_bool_true  : expr
val e_bool_false : expr

val rs_tuple : int -> rsymbol
val e_tuple : expr list -> expr

val rs_void : rsymbol
val e_void : expr

val is_rs_tuple : rsymbol -> bool

val rs_func_app : rsymbol
val e_func_app : expr -> expr -> expr
val e_func_app_l : expr -> expr list -> expr

(** {2 Pretty-printing} *)

val forget_rs  : rsymbol -> unit (* flush id_unique for a program symbol *)

val print_rs   : Format.formatter -> rsymbol -> unit  (* program symbol *)
val print_expr : Format.formatter -> expr -> unit     (* expression *)

val print_val_decl : Format.formatter -> val_decl -> unit
val print_let_defn : Format.formatter -> let_defn -> unit
val print_rec_defn : Format.formatter -> rec_defn -> unit
