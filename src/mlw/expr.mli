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

(** {2 Program symbols} *)

type psymbol = private {
  ps_name   : ident;
  ps_cty    : cty;
  ps_ghost  : bool;
  ps_logic  : ps_logic;
  ps_mfield : pvsymbol option;
}

and ps_logic =
  | PLnone            (* non-pure symbol *)
  | PLpv of pvsymbol  (* local let-function *)
  | PLls of lsymbol   (* top-level let-function or let-predicate *)
  | PLlemma           (* top-level or local let-lemma *)

module Mps : Extmap.S with type key = psymbol
module Sps : Extset.S with module M = Mps
module Hps : Exthtbl.S with type key = psymbol
module Wps : Weakhtbl.S with type key = psymbol

val ps_compare : psymbol -> psymbol -> int
val ps_equal : psymbol -> psymbol -> bool
val ps_hash : psymbol -> int

type ps_kind =
  | PKnone            (* non-pure symbol *)
  | PKpv of pvsymbol  (* local let-function *)
  | PKlocal           (* new local let-function *)
  | PKfunc of int     (* new top-level let-function or constructor *)
  | PKpred            (* new top-level let-predicate *)
  | PKlemma           (* top-level or local let-lemma *)

val create_psymbol : preid -> ?ghost:bool -> ?kind:ps_kind -> cty -> psymbol
(** If [?kind] is supplied and is not [PKnone], then [cty]
    must have no effects except for resets which are ignored.
    If [?kind] is [PKnone] or [PKlemma], external mutable reads
    are allowed, otherwise [cty.cty_freeze.isb_reg] must be empty.
    If [?kind] is [PKlocal], the type variables in [cty] are frozen
    but regions are instantiable. If [?kind] is [PKpred] the result
    type must be [ity_bool]. If [?kind] is [PKlemma] and the result
    type is not [ity_unit], an existential premise is generated. *)

val create_mutable_field : preid -> itysymbol -> pvsymbol -> psymbol

val restore_ps : lsymbol -> psymbol
(** raises [Not_found] if the argument is not a [ps_logic] *)

(** {2 Program patterns} *)

type prog_pattern = private {
  pp_pat   : pattern;
  pp_ity   : ity;
  pp_ghost : bool;
}

type pre_pattern =
  | PPwild
  | PPvar of preid
  | PPapp of psymbol * pre_pattern list
  | PPor  of pre_pattern * pre_pattern
  | PPas  of pre_pattern * preid

exception ConstructorExpected of psymbol

val create_prog_pattern :
  pre_pattern -> ?ghost:bool -> ity -> pvsymbol Mstr.t * prog_pattern

(** {2 Program expressions} *)

type lazy_op = Eand | Eor

type assertion_kind = Assert | Assume | Check

type for_direction = To | DownTo

type for_bounds = pvsymbol * for_direction * pvsymbol

type invariant = term

type variant = term * lsymbol option (** tau * (tau -> tau -> prop) *)

type assign = pvsymbol * psymbol * pvsymbol (* region * field * value *)

type vty =
  | VtyI of ity
  | VtyC of cty

type val_decl =
  | ValV of pvsymbol
  | ValS of psymbol

type expr = private {
  e_node   : expr_node;
  e_vty    : vty;
  e_ghost  : bool;
  e_effect : effect;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node = private
  | Evar    of pvsymbol
  | Esym    of psymbol
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
  | Ewhile  of expr * invariant * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant * expr
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
  fun_sym  : psymbol; (* exported symbol *)
  fun_rsym : psymbol; (* internal symbol *)
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

val e_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a

val e_find_minimal : (expr -> bool) -> expr -> expr
(** [e_find_minimal pr e] looks for a minimal sub-expression
    of [e] satisfying [pr], raises [Not_found] if none found. *)

val proxy_label : label

(** {2 Smart constructors} *)

val e_var : pvsymbol -> expr
val e_sym : psymbol  -> expr

val e_const : Number.constant -> expr
val e_nat_const : int -> expr

val create_let_defn :
  preid -> ?ghost:bool -> expr -> let_defn

val create_let_defn_pv :
  preid -> ?ghost:bool -> expr -> let_defn * pvsymbol

val create_let_defn_ps :
  preid -> ?ghost:bool -> ?kind:ps_kind -> expr -> let_defn * psymbol

val create_rec_defn :
  (psymbol * expr (* Efun *) * variant list * ps_kind) list -> rec_defn

val e_fun :
  pvsymbol list -> pre list -> post list -> post list Mexn.t -> expr -> expr

val e_let : let_defn -> expr -> expr
val e_rec : rec_defn -> expr -> expr

val e_app : expr -> expr list -> ity list -> ity -> expr

val e_assign : (expr * psymbol * expr) list -> expr

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

val e_while : expr -> invariant -> variant list -> expr -> expr

val e_for :
  pvsymbol -> expr -> for_direction -> expr -> invariant -> expr -> expr

val e_pure : term -> expr

val e_assert : assertion_kind -> term -> expr

val e_absurd : ity -> expr

val e_any : cty -> expr

(** {2 Built-in symbols} *)

val ps_bool_true  : psymbol
val ps_bool_false : psymbol

val e_bool_true  : expr
val e_bool_false : expr

val ps_tuple : int -> psymbol
val e_tuple : expr list -> expr

val ps_void : psymbol
val e_void : expr

val is_ps_tuple : psymbol -> bool

val ps_func_app : psymbol
val e_func_app : expr -> expr -> expr
val e_func_app_l : expr -> expr list -> expr
