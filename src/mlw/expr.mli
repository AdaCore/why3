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

open Wstdlib
open Ident
open Term
open Ity

(** {2 Routine symbols} *)

type rsymbol = private {
  rs_name  : ident;
  rs_cty   : cty;
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

val create_projection : itysymbol -> pvsymbol -> rsymbol

val restore_rs : lsymbol -> rsymbol
(** raises [Not_found] if the argument is not a [rs_logic] *)

val rs_ghost : rsymbol -> bool

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

type assertion_kind = Assert | Assume | Check

type for_direction = To | DownTo

type for_bounds = pvsymbol * for_direction * pvsymbol

type invariant = term

type variant = term * lsymbol option (** tau * (tau -> tau -> prop) *)

type assign = pvsymbol * rsymbol * pvsymbol (* region * field * value *)

type expr = private {
  e_node   : expr_node;
  e_ity    : ity;
  e_effect : effect;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node = private
  | Evar    of pvsymbol
  | Econst  of Number.constant
  | Eexec   of cexp
  | Eassign of assign list
  | Elet    of let_defn * expr
  | Eif     of expr * expr * expr
  | Ecase   of expr * (prog_pattern * expr) list
  | Ewhile  of expr * invariant list * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant list * expr
  | Etry    of expr * (xsymbol * pvsymbol * expr) list
  | Eraise  of xsymbol * expr
  | Eassert of assertion_kind * term
  | Epure   of term
  | Eabsurd

and cexp = private {
  c_node : cexp_node;
  c_cty  : cty;
}

and cexp_node = private
  | Capp of rsymbol * pvsymbol list
  | Cfun of expr
  | Cany

and let_defn = private
  | LDvar of pvsymbol * expr
  | LDsym of rsymbol * cexp
  | LDrec of rec_defn list

and rec_defn = private {
  rec_sym  : rsymbol; (* exported symbol *)
  rec_rsym : rsymbol; (* internal symbol *)
  rec_fun  : cexp;    (* Cfun *)
  rec_varl : variant list;
}

(** {2 Expressions} *)

val e_label : ?loc:Loc.position -> Slab.t -> expr -> expr
val e_label_add : label -> expr -> expr
val e_label_copy : expr -> expr -> expr

val e_ghost : expr -> bool
val c_ghost : cexp -> bool

val e_ghostify : bool -> expr -> expr
val c_ghostify : bool -> cexp -> cexp

(** {2 Definitions} *)

val let_var :
  preid -> ?ghost:bool -> expr -> let_defn * pvsymbol

val let_sym :
  preid -> ?ghost:bool -> ?kind:rs_kind -> cexp -> let_defn * rsymbol

val let_rec :
  (rsymbol * cexp * variant list * rs_kind) list -> let_defn * rec_defn list

val ls_decr_of_let_defn : let_defn -> lsymbol option
(* returns the dummy predicate symbol used in the precondition of
   the rec_rsym rsymbol to store the instantiated variant list *)

(** {2 Callable expressions} *)

val c_app : rsymbol -> pvsymbol list -> ity list -> ity -> cexp

val c_fun : pvsymbol list ->
  pre list -> post list -> post list Mexn.t -> pvsymbol Mpv.t -> expr -> cexp

val c_any : cty -> cexp

type ext_cexp = let_defn list * cexp

val ext_c_sym : rsymbol -> ext_cexp

val ext_c_app : ext_cexp -> expr list -> ity list -> ity -> ext_cexp

(** {2 Expression constructors} *)

val e_var : pvsymbol -> expr

val e_const : Number.constant -> expr
val e_nat_const : int -> expr

val e_exec : cexp -> expr

val e_app : rsymbol -> expr list -> ity list -> ity -> expr

val e_let : let_defn -> expr -> expr

exception FieldExpected of rsymbol

val e_assign : (expr * rsymbol * expr) list -> expr

val e_if : expr -> expr -> expr -> expr

val e_and : expr -> expr -> expr
val e_or  : expr -> expr -> expr
val e_not : expr -> expr

val e_true  : expr
val e_false : expr

val is_e_true  : expr -> bool
val is_e_false : expr -> bool

val e_raise : xsymbol -> expr -> ity -> expr

val e_try : expr -> (xsymbol * pvsymbol * expr) list -> expr

val e_case : expr -> (prog_pattern * expr) list -> expr

val e_while : expr -> invariant list -> variant list -> expr -> expr

val e_for : pvsymbol ->
  expr -> for_direction -> expr -> invariant list -> expr -> expr

val e_pure : term -> expr

val e_assert : assertion_kind -> term -> expr

val e_absurd : ity -> expr

(** {2 Expression manipulation tools} *)

val e_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a
(** [e_fold] does not descend into Cfun *)

val e_locate_effect : (effect -> bool) -> expr -> Loc.position option
(** [e_locate_effect pr e] looks for a minimal sub-expression of
    [e] whose effect satisfies [pr] and returns its location *)

val proxy_label : label

(** {2 Built-in symbols} *)

val rs_true  : rsymbol
val rs_false : rsymbol

val rs_tuple : int -> rsymbol
val e_tuple : expr list -> expr

val rs_void : rsymbol
val e_void : expr

val is_e_void : expr -> bool
val is_rs_tuple : rsymbol -> bool

val rs_func_app : rsymbol
val ld_func_app : let_defn
val e_func_app : expr -> expr -> expr
val e_func_app_l : expr -> expr list -> expr

(** {2 Pretty-printing} *)

val forget_rs  : rsymbol -> unit (* flush id_unique for a program symbol *)

val print_rs   : Format.formatter -> rsymbol -> unit  (* program symbol *)

val print_expr : Format.formatter -> expr -> unit     (* expression *)

val print_let_defn : Format.formatter -> let_defn -> unit
