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

val rs_kind : rsymbol -> rs_kind

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

val ls_of_rs : rsymbol -> lsymbol
(** raises [Invalid_argument] is [rs_logic] is not an [RLls] *)

val fd_of_rs : rsymbol -> pvsymbol
(** raises [Invalid_argument] is [rs_field] is [None] *)

(** {2 Program patterns} *)

type pat_ghost =
  | PGfail  (* refutable ghost subpattern before "|" *)
  | PGlast  (* refutable ghost subpattern otherwise  *)
  | PGnone  (* every ghost subpattern is irrefutable *)

type prog_pattern = private {
  pp_pat  : pattern;    (* pure pattern *)
  pp_ity  : ity;        (* type of the matched value *)
  pp_mask : mask;       (* mask of the matched value *)
  pp_fail : pat_ghost;  (* refutable ghost subpattern *)
}

type pre_pattern =
  | PPwild
  | PPvar of preid * bool
  | PPapp of rsymbol * pre_pattern list
  | PPas  of pre_pattern * preid * bool
  | PPor  of pre_pattern * pre_pattern

exception ConstructorExpected of rsymbol

val create_prog_pattern :
  pre_pattern -> ity -> mask -> pvsymbol Mstr.t * prog_pattern

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
  e_mask   : mask;
  e_effect : effect;
  e_attrs  : Sattr.t;
  e_loc    : Loc.position option;
}

and expr_node =
  | Evar    of pvsymbol
  | Econst  of Number.constant
  | Eexec   of cexp * cty
  | Eassign of assign list
  | Elet    of let_defn * expr
  | Eif     of expr * expr * expr
  | Ematch  of expr * reg_branch list * exn_branch Mxs.t
  | Ewhile  of expr * invariant list * variant list * expr
  | Efor    of pvsymbol * for_bounds * pvsymbol * invariant list * expr
  | Eraise  of xsymbol * expr
  | Eexn    of xsymbol * expr
  | Eassert of assertion_kind * term
  | Eghost  of expr
  | Epure   of term
  | Eabsurd

and reg_branch = prog_pattern * expr

and exn_branch = pvsymbol list * expr

and cexp = private {
  c_node : cexp_node;
  c_cty  : cty;
}

and cexp_node =
  | Capp of rsymbol * pvsymbol list
  | Cpur of lsymbol * pvsymbol list
  | Cfun of expr
  | Cany

and let_defn = private
  | LDvar of pvsymbol * expr
  | LDsym of rsymbol * cexp
  | LDrec of rec_defn list

and rec_defn = private {
  rec_sym  : rsymbol; (* exported symbol *)
  rec_rsym : rsymbol; (* internal symbol *)
  rec_fun  : cexp;    (* necessary a Cfun *)
  rec_varl : variant list;
}

(** {2 Expressions} *)

val e_attr_set : ?loc:Loc.position -> Sattr.t -> expr -> expr
val e_attr_push : ?loc:Loc.position -> Sattr.t -> expr -> expr
val e_attr_add : attribute -> expr -> expr
val e_attr_copy : expr -> expr -> expr

(** {2 Definitions} *)

val let_var :
  preid -> ?ghost:bool -> expr -> let_defn * pvsymbol

val let_sym :
  preid -> ?ghost:bool -> ?kind:rs_kind -> cexp -> let_defn * rsymbol

val let_rec :
  (rsymbol * cexp * variant list * rs_kind) list -> let_defn * rec_defn list

val ls_decr_of_rec_defn : rec_defn -> lsymbol option
(* returns the dummy predicate symbol used in the precondition of
   the rec_rsym rsymbol to store the instantiated variant list *)

(** {2 Callable expressions} *)

val c_app : rsymbol -> pvsymbol list -> ity list -> ity -> cexp
val c_pur : lsymbol -> pvsymbol list -> ity list -> ity -> cexp

val c_fun : ?mask:mask -> pvsymbol list ->
  pre list -> post list -> post list Mxs.t -> pvsymbol Mpv.t -> expr -> cexp

val c_any : cty -> cexp

(** {2 Expression constructors} *)

val e_var : pvsymbol -> expr

val e_const : Number.constant -> ity -> expr
val e_nat_const : int -> expr

val e_exec : cexp -> expr

val e_app : rsymbol -> expr list -> ity list -> ity -> expr
val e_pur : lsymbol -> expr list -> ity list -> ity -> expr

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

exception ExceptionLeak of xsymbol

val e_exn : xsymbol -> expr -> expr

val e_raise : xsymbol -> expr -> ity -> expr

val e_match : expr -> reg_branch list -> exn_branch Mxs.t -> expr

val e_while : expr -> invariant list -> variant list -> expr -> expr

val e_for : pvsymbol -> expr -> for_direction -> expr ->
              pvsymbol -> invariant list -> expr -> expr

val e_assert : assertion_kind -> term -> expr

val e_ghostify : bool -> expr -> expr

val e_pure : term -> expr

val e_absurd : ity -> expr

(** {2 Expression manipulation tools} *)

val e_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a
(** [e_fold] does not descend into Cfun *)

val e_locate_effect : (effect -> bool) -> expr -> Loc.position option
(** [e_locate_effect pr e] looks for a minimal sub-expression of
    [e] whose effect satisfies [pr] and returns its location *)

val e_rs_subst : rsymbol Mrs.t -> expr -> expr
val c_rs_subst : rsymbol Mrs.t -> cexp -> cexp

val term_of_post : prop:bool -> vsymbol -> term -> (term * term) option

val term_of_expr : prop:bool -> expr -> term option
val post_of_expr : term -> expr -> term option

val e_ghost : expr -> bool
val c_ghost : cexp -> bool

(** {2 Built-in symbols} *)

val rs_true  : rsymbol
val rs_false : rsymbol

val rs_tuple : int -> rsymbol
val e_tuple : expr list -> expr

val rs_void : rsymbol
val fs_void : lsymbol
val e_void : expr
val t_void : term

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
