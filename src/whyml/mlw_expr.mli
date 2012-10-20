(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Util
open Ident
open Ty
open Term
open Mlw_ty
open Mlw_ty.T

(** program/logic symbols *)

(* plymbols represent algebraic type constructors and projections.
   They must be fully applied and the result is equal to the application of
   the lsymbol. We need this kind of symbols to cover nullary constructors,
   such as Nil, which cannot be given a post-condition. They cannot be
   locally defined and therefore every type variable and region in their
   type signature can be instantiated. *)

type plsymbol = private {
  pl_ls     : lsymbol;
  pl_args   : vty_value list;
  pl_value  : vty_value;
  pl_effect : effect;
  pl_hidden : bool;
  pl_rdonly : bool;
}

val pl_equal : plsymbol -> plsymbol -> bool

val create_plsymbol : ?hidden:bool -> ?rdonly:bool ->
  preid -> vty_value list -> vty_value -> plsymbol
  (* FIXME? Effect calculation is hardwired to correspond to constructors
     and projections: mutable arguments are reset, mutable result is read. *)

exception HiddenPLS of lsymbol
exception RdOnlyPLS of lsymbol

(** cloning *)

type symbol_map = private {
  sm_pure : Theory.symbol_map;
  sm_its  : itysymbol Mits.t;
  sm_pls  : plsymbol Mls.t;
}

val pl_clone : Theory.symbol_map -> symbol_map

(** patterns *)

type ppattern = private {
  ppat_pattern : pattern;
  ppat_vtv     : vty_value;
  ppat_effect  : effect;
}

val ppat_wild : vty_value -> ppattern
val ppat_var : pvsymbol -> ppattern
val ppat_plapp : plsymbol -> ppattern list -> vty_value -> ppattern
val ppat_lapp : lsymbol -> ppattern list -> vty_value -> ppattern
val ppat_or : ppattern -> ppattern -> ppattern
val ppat_as : ppattern -> pvsymbol -> ppattern

type pre_ppattern =
  | PPwild
  | PPvar  of preid
  | PPlapp of lsymbol * pre_ppattern list
  | PPpapp of plsymbol * pre_ppattern list
  | PPor   of pre_ppattern * pre_ppattern
  | PPas   of pre_ppattern * preid

val make_ppattern : pre_ppattern -> vty_value -> pvsymbol Mstr.t * ppattern

(** program symbols *)

(* psymbols represent lambda-abstractions. They are polymorphic and
   can be type-instantiated in some type variables and regions of
   their type signature. *)

type psymbol = private {
  ps_name  : ident;
  ps_vta   : vty_arrow;
  ps_varm  : varmap;
  ps_vars  : varset;
  (* this varset covers the type variables and regions of the defining
     lambda that cannot be instantiated. Every other type variable
     and region in ps_vta is generalized and can be instantiated. *)
  ps_subst : ity_subst;
  (* this substitution instantiates every type variable and region
     in ps_vars to itself *)
}

module Mps : Map.S with type key = psymbol
module Sps : Mps.Set
module Hps : Hashtbl.S with type key = psymbol
module Wps : Hashweak.S with type key = psymbol

val ps_equal : psymbol -> psymbol -> bool

val create_psymbol : preid -> vty_arrow -> psymbol

val create_psymbol_extra : preid -> vty_arrow -> Spv.t -> Sps.t -> psymbol

val spec_pvset : Spv.t -> spec -> Spv.t
val ps_pvset : Spv.t -> psymbol -> Spv.t

(** program expressions *)

type assertion_kind = Aassert | Aassume | Acheck

type for_direction = To | DownTo

type for_bounds = pvsymbol * for_direction * pvsymbol

type invariant = term

type let_sym =
  | LetV of pvsymbol
  | LetA of psymbol

type expr = private {
  e_node   : expr_node;
  e_vty    : vty;
  e_effect : effect;
  e_varm   : varmap;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node = private
  | Elogic  of term
  | Evalue  of pvsymbol
  | Earrow  of psymbol
  | Eapp    of expr * pvsymbol * spec
  | Elet    of let_defn * expr
  | Erec    of fun_defn list * expr
  | Eif     of expr * expr * expr
  | Ecase   of expr * (ppattern * expr) list
  | Eassign of expr * region * pvsymbol
  | Eghost  of expr
  | Eany    of spec
  | Eloop   of invariant * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant * expr
  | Eraise  of xsymbol * expr
  | Etry    of expr * (xsymbol * pvsymbol * expr) list
  | Eabstr  of expr * spec
  | Eassert of assertion_kind * term
  | Eabsurd

and let_defn = private {
  let_sym  : let_sym;
  let_expr : expr;
}

and fun_defn = private {
  fun_ps     : psymbol;
  fun_lambda : lambda;
  fun_varm   : varmap;
}

and lambda = {
  l_args : pvsymbol list;
  l_expr : expr;
  l_spec : spec;
}

val e_pvset : Spv.t -> expr -> Spv.t
val l_pvset : Spv.t -> lambda -> Spv.t

val e_label : ?loc:Loc.position -> Slab.t -> expr -> expr
val e_label_add : label -> expr -> expr
val e_label_copy : expr -> expr -> expr

val e_value : pvsymbol -> expr
val e_arrow : psymbol -> vty_arrow -> expr

exception ValueExpected of expr
exception ArrowExpected of expr

val vtv_of_expr : expr -> vty_value
val vta_of_expr : expr -> vty_arrow

exception GhostWrite of expr * region
exception GhostRaise of expr * xsymbol
(* a ghost expression writes in a non-ghost region or raises an exception *)

val e_app : expr -> expr list -> expr
val e_lapp : lsymbol -> expr list -> ity -> expr
val e_plapp : plsymbol -> expr list -> ity -> expr

val create_let_defn : preid -> expr -> let_defn
val create_fun_defn : preid -> lambda -> fun_defn
val create_rec_defn : (psymbol * lambda) list -> fun_defn list

val rec_varmap : varmap -> fun_defn list -> varmap

exception StaleRegion of expr * ident
(* freshness violation: a previously reset region is associated to an ident *)

val e_let : let_defn -> expr -> expr
val e_rec : fun_defn list -> expr -> expr

val e_if : expr -> expr -> expr -> expr
val e_case : expr -> (ppattern * expr) list -> expr

exception Immutable of expr

val e_assign : expr -> expr -> expr
val e_ghost : expr -> expr

val fs_void : lsymbol
val t_void : term
val e_void : expr

val e_const : constant -> expr
val e_int_const : string -> expr
val e_real_const : real_constant -> expr

val e_lazy_and : expr -> expr -> expr
val e_lazy_or : expr -> expr -> expr
val e_not : expr -> expr

val e_raise : xsymbol -> expr -> ity -> expr
val e_try : expr -> (xsymbol * pvsymbol * expr) list -> expr

val e_loop : invariant -> variant list -> expr -> expr

val e_for :
  pvsymbol -> expr -> for_direction -> expr -> invariant -> expr -> expr

val e_any : spec -> vty -> expr
val e_abstract : expr -> spec -> expr
val e_assert : assertion_kind -> term -> expr
val e_absurd : ity -> expr

(** expression traversal *)

val e_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a

val e_purify : expr -> term option
