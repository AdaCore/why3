(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Why3
open Util
open Ident
open Ty
open Term
open Mlw_ty
open Mlw_ty.T

(** program variables *)

(* pvsymbols represent function arguments and pattern variables *)

type pvsymbol = private {
  pv_vs  : vsymbol;
  pv_vtv : vty_value;
}

val pv_equal : pvsymbol -> pvsymbol -> bool

val create_pvsymbol : preid -> vty_value -> pvsymbol

(* pasymbols represent higher-order intermediate computation results
   introduced by let-expressions. They cannot be type-instantiated. *)

type pasymbol = private {
  pa_name : ident;
  pa_vta  : vty_arrow;
  pa_vars : varset;
  (* this varset contains pa_vta.vta_vars together with all type
     variables and regions of the defining expression, in order to
     cover effects and specification and not overgeneralize *)
}

val pa_equal : pasymbol -> pasymbol -> bool

(** program symbols *)

(* psymbols represent lambda-abstractions. They are polymorphic and
   can be type-instantiated in some type variables and regions of
   their type signature. *)

type psymbol = private {
  ps_name  : ident;
  ps_vta   : vty_arrow;
  ps_vars  : varset;
  (* this varset covers the type variables and regions of the defining
     lambda that cannot be instantiated. Every other type variable
     and region in ps_vty is generalized and can be instantiated. *)
  ps_subst : ity_subst;
  (* this substitution instantiates every type variable and region
     in ps_vars to itself *)
}

val ps_equal : psymbol -> psymbol -> bool

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
}

val pl_equal : plsymbol -> plsymbol -> bool

val create_plsymbol : preid -> vty_value list -> vty_value -> plsymbol
  (* FIXME? Effect calculation is hardwired to correspond to constructors
     and projections: mutable arguments are reset, mutable result is read. *)

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
  | PPvar of preid
  | PPlapp of lsymbol * pre_ppattern list
  | PPpapp of plsymbol * pre_ppattern list
  | PPor of pre_ppattern * pre_ppattern
  | PPas of pre_ppattern * preid

val make_ppattern : pre_ppattern -> vty_value -> pvsymbol Mstr.t * ppattern

(** program expressions *)

type pre = term          (* precondition *)
type post                (* postcondition: a formula with a bound variable *)
type xpost = post Mexn.t (* exceptional postconditions *)

val create_post : vsymbol -> term -> post
val open_post : post -> vsymbol * term

type expr = private {
  e_node   : expr_node;
  e_vty    : vty;
  e_effect : effect;
  e_vars   : varset Mid.t;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node = private
  | Elogic  of term
  | Evalue  of pvsymbol
  | Earrow  of pasymbol
  | Einst   of psymbol
  | Eapp    of pasymbol * pvsymbol
  | Elet    of let_defn * expr
  | Erec    of rec_defn list * expr
  | Eif     of pvsymbol * expr * expr
  | Ecase   of pvsymbol * (ppattern * expr) list
  | Eassign of pvsymbol * region * pvsymbol (* mutable pv <- expr *)

and let_defn = private {
  let_var  : let_var;
  let_expr : expr;
}

and let_var =
  | LetV of pvsymbol
  | LetA of pasymbol

and rec_defn = private {
  rec_ps     : psymbol;
  rec_lambda : lambda;
  rec_vars   : varset Mid.t;
}

and lambda = {
  l_args    : pvsymbol list;
  l_variant : variant list; (* lexicographic order *)
  l_pre     : pre;
  l_expr    : expr;
  l_post    : post;
  l_xpost   : xpost;
}

and variant = {
  v_term : term;           (* : tau *)
  v_rel  : lsymbol option; (* tau tau : prop *)
}

val e_label : ?loc:Loc.position -> Slab.t -> expr -> expr
val e_label_add : label -> expr -> expr
val e_label_copy : expr -> expr -> expr

val e_value : pvsymbol -> expr
val e_arrow : pasymbol -> expr

val e_inst : psymbol -> ity_subst -> expr

exception ValueExpected of expr
exception ArrowExpected of expr

exception GhostWrite of expr * region
exception GhostRaise of expr * xsymbol
(* a ghost expression writes in a non-ghost region or raises an exception *)

val e_app : expr -> expr list -> expr
val e_lapp : lsymbol -> expr list -> ity -> expr
val e_plapp : plsymbol -> expr list -> ity -> expr

val create_let_defn : preid -> expr -> let_defn
val create_fun_defn : preid -> lambda -> rec_defn
val create_rec_defn : (psymbol * lambda) list -> rec_defn list

exception StaleRegion of region * ident * expr
(* a previously reset region is associated to an ident occurring in expr.
   In other terms, freshness violation. *)

val e_let : let_defn -> expr -> expr
val e_rec : rec_defn list -> expr -> expr

val e_if : expr -> expr -> expr -> expr
val e_case : expr -> (ppattern * expr) list -> expr

exception Immutable of pvsymbol

val e_assign : expr -> expr -> expr

(* TODO: when should we check for escaping identifiers (regions?)
   in pre/post/xpost/effects? Here or in WP? *)

