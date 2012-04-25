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
open Ident
open Ty
open Term
open Mlw_ty

(** program variables *)

(* pvsymbols represent function arguments (then they must be VTvalue's),
   pattern variables (again, VTvalue) or intermediate computation results
   introduced by let-expressions. They cannot be type-instantiated. *)

type pvsymbol = private {
  pv_vs   : vsymbol; (* has a dummy type if pv_vty is an arrow *)
  pv_vty  : vty;
  pv_tvs  : Stv.t;
  pv_regs : Sreg.t;
  (* If pv_vty is a value, these sets coinside with pv_vty.vty_tvs/regs.
     If pv_vty is an arrow, we additionally count all type variables
     and regions of the defining expression, in order to cover effects
     and specification and not overgeneralize. *)
}

val pv_equal : pvsymbol -> pvsymbol -> bool

(* a value-typed pvsymbol to use in function arguments and patterns *)
val create_pvsymbol : preid -> vty_value -> pvsymbol

exception ValueExpected of pvsymbol
exception ArrowExpected of pvsymbol

val vtv_of_pv : pvsymbol -> vty_value
val vta_of_pv : pvsymbol -> vty_arrow

(** program symbols *)

(* psymbols represent lambda-abstractions. They are polymorphic and
   can be type-instantiated in some type variables and regions of
   their type signature. *)

type psymbol = private {
  ps_name  : ident;
  ps_vta   : vty_arrow;
  ps_tvs   : Stv.t;
  ps_regs  : Sreg.t;
  (* these sets cover the type variables and regions of the defining
     lambda that cannot be instantiated. Every other type variable
     and region in ps_vty is generalized and can be instantiated. *)
  ps_subst : ity_subst;
  (* this substitution instantiates every type variable and region
     in ps_tvs and ps_regs to itself *)
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

(* TODO: patterns *)

(** program expressions *)

type pre   = term (* precondition *)
type post  = term (* postcondition *)
type xpost = (vsymbol * post) Mexn.t (* exceptional postconditions *)

type variant = {
  v_term : term;           (* : tau *)
  v_rel  : lsymbol option; (* tau tau : prop *)
}

type expr = private {
  e_node   : expr_node;
  e_vty    : vty;
  e_effect : effect;
  e_tvs    : Stv.t Mid.t;
  e_regs   : Sreg.t Mid.t;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node = private
  | Elogic  of term
  | Evar    of pvsymbol
  | Esym    of psymbol * ity_subst
  | Eapp    of pvsymbol * pvsymbol
  | Elet    of let_defn * expr
  | Erec    of rec_defn list * expr
  | Eif     of pvsymbol * expr * expr
  | Eassign of pvsymbol * pvsymbol (* mutable pv <- expr *)
  | Eany

and let_defn = private {
  ld_pv   : pvsymbol;
  ld_expr : expr;
}

and rec_defn = private {
  rd_ps     : psymbol;
  rd_lambda : lambda;
}

and lambda = {
  l_args    : pvsymbol list;
  l_variant : variant list; (* lexicographic order *)
  l_pre     : pre;
  l_expr    : expr;
  l_post    : post;
  l_xpost   : xpost;
}

val e_label : ?loc:Loc.position -> Slab.t -> expr -> expr
val e_label_add : label -> expr -> expr
val e_label_copy : expr -> expr -> expr

val e_var : pvsymbol -> expr
(* produces Elogic if a value or Evar if an arrow *)

val e_sym : psymbol -> ity_subst -> expr
(* FIXME? We store the substitution in the expr as given, though it could
   be restricted to type variables and regions (both top and subordinate)
   of ps_vta.vta_tvs/regs. *)

exception GhostWrite of expr * region
exception GhostRaise of expr * xsymbol
(* a ghost expression writes in a non-ghost region or raises an exception *)

val e_app : pvsymbol -> pvsymbol -> expr

val create_let_defn : preid -> expr -> let_defn

exception StaleRegion of region * ident * expr
(* a previously reset region is associated to an ident occurring in expr.
   In other terms, freshness violation. *)

val e_let : let_defn -> expr -> expr

(* TODO: when should we check for escaping identifiers (regions?)
   in pre/post/xpost/effects? Here or in WP? *)

(*
val lapp : lsymbol -> expr list -> expr
val papp : psymbol -> expr list -> expr
val app : expr -> expr -> expr
val plet : psymbol -> expr -> expr -> expr
val pletrec : recfun list -> expr -> expr
val pfun : lambda -> expr
val assign : expr -> psymbol -> expr -> expr
*)
