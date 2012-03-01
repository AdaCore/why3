(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

(* program symbols *)
type psymbol = private {
  p_name : ident;
  p_tvs  : Stv.t;  (* type variables that cannot be instantiated *)
  p_reg  : Sreg.t; (* regions that cannot be instantiated *)
  p_vty  : vty;
}

val create_psymbol : preid -> Stv.t -> Sreg.t -> vty -> psymbol

val ps_equal : psymbol -> psymbol -> bool

(* program expressions *)

type variant = {
  v_term : term;           (* : tau *)
  v_rel  : lsymbol option; (* tau tau : prop *)
}

type expr = private {
  e_node  : expr_node;
  e_vty   : vty;
  e_eff   : effect;
  e_ghost : bool;
  e_label : Slab.t;
  e_loc   : Loc.position option;
}

and expr_node = private
  | Elogic  of term
  | Esym    of psymbol (* function *)
  | Eapp    of psymbol * expr * cty
  | Elet    of psymbol * expr * expr
  | Eletrec of recfun list * expr
  | Efun    of lambda
  | Eif     of expr * expr * expr
  | Eassign of pvsymbol * psymbol * region * expr (* e1.f<rho> <- e2 *)

and recfun = psymbol * lambda

and lambda = private {
  l_args    : pvsymbol list;
  l_variant : variant list; (* lexicographic order *)
  l_pre     : term;
  l_body    : expr;
  l_post    : term;
  l_xpost   : xpost;
}

val lapp : lsymbol -> expr list -> expr
val papp : psymbol -> expr list -> expr
val app : expr -> expr -> expr
val plet : psymbol -> expr -> expr -> expr
val pletrec : recfun list -> expr -> expr
val pfun : lambda -> expr
val assign : expr -> psymbol -> expr -> expr
