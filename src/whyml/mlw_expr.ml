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

type variant = {
  v_term : term;           (* : tau *)
  v_rel  : lsymbol option; (* tau tau : prop *)
}

(* program symbols *)
type psymbol = {
  p_name : ident;
  p_tvs  : Stv.t;
  p_reg  : Sreg.t;
  p_vty  : vty;
}

let create_psymbol id tvars regs = function
  | VTvalue pv ->
      let pv =
        create_pvsymbol id ?mut:pv.pv_mutable ~ghost:pv.pv_ghost pv.pv_ity in
      { p_name = pv.pv_vs.vs_name;
        p_tvs = tvars; p_reg = regs; p_vty = vty_value pv; }
  | VTarrow _ as vty ->
      (* TODO? check that tvars/regs are in vty *)
      { p_name = id_register id; p_tvs = tvars; p_reg = regs; p_vty = vty; }

let ps_equal : psymbol -> psymbol -> bool = (==)

type expr = private {
  e_node  : expr_node;
  e_vty   : vty;
  e_eff   : effect;
  e_ghost : bool;
  e_label : Slab.t;
  e_loc   : Loc.position option;
}

and expr_node =
  | Elogic  of term
  | Esym    of psymbol (* function *)
  | Eapp    of psymbol * expr
  | Elet    of psymbol * expr * expr
  | Eletrec of recfun list * expr
  | Efun    of lambda
  | Eif     of expr * expr * expr
  | Eassign of pvsymbol * psymbol * region * expr (* e1.f<rho> <- e2 *)

and recfun = psymbol * lambda

and lambda = {
  l_args    : pvsymbol list;
  l_variant : variant list; (* lexicographic order *)
  l_pre     : term;
  l_body    : expr;
  l_post    : term;
  l_xpost   : xpost;
}

let lapp _ = assert false (*TODO*)
let papp _ = assert false (*TODO*)
let app _ = assert false (*TODO*)
let plet _ = assert false (*TODO*)
let pletrec _ = assert false (*TODO*)
let pfun _ = assert false (*TODO*)
let assign _ = assert false (*TODO*)

