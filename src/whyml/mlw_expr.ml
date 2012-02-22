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
open Mlw_ty

(* program symbols *)
type psymbol = {
  p_ident: ident;
  p_tvs:   Stv.t;
  p_reg:   Sreg.t;
  p_vty:   vty;
  (* pv_ghost: bool; *)
}

let create_psymbol id tvars regs vty =
  (* TODO? check that tvars/regs are in vty *)
  { p_ident = id_register id;
    p_tvs   = tvars;
    p_reg   = regs;
    p_vty   = vty; }

let ps_equal : psymbol -> psymbol -> bool = (==)

type expr = private {
  e_node  : expr_node;
  e_vty   : vty;
  e_eff   : effect;
  e_label : Slab.t;
  e_loc   : Loc.position option;
}

and expr_node
