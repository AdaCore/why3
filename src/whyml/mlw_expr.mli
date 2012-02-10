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
type psymbol = private {
  p_ident: ident;
  p_tvs:   Stv.t;
  p_reg:   Sreg.t;
  p_vty:   vty;
  (* pv_ghost: bool; *)
}

val create_psymbol: preid -> Stv.t -> Sreg.t -> vty -> psymbol

(* program expressions *)
(*
  | Letrec of (psymbol * lambda) list * expr
  | Let of pvsymbol * expr * expr
*)

