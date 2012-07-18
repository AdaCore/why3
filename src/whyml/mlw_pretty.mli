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

open Format
open Why3
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl

val forget_all      : unit -> unit     (* flush id_unique *)
val forget_regs     : unit -> unit     (* flush id_unique for regions *)
val forget_tvs_regs : unit -> unit     (* flush for type vars and regions *)

val forget_pv : pvsymbol -> unit (* flush for a program variable *)
val forget_ps : psymbol  -> unit (* flush for a program symbol *)

val print_xs  : formatter -> xsymbol -> unit      (* exception symbol *)

val print_reg : formatter -> region -> unit       (* region *)
val print_its : formatter -> itysymbol -> unit    (* type symbol *)
val print_ity : formatter -> ity -> unit          (* individual type *)

val print_vtv : formatter -> vty_value -> unit    (* value type *)
val print_vta : formatter -> vty_arrow -> unit    (* arrow type *)
val print_vty : formatter -> vty -> unit          (* expression type *)

val print_pv   : formatter -> pvsymbol -> unit    (* program variable *)
val print_pvty : formatter -> pvsymbol -> unit    (* pvsymbol : type *)
val print_ps   : formatter -> psymbol  -> unit    (* program symbol *)
val print_psty : formatter -> psymbol  -> unit    (* psymbol : type *)

val print_effect : formatter -> effect -> unit    (* effect *)

val print_ppat : formatter -> ppattern -> unit    (* program patterns *)

val print_expr : formatter -> expr -> unit        (* expression *)

val print_pdecl : formatter -> pdecl -> unit
