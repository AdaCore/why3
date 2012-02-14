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

type pdecl = private {
  pd_node : pdecl_node;
  pd_syms : Sid.t;         (* idents used in declaration *)
  pd_news : Sid.t;         (* idents introduced in declaration *)
  pd_tag  : int;           (* unique tag *)
}

and pdecl_node

type known_map = pdecl Mid.t

val known_id : known_map -> ident -> unit
val known_add_decl : known_map -> pdecl -> known_map
val merge_known: known_map -> known_map -> known_map

