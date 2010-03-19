(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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
open Env
open Task
open Trans

type 'a trans_reg
type 'a tlist_reg = 'a list trans_reg

val store : (unit -> 'a trans) -> 'a trans_reg
val store_env : (unit -> env -> 'a trans) -> 'a trans_reg
val store_clone : (unit -> env -> clone -> 'a trans) -> 'a trans_reg

exception ArgumentNeeded

val apply_clone : 'a trans_reg -> env -> clone -> task -> 'a
val apply_env : 'a trans_reg -> env -> task -> 'a
val apply : 'a trans_reg -> task -> 'a

val compose : task trans_reg -> 'a trans_reg -> 'a trans_reg 
val compose_l : task tlist_reg -> 'a tlist_reg -> 'a tlist_reg 

(*val conv_res : ('a -> 'b) -> 'a registered -> 'b registered
(* Sould be used only with function working in constant time*)
*)

val singleton : 'a trans_reg -> 'a tlist_reg

val clear_all : unit -> unit
val clear : 'a trans_reg -> unit

val identity_trans : task trans_reg
val identity_trans_l : task tlist_reg
