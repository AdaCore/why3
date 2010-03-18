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

type 'a registered

val store : (unit -> 'a) -> 'a registered
val store_env : (unit -> env -> 'a) -> 'a registered
val store_clone : (unit -> env -> clone -> 'a) -> 'a registered

exception ArgumentNeeded
val apply0 : 'a registered -> env option -> clone option -> 'a
val apply_clone : 'a registered -> env -> clone -> 'a
val apply_env : 'a registered -> env -> 'a
val apply : 'a registered -> 'a

val apply_trans0 : 
  'a trans registered -> env option -> clone option -> task -> 'a
val apply_trans_clone : 
  'a trans registered -> env -> clone -> task -> 'a
val apply_trans_env : 
  'a trans registered -> env -> task -> 'a
val apply_trans : 
  'a trans registered -> task -> 'a

val compose0 : 
  ('a -> 'b -> 'c) -> 'a registered -> 'b registered -> 'c registered
val compose : 
  ('a -> 'b) registered -> ('b -> 'c) registered -> ('a -> 'c) registered 
val compose_trans : 
  task trans registered -> 'a trans registered -> 'a trans registered 
val compose_trans_l : 
  task tlist registered -> 'a tlist registered -> 'a tlist registered 

val conv_res : ('a -> 'b) -> 'a registered -> 'b registered
(* Sould be used only with function working in constant time*)

val clear_all : unit -> unit
val clear : 'a registered -> unit

val identity_trans : task trans registered
val identity_trans_l : task tlist registered
