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
val store_env : (env -> 'a) -> 'a registered
val store_clone : (env -> clone -> 'a) -> 'a registered

exception ArgumentNeeded
val apply : 'a registered -> env option -> clone option -> 'a
val apply_trans : 
  'a trans registered -> env option -> clone option -> task -> 'a

val compose : 
  ('a -> 'b) registered -> ('b -> 'c) registered -> ('a -> 'c) registered 
val compose_trans : 
  task trans registered -> 'a trans registered -> 'a trans registered 
val compose_trans_l : 
  task tlist registered -> 'a tlist registered -> 'a tlist registered 

val clear_all : unit -> unit
val clear : 'a registered -> unit
