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

val identity   : task trans_reg
val identity_l : task tlist_reg

(** [compose f g] applies [f], then [g] *)
val compose   : task trans_reg -> 'a trans_reg -> 'a trans_reg
val compose_l : task tlist_reg -> 'a tlist_reg -> 'a tlist_reg

val singleton : 'a trans_reg -> 'a tlist_reg

(** Use only with functions working in constant time *)
val conv_res : ('a -> 'b) -> 'a trans_reg -> 'b trans_reg

val clear : 'a trans_reg -> unit

(** Store and apply *)

type query = Driver.driver_query
type clone = Theory.clone_map
type use   = Theory.use_map

val store       : (unit ->                  'a trans) -> 'a trans_reg
val store_env   : (env  ->                  'a trans) -> 'a trans_reg
val store_use   : (env  -> use           -> 'a trans) -> 'a trans_reg
val store_clone : (env  ->         clone -> 'a trans) -> 'a trans_reg
val store_both  : (env  -> use  -> clone -> 'a trans) -> 'a trans_reg

val store_goal  : (env  ->          task -> 'a trans) -> 'a trans_reg
val store_query : (        query ->         'a trans) -> 'a trans_reg
val store_full  : (        query -> task -> 'a trans) -> 'a trans_reg

exception ArgumentNeeded

val apply_driver : 'a trans_reg -> Driver.driver -> task -> 'a
val apply_env : 'a trans_reg -> env -> task -> 'a
val apply : 'a trans_reg -> task -> 'a

(** Registration *)

type printer = query -> Format.formatter -> task -> unit

val register_printer     : string -> printer -> unit
val register_transform   : string -> task trans_reg -> unit
val register_transform_l : string -> task tlist_reg -> unit

val lookup_printer     : string -> printer
val lookup_transform   : string -> task trans_reg
val lookup_transform_l : string -> task tlist_reg

val list_printers     : unit -> string list
val list_transforms   : unit -> string list
val list_transforms_l : unit -> string list

