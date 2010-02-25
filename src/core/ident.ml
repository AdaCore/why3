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

(** Identifiers *)

type ident = {
  id_short : string;    (* non-unique name for string-based lookup *)
  id_long : string;     (* non-unique name for pretty printing *)
  id_origin : origin;   (* origin of the ident *)
  id_tag : int;         (* unique numeric tag *)
}

and origin =
  | User of Loc.position
  | Derived of ident
  | Fresh

module Id = struct
  type t = ident
  let hash id1 = id1.id_tag
  let equal id1 id2 = id1.id_tag == id2.id_tag
  let compare id1 id2 = Pervasives.compare id1.id_tag id2.id_tag
end
module Mid = Map.Make(Id)
module Sid = Set.Make(Id)
module Hid = Hashtbl.Make(Id)

(* constructors *)

let gentag = let r = ref 0 in fun () -> incr r; !r

let create_ident short long origin = {
  id_short  = short;
  id_long   = long;
  id_origin = origin;
  id_tag    = gentag ()
}

let id_fresh sh ln = create_ident sh ln Fresh
let id_derive sh ln id = create_ident sh ln (Derived id)
let id_clone id = create_ident id.id_short id.id_long (Derived id)
let id_user sh ln loc = create_ident sh ln (User loc)

(** Unique names for pretty printing *)

type printer = (string, int) Hashtbl.t * (int, string) Hashtbl.t

let create_printer _ = Hashtbl.create 1997, Hashtbl.create 1997

let rec find_index indices name ind =
  if Hashtbl.mem indices (name ^ string_of_int ind)
  then find_index indices name (succ ind) else ind

let find_unique indices name =
  try
    let ind = Hashtbl.find indices name + 1 in
    let ind = find_index indices name ind in
    let _ = Hashtbl.add indices name ind in
    name ^ string_of_int ind
  with Not_found ->
    name

let id_unique (indices,values) id =
  try Hashtbl.find values id.id_tag
  with Not_found ->
    let name = find_unique indices id.id_long in
    let _ = Hashtbl.add values id.id_tag name in
    let _ = Hashtbl.add indices name 0 in
    name

