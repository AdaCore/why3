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

open Stdlib
open Util

type label = int

let label_hash (x : label) = x

let label_equal (a : label) (b : label) = a = b

let ht : (string, label) Hashtbl.t = Hashtbl.create 17

let inverse : (label, string) Hashtbl.t = Hashtbl.create 17

let cnt = ref 0

let from_string s =
   try
      Hashtbl.find ht s
   with Not_found ->
      incr cnt;
      let r = !cnt in
      Hashtbl.add ht s r;
      Hashtbl.add inverse r s;
      r

let to_string x = Hashtbl.find inverse x

module Lab = StructMake (struct
  type t = label
  let tag id = id
end)

module Slab = Lab.S
module Mlab = Lab.M


let hash_set s =
   Slab.fold (fun acc x -> Hashcons.combine acc x) s 17

let singleton s =
   Slab.singleton (from_string s)
