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

type label =
   { label_id : int ;
     label_string : string }

let label_hash (x : label) = Hashtbl.hash x.label_id

let label_equal (a : label) (b : label) = a.label_id = b.label_id

let ht : (string, label) Hashtbl.t = Hashtbl.create 17

let cnt = ref 0

let from_string s =
   try
      Hashtbl.find ht s
   with Not_found ->
      incr cnt;
      let r = { label_id = !cnt ; label_string = s } in
      Hashtbl.add ht s r;
      r

let to_string x = x.label_string

module Lab = StructMake (struct
  type t = label
  let tag id = id.label_id
end)

module Slab = Lab.S
module Mlab = Lab.M

