(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
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

let combine n acc = 
  let r = acc * 65599 + n in
  if r < 0 then
    if r = min_int then max_int
    else 0 - r
  else r

let combine2 n acc1 acc2 = combine n (combine acc1 acc2)
let combine3 n acc1 acc2 acc3 = combine n (combine acc1 (combine acc2 acc3))

let hash_int : int -> int = Hashtbl.hash
let hash_string : string -> int = Hashtbl.hash

module IntMap = 
  Map.Make(struct type t = int let compare = Pervasives.compare end)

open Format
let id x = x
let ksprintf k s =
  ignore(flush_str_formatter ());
  kfprintf (fun _ -> k (flush_str_formatter ())) str_formatter s

let sprintf s = ksprintf id s

let rec print_list sep prf fmt = function
  | [] -> ()
  | [x] -> prf fmt x
  | (x::xs) -> prf fmt x; sep fmt (); print_list sep prf fmt xs

let comma fmt () = pp_print_string fmt ","
