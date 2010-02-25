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

type t = { tag : int ; name : string }

let fresh =
  let cnt = ref 0 in
  fun t -> 
    let tag = !cnt in
    incr cnt;
    { t with tag = tag }

let from_string s = fresh { name = s; tag = 0}

let equal a b = a.tag = b.tag
let compare a b = Pervasives.compare a.tag b.tag
let hash n = Hashtbl.hash n.tag

let unsafe_to_string n = n.name

let name_map = Hashtbl.create 47

let default_string = "anon"

let strip_numbers s = 
  let rec aux n = 
    if n <= 0 then 0
    else
      match s.[n-1] with
      | '0'..'9' -> aux (n-1)
      | _ -> n in
  let n = aux (String.length s) in
  if n = 0 then default_string else String.sub s 0 n

let fresh_string name = 
  let s = strip_numbers name in
  try
    let i = Hashtbl.find name_map s in
    let s' = s ^ (string_of_int !i) in
    incr i; s'
  with Not_found ->
    let x = ref 1 in
  Hashtbl.add name_map s x;
  s

let to_string n = fresh_string (unsafe_to_string n)

module HT = struct
  type t' = t
  type t = t'
  let equal = equal
  let hash = hash
  let compare = compare
end
module H = Hashtbl.Make (HT)
module M = Map.Make (HT)
module S = Set.Make (HT)

let get_cur_name, reset =
  let current_name_map = H.create 47 in
  let reset () = 
    H.clear current_name_map; 
    Hashtbl.clear name_map in
  let get_name x = 
    try H.find current_name_map x
    with Not_found ->
      let s = to_string x in
      H.add current_name_map x s;
      s in
  get_name, reset

let to_string = get_cur_name
  
let print fmt x = Format.fprintf fmt "%s" (get_cur_name x)

let build_map nl = 
  let m,_ = 
    List.fold_left (fun (m, i) n -> M.add n i m, i + 1) 
      (M.empty, 0) nl in
  m

