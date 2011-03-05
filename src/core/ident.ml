(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

(** Labels *)

type label = string * Loc.position option

let label ?loc s = (s,loc)

(** Identifiers *)

type ident = {
  id_string : string;       (* non-unique name *)
  id_origin : origin;       (* origin of the ident *)
  id_label  : label list;   (* identifier labels *)
  id_tag    : Hashweak.tag; (* unique magical tag *)
}

and origin =
  | User of Loc.position
  | Derived of ident
  | Fresh

module Id = WeakStructMake (struct
  type t = ident
  let tag id = id.id_tag
end)

module Sid = Id.S
module Mid = Id.M
module Hid = Id.H

type preid = ident

let id_equal : ident -> ident -> bool = (==)

let id_hash id = Hashweak.tag_hash id.id_tag

(* constructors *)

let id_register = let r = ref 0 in fun id ->
  { id with id_tag = (incr r; Hashweak.create_tag !r) }

let create_ident name origin labels = {
  id_string = name;
  id_origin = origin;
  id_label  = labels;
  id_tag    = Hashweak.dummy_tag;
}

let id_fresh ?(labels = []) nm = create_ident nm Fresh labels
let id_user ?(labels = []) nm loc =
  let new_loc = ref loc in
  let new_labels = List.fold_left
    (fun acc ((s,l) as lab) ->
       match l with
	 | None -> lab :: acc
	 | Some loc -> 
	     new_loc := loc; 
	     match s with
	       | "" -> acc
	       | _ -> lab :: acc)
    [] labels
  in
  create_ident nm (User !new_loc) new_labels

let id_derive ?(labels = []) nm id = create_ident nm (Derived id) labels

let id_clone ?(labels = []) id =
  create_ident id.id_string (Derived id) (labels @ id.id_label)

let id_dup ?(labels = []) id =
  create_ident id.id_string id.id_origin (labels @ id.id_label)

let rec id_derived_from i1 i2 = id_equal i1 i2 ||
  (match i1.id_origin with
    | Derived i3 -> id_derived_from i3 i2
    | _ -> false)

let rec id_from_user i =
  match i.id_origin with
    | Derived i -> id_from_user i
    | User l -> Some l
    | Fresh -> None

(** Unique names for pretty printing *)

type ident_printer = {
  indices   : (string, int) Hashtbl.t;
  values    : string Hid.t;
  sanitizer : string -> string;
  blacklist : string list;
}

let rec find_index indices name ind =
  if Hashtbl.mem indices (name ^ string_of_int ind)
  then find_index indices name (succ ind) else ind

let find_unique indices name =
  let name = try
    let ind = Hashtbl.find indices name + 1 in
    let ind = find_index indices name ind in
    Hashtbl.replace indices name ind;
    name ^ string_of_int ind
  with Not_found -> name in
  Hashtbl.replace indices name 0;
  name

let reserve indices name = ignore (find_unique indices name)

let same x = x

let create_ident_printer ?(sanitizer = same) sl =
  let indices = Hashtbl.create 1997 in
  List.iter (reserve indices) sl;
  { indices   = indices;
    values    = Hid.create 1997;
    sanitizer = sanitizer;
    blacklist = sl }

let id_unique printer ?(sanitizer = same) id =
  try
    Hid.find printer.values id
  with Not_found ->
    let name = sanitizer (printer.sanitizer id.id_string) in
    let name = find_unique printer.indices name in
    Hid.replace printer.values id name;
    name

let string_unique printer s = find_unique printer.indices s

let forget_id printer id =
  try
    let name = Hid.find printer.values id in
    Hashtbl.remove printer.indices name;
    Hid.remove printer.values id
  with Not_found -> ()

let forget_all printer =
  Hid.clear printer.values;
  Hashtbl.clear printer.indices;
  List.iter (reserve printer.indices) printer.blacklist

(** Sanitizers *)

let unsanitizable = Debug.register_flag "unsanitizable"

let char_to_alpha c = match c with
  | 'a'..'z' | 'A'..'Z' -> String.make 1 c
  | ' ' -> "sp" | '_'  -> "us" | '#' -> "sh"
  | '`' -> "bq" | '~'  -> "tl" | '!' -> "ex"
  | '@' -> "at" | '$'  -> "dl" | '%' -> "pc"
  | '^' -> "cf" | '&'  -> "et" | '*' -> "as"
  | '(' -> "lp" | ')'  -> "rp" | '-' -> "mn"
  | '+' -> "pl" | '='  -> "eq" | '[' -> "lb"
  | ']' -> "rb" | '{'  -> "lc" | '}' -> "rc"
  | ':' -> "cl" | '\'' -> "qt" | '"' -> "dq"
  | '<' -> "ls" | '>'  -> "gt" | '/' -> "sl"
  | '?' -> "qu" | '\\' -> "bs" | '|' -> "br"
  | ';' -> "sc" | ','  -> "cm" | '.' -> "dt"
  | '0' -> "zr" | '1'  -> "un" | '2' -> "du"
  | '3' -> "tr" | '4'  -> "qr" | '5' -> "qn"
  | '6' -> "sx" | '7'  -> "st" | '8' -> "oc"
  | '9' -> "nn" | '\n' -> "br"
  | _ ->
    Debug.dprintf unsanitizable "Unsanitizable : '%c' can't be sanitized@." c;
    "zz"

let char_to_lalpha c = String.uncapitalize (char_to_alpha c)
let char_to_ualpha c = String.capitalize (char_to_alpha c)

let char_to_alnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_alpha c

let char_to_alnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_alnum c

let sanitizer head rest n =
  let lst = ref [] in
  let code c = lst := rest c :: !lst in
  let n = if n = "" then "zilch" else n in
  String.iter code n;
  let rst = List.tl (List.rev !lst) in
  let cs = head (String.get n 0) :: rst in
  String.concat "" cs
