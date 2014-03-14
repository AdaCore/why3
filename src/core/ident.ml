(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib

(** Labels *)

type label = {
  lab_string : string;
  lab_tag    : int;
}

module Lab = MakeMSH (struct
  type t = label
  let tag lab = lab.lab_tag
end)

module Slab = Lab.S
module Mlab = Lab.M

module Hslab = Hashcons.Make (struct
  type t = label
  let equal lab1 lab2 = lab1.lab_string = lab2.lab_string
  let hash lab = Hashtbl.hash lab.lab_string
  let tag n lab = { lab with lab_tag = n }
end)

let create_label s = Hslab.hashcons {
  lab_string = s;
  lab_tag    = -1
}

let lab_equal : label -> label -> bool = (==)
let lab_hash lab = lab.lab_tag
let lab_compare l1 l2 = Pervasives.compare l1.lab_tag l2.lab_tag

(** Identifiers *)

type ident = {
  id_string : string;               (* non-unique name *)
  id_label  : Slab.t;               (* identifier labels *)
  id_loc    : Loc.position option;  (* optional location *)
  id_tag    : Weakhtbl.tag;         (* unique magical tag *)
}

module Id = MakeMSHW (struct
  type t = ident
  let tag id = id.id_tag
end)

module Sid = Id.S
module Mid = Id.M
module Hid = Id.H
module Wid = Id.W

type preid = {
  pre_name  : string;
  pre_label : Slab.t;
  pre_loc   : Loc.position option;
}

let id_equal : ident -> ident -> bool = (==)
let id_hash id = Weakhtbl.tag_hash id.id_tag
let id_compare id1 id2 = Pervasives.compare (id_hash id1) (id_hash id2)

(* constructors *)

let id_register = let r = ref 0 in fun id -> {
  id_string = id.pre_name;
  id_label  = id.pre_label;
  id_loc    = id.pre_loc;
  id_tag    = (incr r; Weakhtbl.create_tag !r);
}

let create_ident name labels loc = {
  pre_name  = name;
  pre_label = labels;
  pre_loc   = loc;
}

let id_fresh ?(label = Slab.empty) ?loc nm =
  create_ident nm label loc

let id_user ?(label = Slab.empty) nm loc =
  create_ident nm label (Some loc)

let id_clone ?(label = Slab.empty) id =
  let ll = Slab.union label id.id_label in
  create_ident id.id_string ll id.id_loc

let id_derive ?(label = Slab.empty) nm id =
  let ll = Slab.union label id.id_label in
  create_ident nm ll id.id_loc

let preid_name id = id.pre_name

(** Unique names for pretty printing *)

type ident_printer = {
  indices   : int Hstr.t;
  values    : string Hid.t;
  sanitizer : string -> string;
  blacklist : string list;
}

let find_unique indices name =
  let specname ind = name ^ string_of_int ind in
  let testname ind = Hstr.mem indices (specname ind) in
  let rec advance ind =
    if testname ind then advance (succ ind) else ind in
  let rec retreat ind =
    if ind = 1 || testname (pred ind) then ind else retreat (pred ind) in
  let fetch ind =
    if testname ind then advance (succ ind) else retreat ind in
  let name = try
    let ind = fetch (succ (Hstr.find indices name)) in
    Hstr.replace indices name ind;
    specname ind
  with Not_found -> name in
  Hstr.replace indices name 0;
  name

let reserve indices name = ignore (find_unique indices name)

let same x = x

let create_ident_printer ?(sanitizer = same) sl =
  let indices = Hstr.create 1997 in
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
    Hstr.remove printer.indices name;
    Hid.remove printer.values id
  with Not_found -> ()

let forget_all printer =
  Hid.clear printer.values;
  Hstr.clear printer.indices;
  List.iter (reserve printer.indices) printer.blacklist

(** Sanitizers *)

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
  | '9' -> "nn" | '\n' -> "br" |  _  -> "zz"

let char_to_lalpha c = String.uncapitalize (char_to_alpha c)
let char_to_ualpha c = String.capitalize (char_to_alpha c)

let char_to_alnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_alpha c

let char_to_lalnum c =
  match c with '0'..'9' -> String.make 1 c | _ -> char_to_lalpha c

let char_to_alnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_alnum c

let char_to_lalnumus c =
  match c with '_' | ' ' -> "_" | _ -> char_to_lalnum c

let sanitizer head rest n =
  let lst = ref [] in
  let code c = lst := rest c :: !lst in
  let n = if n = "" then "zilch" else n in
  String.iter code n;
  let rst = List.tl (List.rev !lst) in
  let cs = head (String.get n 0) :: rst in
  String.concat "" cs
