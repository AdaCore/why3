(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

let string fmt s =
  let b = Buffer.create (2 * String.length s) in
  Buffer.add_char b '"';
  for i = 0 to String.length s -1 do
    match s.[i] with
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | c -> Buffer.add_char b c
  done;
  Buffer.add_char b '"';
  Format.fprintf fmt "%s" (Buffer.contents b)

let int fmt d = Format.fprintf fmt "%d" d
let bool fmt b = Format.fprintf fmt "%b" b

let print_json_field key value_pr fmt value =
  Format.fprintf fmt "%a : %a " string key value_pr value

let list pr fmt l =
  if l = [] then Format.fprintf fmt "[]"
  else
    Pp.print_list_delim ~start:Pp.lsquare ~stop:Pp.rsquare ~sep:Pp.comma
      pr fmt l

let print_map_binding key_to_str value_pr fmt binding =
  let (key, value) = binding in
  print_json_field (key_to_str key) value_pr fmt value

let map_bindings key_to_str value_pr fmt map_bindings =
  if map_bindings = [] then Format.fprintf fmt "{}"
  else
    Pp.print_list_delim ~start:Pp.lbrace ~stop:Pp.rbrace ~sep:Pp.comma
      (print_map_binding key_to_str value_pr) fmt map_bindings
