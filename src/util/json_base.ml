(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Wstdlib

let char fmt = function
  | '"'  -> pp_print_string fmt "\\\""
  | '\\' -> pp_print_string fmt "\\\\"
  | '\b' -> pp_print_string fmt "\\b"
  | '\n' -> pp_print_string fmt "\\n"
  | '\r' -> pp_print_string fmt "\\r"
  | '\t' -> pp_print_string fmt "\\t"
  | '\012' -> pp_print_string fmt "\\f"
  | '\032' .. '\126' as c -> pp_print_char fmt c
  | c -> fprintf fmt "\\u%04x" (Char.code c)

let string fmt s =
  pp_print_char fmt '"';
  String.iter (char fmt) s;
  pp_print_char fmt '"'

let int fmt d = fprintf fmt "%d" d
let bool fmt b = fprintf fmt "%b" b
let standard_float fmt f = fprintf fmt "%f" f
let float fmt f = fprintf fmt "%g" f

let print_json_field key value_pr fmt value =
  fprintf fmt "@[<hv 1>%a:@ %a@]" string key value_pr value

let list pr fmt l =
  if l = [] then fprintf fmt "[]"
  else
    fprintf fmt "@[<hv 1>%a@]"
      (Pp.print_list_delim ~start:Pp.lsquare ~stop:Pp.rsquare ~sep:Pp.comma pr)
      l

let print_map_binding key_to_str value_pr fmt binding =
  let (key, value) = binding in
  print_json_field (key_to_str key) value_pr fmt value

let map_bindings key_to_str value_pr fmt map_bindings =
  if map_bindings = [] then fprintf fmt "{}"
  else
    fprintf fmt "@[<hv 1>%a@]"
     (Pp.print_list_delim ~start:Pp.lbrace ~stop:Pp.rbrace ~sep:Pp.comma
      (print_map_binding key_to_str value_pr)) map_bindings

(* Convert a list of bindings into a map *)
let convert_record l =
  List.fold_left (fun m (k, x) -> Mstr.add k x m) Mstr.empty l

type json =
  | Record of json Mstr.t
  | Proj of json Mstr.t
  | List of json list
  | String of string
  | Int of int
  | Float of float
  | Bool of bool
  | Null

let rec print_json fmt v =
  match v with
  | Record r -> map_bindings (fun x -> x) print_json fmt (Mstr.bindings r)
  | Proj p -> map_bindings (fun x -> x) print_json fmt (Mstr.bindings p)
  | List l -> list print_json fmt l
  | String s -> string fmt s
  | Int i -> int fmt i
  | Float f -> float fmt f
  | Bool b -> bool fmt b
  | Null -> fprintf fmt "null"


(* Get json fields. Return Not_found if no fields or field missing *)
let get_field j s =
  match j with
  | Record r -> Mstr.find s r
  | _ -> raise Not_found

let get_string j =
  match j with
  | String s -> s
  | _ -> raise Not_found

let get_int j =
  match j with
  | Int n -> n
  | _ -> raise Not_found

let get_list j =
  match j with
  | List l -> l
  | _ -> raise Not_found

let get_float j =
  match j with
  | Float f -> f
  | _ -> raise Not_found

let get_bool j =
  match j with
  | Bool b -> b
  | _ -> raise Not_found

let get_bool_opt j def =
  match j with
  | Bool b -> b
  | _ -> def
