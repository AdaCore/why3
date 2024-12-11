(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format

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

let int = pp_print_int
let bool fmt b = fprintf fmt "%b" b
let float fmt f = fprintf fmt "%g" f

let rec seq pr fmt = function
  | [] -> ()
  | [v] -> pr fmt v
  | h::t ->
      pr fmt h;
      Format.fprintf fmt ",@ ";
      seq pr fmt t

let list pr fmt l =
  fprintf fmt "@[<hv 1>[%a]@]" (seq pr) l

type json =
  | Record of (string * json) list
  | List of json list
  | String of string
  | Int of int
  | Float of float
  | Bool of bool
  | Null

let rec print_json fmt v =
  match v with
  | Record r ->
      (* FIXME: sorting is only needed because tests are doing purely syntactic checks. *)
      let r = List.sort (fun (k1,_) (k2,_) -> String.compare k1 k2) r in
      map_bindings fmt r
  | List l -> list print_json fmt l
  | String s -> string fmt s
  | Int i -> int fmt i
  | Float f -> float fmt f
  | Bool b -> bool fmt b
  | Null -> pp_print_string fmt "null"
and map_binding fmt binding =
  let (key, value) = binding in
  fprintf fmt "@[<hv 1>%a:@ %a@]" string key print_json value
and map_bindings fmt map_bindings =
  fprintf fmt "@[<hv 1>{%a}@]" (seq map_binding) map_bindings


(* Get json fields. Return Not_found if no fields or field missing *)
let get_field j s =
  match j with
  | Record r -> List.assoc s r
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
  | Int n -> float_of_int n
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

let get_string_field j s = get_string (get_field j s)
let get_int_field j s = get_int (get_field j s)
let get_list_field j s = get_list (get_field j s)
let get_float_field j s = get_float (get_field j s)
let get_bool_field j s = get_bool (get_field j s)
