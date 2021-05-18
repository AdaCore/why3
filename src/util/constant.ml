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

open Mysexplib.Std [@@warning "-33"]
open Number

(** Construction *)

type constant =
  | ConstInt  of int_constant
  | ConstReal of real_constant
  | ConstStr  of string
[@@deriving sexp_of]

let compare_const ?(structural=true) c1 c2 =
  match c1, c2 with
  | ConstInt { il_kind = k1; il_int = i1 }, ConstInt { il_kind = k2; il_int = i2 } ->
      let c = if structural then Pervasives.compare k1 k2 else 0 in
      if c <> 0 then c else BigInt.compare i1 i2
  | ConstReal { rl_kind = k1; rl_real = r1 }, ConstReal { rl_kind = k2; rl_real = r2 } ->
      let c = if structural then Pervasives.compare k1 k2 else 0 in
      if c <> 0 then c else compare_real ~structural r1 r2
  | _, _ ->
      Pervasives.compare c1 c2

let int_const ?(il_kind=ILitUnk) n =
  ConstInt { il_kind; il_int = n }

let int_const_of_int n =
  int_const (BigInt.of_int n)

let real_const ?(pow2 = BigInt.zero) ?(pow5 = BigInt.zero) i =
  ConstReal { rl_kind = RLitUnk; rl_real = real_value ~pow2 ~pow5 i }

let string_const s =
  ConstStr s

type escape_map = char -> string

let default_escape c = match c with
  | '\\' -> "\\\\"
  | '\n' -> "\\n"
  | '\r' -> "\\r"
  | '\t' -> "\\t"
  | '\b' -> "\\b"
  | '\"'  -> "\\\""
  | '\032' .. '\126' -> Format.sprintf "%c" c
  | '\000' .. '\031'
  | '\127' .. '\255' -> Format.sprintf "\\x%02X" (Char.code c)

let unsupported_escape = fun _ -> assert false

let escape f s =
  let open Buffer in
  let b = create (String.length s) in
  String.iter (fun c -> add_string b (f c)) s;
  contents b

let print_string_constant string_escape fmt s =
  Format.fprintf fmt "\"%s\"" (escape string_escape s)

let print_string_def fmt s =
  print_string_constant default_escape fmt s

let print support string_escape fmt = function
  | ConstInt i  -> print_int_constant support fmt i
  | ConstReal r -> print_real_constant support fmt r
  | ConstStr s  -> print_string_constant string_escape fmt s

let print_def = print full_support default_escape
