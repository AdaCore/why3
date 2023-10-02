(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type sexp = Sexplib.Sexp.t

module Std = Sexplib.Std
module Std_big_int = Sexplib_num.Std.Big_int

exception Parse_error of string

let () = Exn_printer.register (fun fmt exn -> match exn with
  | Parse_error msg -> Format.fprintf fmt "Sexp parser syntax error: %s" msg
  | _ -> raise exn)

let input_sexp (c : in_channel) : sexp =
  try
    Sexplib.Sexp.input_sexp c
  with
    Sexplib.Conv.Of_sexp_error(Failure msg,_) ->
      raise (Parse_error msg)

(*
let of_list = function
  | Sexplib.Sexp.List l -> l
  | _ -> invalid_arg "Mysexplib.of_list"
*)


let is_sexp_simple_token s =
  let rec loop i =
    i < 0 || (
      match s.[i] with
      | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '-' ->
          (* Very conservative for compatiblity with python's sexpdata in bench/test_mlw_printer *)
          loop (pred i)
      | _ -> false ) in
  String.length s > 0 && loop (pred (String.length s))

open Format

(* Functions [Sexplib.Sexp.output*] do not escape brackets and quotes in tokens *)
let rec output fmt = function
  | Sexplib.Sexp.Atom s ->
      if is_sexp_simple_token s then
        fprintf fmt "%s" s
      else
        fprintf fmt "%S" s
  | Sexplib.Sexp.List l ->
      let pp_sep fmt () = fprintf fmt "@ " in
      fprintf fmt "@[<hv2>(%a)@]" (pp_print_list ~pp_sep output) l


let sexp_of_string = Std.sexp_of_string

let string_of_sexp = Std.string_of_sexp
