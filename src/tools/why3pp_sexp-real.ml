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
open Sexplib.Sexp

let rec output fmt = function
  | Atom s ->
      if Why3.Util.is_sexp_simple_token s then
        fprintf fmt "%s" s
      else
        fprintf fmt "%S" s
  | List l ->
      let pp_sep fmt () = fprintf fmt "@ " in
      fprintf fmt "@[<hv2>(%a)@]" (pp_print_list ~pp_sep output) l

let why3pp_sexp out mlw_file =
  let sexp = Why3.Ptree.sexp_of_mlw_file mlw_file in
  output (Format.formatter_of_out_channel out) sexp
  (* Functions [Sexplib.Sexp.output*] do not escape brackets and quotes in tokens *)
