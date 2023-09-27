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

type sexp = unit

module Std = struct end
module Std_big_int = struct end

exception Parse_error of string

let () = Exn_printer.register (fun fmt exn -> match exn with
  | Parse_error msg -> Format.fprintf fmt "Sexp parser syntax error: %s" msg
  | _ -> raise exn)

let input_sexp (_ : in_channel) : sexp =
  raise (Parse_error "Not compiled with S-expression support")

let output (_ : Format.formatter) (_ : sexp) : unit =
  raise (Parse_error "Not compiled with S-expression support")
