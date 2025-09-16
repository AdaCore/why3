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


let read_channel env path file c =
  try
    let sexp = Mysexplib.input_sexp c in
    let ptree = Ptree.mlw_file_of_sexp sexp in
    Typing.type_mlw_file env path file ptree
  with e ->
    let loc = Loc.user_position (String.concat Filename.dir_sep (path@[file])) 0 0 0 0 in
    raise (Loc.Located(loc,e))

let sexp_format = "sexp"

let () = Env.register_format Pmodule.mlw_language sexp_format ["sexp"]
    read_channel ~desc:"WhyML@ code in s-expressions format"
