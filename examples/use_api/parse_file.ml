(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*

Simple usage of Why3 API: parse and type a mlw source file

can be compiled using

ocamlfind ocamlopt -linkpkg -package why3 parse_file.ml -o parse_file

*)

open Format
open Why3

let file_name =
  if Array.length Sys.argv <> 2 then
    begin
      eprintf "usage: parse_file <file.mlw>@.";
      exit 2;
    end
  else Sys.argv.(1)

let config : Whyconf.config = Whyconf.read_config None

let main : Whyconf.main = Whyconf.get_main config

let env : Env.env = Env.create_env (Whyconf.loadpath main)

let () =
  try
    let _ = Env.read_file Env.mlw_language env file_name in
    printf "Syntax OK@.";
    exit 0
  with
  | Loc.Located(loc, e) ->
    printf "%a: %a@." Loc.gen_report_position loc Exn_printer.exn_printer e
  | e ->
    printf "unlocated error: %s@." (Printexc.to_string e)
