(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)
open Why3

(* printing *)

open Format
open Pp

let usage = "why3_ptree <optional \"term\" or \"decl\"> <string|file>"

module J = struct
  let log ?(level=0) = Format.printf
  let fatal ?(level=0) = log
  let result ?(level=0) = log
end

let error e= J.log "error : %s : %s\n" e usage

let () =
  try
    match Array.length Sys.argv with
    | 2 ->
        let ast = let lb = Lexing.from_channel (open_in Sys.argv.(1)) in Lexer.parse_mlw_file lb in
        J.log "%a@." Why3ml_pp.Output_ast.print_mlw_file ast;
        J.log "\n";
        J.log "%a@." Why3ml_pp.Output_mlw.print_mlw_file ast
    | 3 ->
        let arg = Sys.argv.(2) in (
          match Sys.argv.(1) with
          | "term" ->
              let ast = let lb = Lexing.from_string arg in Lexer.parse_term lb in
              J.log "%a@." Why3ml_pp.Output_ast.print_term ast;
              J.log "\n";
              J.log "%a@." Why3ml_pp.Output_mlw.print_term ast
          | "decl" ->
              let ast = let lb = Lexing.from_string arg in Lexer.parse_decl lb in
              J.log "%a@." Why3ml_pp.Output_ast.print_decl ast;
              J.log "\n";
              J.log "%a@." Why3ml_pp.Output_mlw.print_decl ast
          | _ -> error "" )
    | _ -> error ""
  with
  | Invalid_argument e -> error e
