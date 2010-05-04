(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* main module for whyl *)

open Format
open Why

let files = ref []
let parse_only = ref false
let type_only = ref false
let debug = ref false
let loadpath = ref []

let () = 
  Arg.parse 
    ["--parse-only", Arg.Set parse_only, "stops after parsing";
     "--type-only", Arg.Set type_only, "stops after type-checking";
     "--debug", Arg.Set debug, "sets the debug flag";
     "-I", Arg.String (fun s -> loadpath := s :: !loadpath), 
       "<dir>  adds dir to the loadpath";
    ]
    (fun f -> files := f :: !files)
    "usage: whyl [options] files..."

let rec report fmt = function
  | Lexer.Error e ->
      fprintf fmt "lexical error: %a" Lexer.report e;
  | Pgm_lexer.Error e ->
      fprintf fmt "lexical error: %a" Pgm_lexer.report e;
  | Loc.Located (loc, e) ->
      fprintf fmt "%a%a" Loc.report_position loc report e
  | Parsing.Parse_error ->
      fprintf fmt "syntax error"
  | Typing.Error e ->
      Typing.report fmt e
  | Pgm_typing.Error e ->
      Pgm_typing.report fmt e
  | Denv.Error e ->
      Denv.report fmt e
  | e ->
      raise e
(*       fprintf fmt "anomaly: %s" (Printexc.to_string e) *)

open Pgm_ptree
open Theory

let env = Env.create_env (Typing.retrieve !loadpath)

let type_file file =
  let c = open_in file in
  let lb = Lexing.from_channel c in
  Loc.set_file file lb;
  let p = Pgm_lexer.parse_file lb in 
  close_in c;
  if !parse_only then raise Exit;
  let uc = Theory.create_theory (Ident.id_fresh "Pgm") in
  let th = Env.find_theory env ["programs"] "Prelude" in
  let uc = Theory.use_export uc th in
  let _uc, _dl = Pgm_typing.file env uc p in
  ()

let handle_file file =
  try
    type_file file
  with Exit -> 
    ()

let () =
  try
    List.iter handle_file !files
  with e when not !debug ->
    eprintf "%a@." report e;
    exit 1

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
