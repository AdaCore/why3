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

(** this is a tool to convert tptp files (.p files) to .why files *)

open TptpTree

open Why

open Lexing

open TptpTranslate


(** module to process a single file *)
module Process : sig

  (** deprecated *)
  val printFile : Format.formatter -> string -> string -> string -> unit

  val read_channel : Env.read_channel
end = struct

  let fromInclude = function | Include x -> x | _ -> assert false
  let isInclude = function | Include _ -> true | _ -> false

  (** report errors *)
  let () = Exn_printer.register (fun fmt exn -> match exn with
    | TptpLexer.LexicalError (s, pos) ->
      Format.fprintf fmt "lexical error: %a@." TptpLexer.report (s, pos)
    | TptpParser.Error ->
      Format.fprintf fmt "syntax error.@." (*TODO : find how to report pos*)
    | e -> raise e)

  (** for a given file, returns the list of declarations
  for this file and all the files it includes, recursively *)
  let rec getAllDecls ?first:(first=false) include_dir filename =
    try
      let filename = if first then filename else include_dir^"/"^filename in
      let input = if filename = "-" then stdin else open_in filename in
      let decls = myparse input in
      close_in input;
      process_recursively ~include_dir:include_dir decls
    with (Sys_error _) as e ->
      print_endline ("error : unable to open "^filename);
      raise e
  (** read completely a channel *)
  and getDeclsFromChan input =
    let decls = myparse input in
    process_recursively decls
  (** search a list of declarations for include statements *)
  and process_recursively ?(include_dir=".") decls =
    let (to_include, real_decl) = List.partition isInclude decls in
    let to_include = List.map fromInclude to_include in (* remove Include *)
    let all_decls = List.concat
      (List.map (getAllDecls include_dir) to_include) in
    all_decls @ real_decl

  (** parses a single file *)
  and myparse chan =
    let lb = Lexing.from_channel chan in
    TptpParser.tptp TptpLexer.token lb


  let read_channel
  ?(debug=false) ?(parse_only=false) ?(type_only=false) _env file c =
    if debug then Format.eprintf "tptp2why : starts parsing %s@." file;
    let decls = getDeclsFromChan c in
    if parse_only || type_only then Theory.Mnm.empty else
      let my_theory = theory_of_decls file decls in
      Theory.Mnm.add "Tptp" my_theory Theory.Mnm.empty


  (** process a single file and all includes inside *)
  let printFile fmter include_dir theoryName filename =
    let decls = getAllDecls ~first:true include_dir filename in
    let theory = TptpTranslate.theory_of_decls theoryName decls in
    (* Format.eprintf "translation done@."; *)
    Pretty.print_theory fmter theory

end



(*s main function and arg parsing *)



(** module for options processing *)
(*module Init = struct

  let input_files = ref []
  let output_chan = ref (Format.formatter_of_out_channel stdout)
  let include_dir = ref "."

  let output_updater filename = if filename <> "-"
    then output_chan := Format.formatter_of_out_channel (open_out filename)
    else ()

  let include_updater s = include_dir := s

  let options = [
    ("-o", String output_updater, "outputs to a file");
    ("-I", String include_updater, "search for included files in this dir");
    ("-", Unit (fun () -> input_files := "-" :: !input_files), "reads from stdin")
  ]

  let usage = "tptp2why [file1|-] [file2...] [-o file] [-I dir]
  It parses tptp files (fof or cnf format) and prints a why file
  with one theory per input file."

end

open Init *)

(** read options, and process each input file accordingly *)
(* let () =
  parse options (fun file -> input_files := file :: (!input_files)) usage;
  input_files := List.rev !input_files;
  let theoryCounter = ref 0 in
  List.iter
    (fun x -> let theoryName = "Theory"^(string_of_int !theoryCounter) in
              incr theoryCounter;
              Process.printFile !output_chan !include_dir theoryName x)
    !input_files *)


(** register as a .p/.ax file parser *)
let () = Env.register_format "tptp" ["p"] Process.read_channel


(*
Local Variables: 
compile-command: "unset LANG; make -C ../.."
End: 
*)
