(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

open Format
open Why3

let includes = ref []
let files = Queue.create ()
let opt_version = ref false
let output_dir = ref ""
let allow_obsolete = ref true
let opt_config = ref None
let opt_context = ref false


let spec = Arg.align [
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> Add s to loadpath") ;
  ("-v",
   Arg.Set opt_version,
   " Print version information") ;
  ("-o",
   Arg.Set_string output_dir,
   " The directory to output the files ('-' for stdout)");
  ("--strict",
   Arg.Clear allow_obsolete,
   " Forbid obsolete session");
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " Same as -C";
  "--context", Arg.Set opt_context,
  " Add context around the generated code in order to allow direct \
    visualisation (header, css, ...). It also add in the directory \
    all the needed external file. It can't be set with stdout output";
]


let version_msg = sprintf
  "Why3 html session output, version %s (build date: %s)"
  Config.version Config.builddate

let usage_str = sprintf
  "Usage: %s [options] [<file.why>|<project directory>] ... "
  (Filename.basename Sys.argv.(0))

let set_file f = Queue.push f files

let () = Arg.parse spec set_file usage_str

let () =
  if !opt_version then begin
    printf "%s@." version_msg;
    exit 0
  end

let output_dir =
  match !output_dir with
    | "" -> printf
      "Error: output_dir must be set@.";
      exit 1
    | "-" when !opt_context ->
      printf
        "Error: context and stdout output can't be set at the same time@.";
      exit 1
    | _ -> !output_dir

let allow_obsolete = !allow_obsolete
let includes = List.rev !includes

open Session_ro

let env = read_config ~includes !opt_config

open Util

let print_prover fmt = function
  | Detected_prover pd -> fprintf fmt "%s" pd.prover_name
  | Undetected_prover s -> fprintf fmt "%s" s

let print_proof_status fmt = function
  | Undone -> fprintf fmt "Undone"
  | Done pr -> fprintf fmt "Done : %a" Call_provers.print_prover_result pr
  | InternalFailure exn ->
    fprintf fmt "Failure : %a"Exn_printer.exn_printer exn

let print_proof_attempt fmt pa =
  fprintf fmt "<il>%a : %a</il>"
    print_prover pa.prover
    print_proof_status pa.proof_state

let rec print_transf fmt tr =
  fprintf fmt "<il>%s : <ul>%a</ul></il>"
    tr.transf_name
    (Pp.print_list Pp.newline print_goal) tr.subgoals

and print_goal fmt g =
  fprintf fmt "<il>%s : <ul>%a%a</ul></il>"
    g.goal_name
    (Pp.print_iter2 Mstr.iter Pp.newline Pp.nothing
       Pp.nothing print_proof_attempt)
    g.external_proofs
    (Pp.print_iter2 Mstr.iter Pp.newline Pp.nothing
       Pp.nothing print_transf)
    g.transformations

let print_theory fmt th =
  fprintf fmt "<il>%s : <ul>%a</ul></il>"
    th.theory_name
    (Pp.print_list Pp.newline print_goal) th.goals

let print_file fmt f =
  fprintf fmt "<il>%s : <ul>%a</ul></il>"
    f.file_name
    (Pp.print_list Pp.newline print_theory) f.theories

let print_session fmt s =
  fprintf fmt "<p><ul>%a</ul></p>"
    (Pp.print_list Pp.newline print_file) s

type context =
    ((formatter -> Session_ro.session -> unit)
     -> Session_ro.session -> unit, formatter, unit) format

let simple_context : context = "<!DOCTYPE html
PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">
<head>
<title>A template for why3html</title>
</head>
<body>
%a
</body>
</html>
"

let run_file f =
  let session_path = get_project_dir f in
  let session = read_project_dir ~allow_obsolete ~env session_path in
  let cout = if output_dir = "-" then stdout else
      let basename = Filename.basename session_path in
      open_out (Filename.concat output_dir (basename^".html")) in
  let fmt = formatter_of_out_channel cout in
  if !opt_context
  then fprintf fmt simple_context print_session session
  else print_session fmt session;
  pp_print_flush fmt ();
  if output_dir <> "-" then close_out cout


let () = Queue.iter run_file files
