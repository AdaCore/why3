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

open Why3

let includes = ref []
let files = Queue.create ()
let opt_version = ref false
let output_dir = ref ""
let allow_obsolete = ref true
let opt_config = ref None


let spec = Arg.align [
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> add s to loadpath") ;
  ("-v",
   Arg.Set opt_version,
   " print version information") ;
  ("-o",
   Arg.Set_string output_dir,
   " the directory to output the files");
  ("--strict",
   Arg.Clear allow_obsolete,
   " forbid obsolete session");
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
]


let version_msg = Format.sprintf
  "Why3 html session output, version %s (build date: %s)"
  Config.version Config.builddate

let usage_str = Format.sprintf
  "Usage: %s [options] [<file.why>|<project directory>] ... "
  (Filename.basename Sys.argv.(0))

let set_file f = Queue.push f files

let () = Arg.parse spec set_file usage_str

let () =
  if !opt_version then begin
    Format.printf "%s@." version_msg;
    exit 0
  end

let output_dir =
  if !output_dir = "" then begin
    Format.printf "output_dir must be set@.";
    exit 0
  end
  else !output_dir


let allow_obsolete = !allow_obsolete
let includes = List.rev !includes

open Session_ro

let env = read_config ~includes !opt_config

open Format
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

let run_file f =
  let session_path = get_project_dir f in
  let session = read_project_dir ~allow_obsolete ~env session_path in
  let basename = Filename.basename session_path in
  let cout = open_out (Filename.concat output_dir (basename^".html")) in
  let fmt = formatter_of_out_channel cout in
  fprintf fmt
    "<!DOCTYPE html
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
print_session session


let () = Queue.iter run_file files
