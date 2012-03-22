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
open Why3session_lib
open Whyconf
open Format

module S = Session

let opt_print_provers = ref false
let opt_print_edited = ref false
let opt_tree_print = ref false
let opt_project_dir = ref false
let opt_print0 = ref false

let spec =
  ("--provers", Arg.Set opt_print_provers,
   " the prover used in the session are listed" ) ::
  ("--edited-files", Arg.Set opt_print_edited,
   " the edited files used in the session are listed" ) ::
  ("--tree", Arg.Set opt_tree_print,
   " the session is pretty printed in an ascii tree format" ) ::
  ("--dir", Arg.Set opt_project_dir,
   " print the directory of the session" ) ::
  ("--print0", Arg.Set opt_print0,
   " use the null character instead of newline to separate the output of \
--provers and --edited-files" ) ::
  common_options

let run_one fname =
  let project_dir = Session.get_project_dir fname in
  if !opt_project_dir then printf "%s@." project_dir;
  let session = Session.read_session project_dir in
  let sep = if !opt_print0 then Pp.print0 else Pp.newline in
  if !opt_print_provers then
    printf "%a@."
      (Pp.print_iter1 Sprover.iter sep print_prover)
      (S.get_used_provers session);
  if !opt_print_edited then
    S.session_iter_proof_attempt
      (fun pr ->
        Util.option_iter (fun s -> printf "%s%a" s sep ())
          (S.get_edited_as_abs session pr))
      session;
  if !opt_tree_print then
    printf "%a@." S.print_session session

let run () =
  let should_exit1 = read_simple_spec () in
  if should_exit1 then exit 1;
  iter_files run_one


let cmd =
  { cmd_spec = spec;
    cmd_desc = "print informations about session.";
    cmd_name = "info";
    cmd_run  = run;
  }
