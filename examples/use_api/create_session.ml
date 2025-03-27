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

(*******************

This file builds a new session from a given file.

To each goal is added as many proof attempts as provers
found in the configuration.


******************)

open Format

(* opening the Why3 library *)
open Why3

(* access to the Why configuration *)

(* reads the default config file *)
let config = Whyconf.init_config None
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

(* loading the drivers *)
let provers =
  Whyconf.Mprover.fold
    (fun _ p acc ->
      try
        let d = Driver.load_driver_for_prover main env p in
        (p,d)::acc
      with e ->
        let p = p.Whyconf.prover in
        eprintf "Failed to load driver for %s %s: %a@."
          p.Whyconf.prover_name p.Whyconf.prover_version
          Exn_printer.exn_printer e;
        exit 1)
    provers
    []

(* default resource limits *)
let limits =
  Call_provers.{empty_limits with
                limit_time = Whyconf.timelimit main;
                limit_mem = Whyconf.memlimit main }

(* create an empty session in the current directory *)
let session = Session_itp.empty_session "."

(* creates a controller on top of this session *)
let controller = Controller_itp.create_controller config env session

(* adds a file in the new session *)
let file : Session_itp.file =
  let file_name = "examples/logic/hello_proof.why" in
  try
    Controller_itp.add_file controller file_name;
    let path = Sysutil.relativize_filename (Session_itp.get_dir session) file_name in
    Session_itp.find_file_from_path session path
  with
  | Controller_itp.Errors_list le ->
      eprintf "@[Error while reading file@ '%s':@ %a@.@]" file_name
              (Pp.print_list Pp.space Exn_printer.exn_printer) le;
      exit 1

(* explore the theories in that file *)
let theories = Session_itp.file_theories file
let () = printf "%d theories found in session@." (List.length theories)

(* save the session on disk. *)
let () = Session_itp.save_session session


(* add proof attempts for each goals in the theories *)
let add_proofs_attempts g =
  List.iter
    (fun (p,_driver) ->
      let _pa : Session_itp.proofAttemptID =
        Session_itp.graft_proof_attempt
          ~limits session g p.Whyconf.prover
      in ())
    provers

let () =
  List.iter
    (fun th -> List.iter add_proofs_attempts (Session_itp.theory_goals th))
    theories

(* save the session on disk. note: the prover have not been run yet ! *)
let () = Session_itp.save_session session
