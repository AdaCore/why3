(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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

(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config None
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
        let d = Whyconf.load_driver main env p.Whyconf.driver [] in
        (p,d)::acc
      with e ->
        let p = p.Whyconf.prover in
        eprintf "Failed to load driver for %s %s: %a@."
          p.Whyconf.prover_name p.Whyconf.prover_version
          Exn_printer.exn_printer e;
        exit 1)
    provers
    []

(* create an empty session in the current directory *)
let session = Session_itp.empty_session "."
(*
let env_session,_,_ =
  let dummy_session : unit Session.session = Session.create_session "." in
  let ctxt = Session.mk_update_context
    ~allow_obsolete_goals:true
    dummy_keygen
  in
  Session.update_session ~ctxt dummy_session env config
 *)

(* creates a controller on top of this session *)
let controller = Controller_itp.create_controller config env session

(* adds a file in the new session *)
let file : Session_itp.file =
  let file_name = "examples/logic/hello_proof.why" in
  try
    Controller_itp.add_file controller file_name;
    Session_itp.get_file session file_name
  with e ->
    eprintf "@[Error while reading file@ '%s':@ %a@.@]" file_name
      Exn_printer.exn_printer e;
    exit 1

(* explore the theories in that file *)
let theories = Session_itp.file_theories file
let () = eprintf "%d theories found@." (List.length theories)

(* save the session on disk. *)
let () = Session_itp.save_session session


(* add proof attempts for each goals in the theories *)
let add_proofs_attempts g =
  List.iter
    (fun (p,d) ->
      let _pa : Session_itp.proofAttemptID =
        Session_itp.graft_proof_attempt
          ~limit:{Call_provers.empty_limit with
                  Call_provers.limit_time = 5;
                               limit_mem = 1000 }
          session g p.Whyconf.prover
      in ())
    provers

let () =
  List.iter
    (fun th -> List.iter add_proofs_attempts (Session_itp.theory_goals th))
    theories

(* save the session on disk. note: the prover have not been run yet ! *)
let () = Session_itp.save_session session
