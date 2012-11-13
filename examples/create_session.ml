(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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
        let d = Driver.load_driver env p.Whyconf.driver [] in
        (p,d)::acc
      with e ->
        let p = p.Whyconf.prover in
        eprintf "Failed to load driver for %s %s: %a@."
          p.Whyconf.prover_name p.Whyconf.prover_version
          Exn_printer.exn_printer e;
        exit 1)
    provers
    []


(* a dummy keygen function for sessions *)
let keygen ?parent () = ()

(* create an empty session in the current directory *)
let env_session,_ =
  let dummy_session : unit Session.session = Session.create_session "." in
  Session.update_session ~keygen ~allow_obsolete:true dummy_session env config

(* adds a file in the new session *)
let file : unit Session.file = 
  let file_name = "examples/hello_proof.why" in
  try
    Session.add_file keygen env_session file_name
  with e ->
    eprintf "@[Error while reading file@ '%s':@ %a@.@]" file_name
      Exn_printer.exn_printer e;
    exit 1

(* explore the theories in that file *)
let theories = file.Session.file_theories 
let () = eprintf "%d theories found@." (List.length theories)

(* add proof attempts for each goals in the theories *)

let add_proofs_attempts g =
  List.iter
    (fun (p,d) ->
      let _pa : unit Session.proof_attempt =
        Session.add_external_proof
          ~keygen
          ~obsolete:true
          ~archived:false
          ~timelimit:5
          ~memlimit:1000
          ~edit:None
          g p.Whyconf.prover Session.Scheduled
      in ()) 
    provers

let () =
  List.iter
    (fun th -> List.iter add_proofs_attempts th.Session.theory_goals)
    theories

(* save the session on disk *)
let () = Session.save_session config env_session.Session.session


