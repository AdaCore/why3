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
open Session
open Format

type filter_prover =
  | Prover of Whyconf.prover
  | ProverId of string

(**
   TODO add_transformation,...
**)

let opt_to_prover = ref None

(** Currently doesn't share the configuration of ide *)
type replace = Interactive | Always | Not_valid | Never
let opt_replace = ref Not_valid
let set_replace s () = opt_replace := s

let spec =
  ("--to-prover",
   Arg.String (fun s -> opt_to_prover := Some (read_opt_prover s)),
   " the proof is copied to this new prover")::
  ("--interactive",
   Arg.Unit (set_replace Interactive), " ask before replacing proof_attempt")::
  ("-i",
   Arg.Unit (set_replace Interactive), " same as --interactive")::
  ("--force", Arg.Unit (set_replace Always),
   " force the replacement of proof_attempt")::
  ("-f", Arg.Unit (set_replace Always), " same as --force")::
  ("--conservative", Arg.Unit (set_replace Not_valid),
   " never replace proof which are not obsolete and valid (default)")::
  ("-c", Arg.Unit (set_replace Not_valid), " same as --conservative")::
  ("--never", Arg.Unit (set_replace Never),
   " never replace a proof")::
  ("-n", Arg.Unit (set_replace Never), " same as --never")::
  (filter_spec @ env_spec)

let rec interactive to_remove =
  eprintf "Do you want to replace the external proof %a (y/n)@."
    print_external_proof to_remove;
  let answer = read_line () in
  match answer with
    | "y" -> true
    | "n" -> false
    | _ -> interactive to_remove

let keygen ?parent:_ _ = ()

let run_one env config filters fname =
  let pk = match !opt_to_prover with
    | None ->
      eprintf "You should specify one prover with --to_prover";
      exit 1
    | Some fpr ->
      try prover_of_filter_prover config fpr
      with ProverNotFound (_,id) ->
        eprintf
          "The prover %s is not found in the configuration file %s@."
          id (get_conf_file config);
        exit 1 in
  let env_session,_ =
    read_update_session ~allow_obsolete:false env config fname in
  let s = Stack.create () in
  session_iter_proof_attempt_by_filter filters
    (fun pr -> Stack.push pr s) env_session.session;
  Stack.iter (fun pr ->
    (** If such a prover already exists on the goal *)
    let exists =
      (PHprover.mem pr.proof_parent.goal_external_proofs pk) in
    let replace = not exists || match !opt_replace with
      | Always -> true | Never -> false
      | Interactive ->
        interactive
          (PHprover.find pr.proof_parent.goal_external_proofs pk)
      | Not_valid ->
        let rm = (PHprover.find pr.proof_parent.goal_external_proofs pk) in
        not (proof_verified rm) in
    if replace then
      ignore (copy_external_proof ~keygen ~prover:pk ~env_session pr)
  ) s;
  save_session env_session.session


let run () =
  let env,config,should_exit1 = read_env_spec () in
  let filters,should_exit2 = read_filter_spec config in
  if should_exit1 || should_exit2 then exit 1;
  iter_files (run_one env config filters)


let cmd =
  { cmd_spec = spec;
    cmd_desc     = "copy proof based on a filter. \
No filter means all the possibilities.";
    cmd_name     = "copy";
    cmd_run      = run;
  }
