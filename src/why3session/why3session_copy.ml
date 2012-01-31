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
let opt_convert_unknown = ref false

let spec =
  ("--to-prover",
   Arg.String (fun s -> opt_to_prover := Some (read_opt_prover s)),
   " the proof is copied to this new prover")::
  ("--convert-unknown",
   Arg.Set opt_convert_unknown,
   " convert the unknown provers to the most similar known prover.
The converted proof attempt are set to archived.
The archived proof attempt are not converted")::
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

type to_prover =
  | Convert of prover Mprover.t
  | To_prover of prover

let get_to_prover pk session config =
  match pk with
    | Some pk -> To_prover pk
    | None -> (** We are in the case convert-unknown *)
      assert (!opt_convert_unknown);
      let known_provers = get_provers config in
      let provers = get_used_provers session in
      let unknown_provers = Mprover.set_diff provers known_provers in
      let map pu () =
        let _,name,version =
          Session_tools.unknown_to_known_provers known_provers pu in
        match name,version with
          | _,a::_ -> Some a
          | a::_,_ -> Some a
          | _ -> None in
      Convert (Mprover.mapi_filter map unknown_provers)

let run_one env config filters pk fname =
  let env_session,_ =
    read_update_session ~allow_obsolete:false env config fname in
  let to_prover = get_to_prover pk env_session.session config in
  let s = Stack.create () in
  session_iter_proof_attempt_by_filter filters
    (fun pr -> Stack.push pr s) env_session.session;
  Stack.iter (fun pr ->
    try
      if pr.proof_archived then raise Exit;
      let prover = match to_prover with To_prover pk -> pk
        | Convert mprover -> Mprover.find_exn Exit pr.proof_prover mprover
      in
      (** If such a prover already exists on the goal *)
      let exists =
        (PHprover.mem pr.proof_parent.goal_external_proofs prover) in
      let replace = not exists || match !opt_replace with
        | Always -> true | Never -> false
        | Interactive ->
          interactive
            (PHprover.find pr.proof_parent.goal_external_proofs prover)
        | Not_valid ->
          let rm =
            (PHprover.find pr.proof_parent.goal_external_proofs prover) in
          not (proof_verified rm) in
      if replace then
        begin
          ignore (copy_external_proof ~keygen ~prover ~env_session pr);
          match to_prover with To_prover _ -> ()
            | Convert _ -> set_archived pr true
        end
    with Exit -> () (** a known prover or no alternative has been found *)
  ) s;
  save_session env_session.session

let read_to_prover config =
  match !opt_to_prover with
    | None -> None
    | Some fpr ->
      try Some (prover_of_filter_prover config fpr)
      with ProverNotFound (_,id) ->
        eprintf
          "The prover %s is not found in the configuration file %s@."
          id (get_conf_file config);
          exit 1


let run () =
  let env,config,should_exit1 = read_env_spec () in
  let filters,should_exit2 = read_filter_spec config in
  if should_exit1 || should_exit2 then exit 1;
  (** sanitize --to-prover and --convert-unknown *)
  if (!opt_to_prover <> None) = (!opt_convert_unknown) then begin
    eprintf "The option --to-prover@ and@ --convert-unknown@ are@ exclusive@ \
but@ one@ is@ needed.@.";
    exit 1
  end;
  (** get the provers *)
  let pk = read_to_prover config in
  iter_files (run_one env config filters pk)


let cmd =
  { cmd_spec = spec;
    cmd_desc     = "copy proof based on a filter. \
No filter means all the possibilities.";
    cmd_name     = "copy";
    cmd_run      = run;
  }
