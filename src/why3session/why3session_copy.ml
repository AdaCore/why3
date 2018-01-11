(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Why3session_lib
open Whyconf
open Session
open Format

(**
   TODO add_transformation,...

   TODO:
    filter_state
    filter_time
    filter_?

**)

(** To prover *)

let opt_to_prover = ref None

(** Currently doesn't share the configuration of ide *)
type replace = Interactive | Always | Not_valid | Never
let opt_replace = ref Not_valid
let set_replace s () = opt_replace := s


let opt_to_known = ref false

let tobe_archived = ref None
let set_opt_archived () = tobe_archived := Some true
let unset_opt_archived () = tobe_archived := Some false

let tobe_obsolete = ref false

let spec =
  ("--set-obsolete", Arg.Set tobe_obsolete,
   " the proof is set to obsolete" ) ::
  ("--set-archive", Arg.Unit set_opt_archived,
   " the proof is set to archive" ) ::
  ("--unset-archive", Arg.Unit unset_opt_archived,
   " the proof attribute archive is unset" ) ::
(*
  ("--to-known-prover",
   Arg.Set opt_to_known,
   " convert the unknown provers to the most similar known prover.")::
*)
  ["--to-prover",
   Arg.String (fun s -> opt_to_prover := Some (read_opt_prover s)),
   " the proof is copied to this new prover";
   "--interactive", Arg.Unit (set_replace Interactive),
   " ask before replacing proof_attempt";
   "-i", Arg.Unit (set_replace Interactive), " same as --interactive";
   "--force", Arg.Unit (set_replace Always),
   " force the replacement of proof_attempt";
   "-f", Arg.Unit (set_replace Always), " same as --force";
   "--conservative", Arg.Unit (set_replace Not_valid),
   " never replace proof which are not obsolete and valid (default)";
   "-c", Arg.Unit (set_replace Not_valid), " same as --conservative";
   "--never", Arg.Unit (set_replace Never), " never replace a proof";
   "-n", Arg.Unit (set_replace Never), " same as --never"]@
    (force_obsolete_spec @ filter_spec @ common_options)

type action =
  | Copy
  | CopyArchive
  | Mod

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
  | SameProver

let get_to_prover pk session config =
  match pk with
    | Some pk -> To_prover pk
    | None when !opt_to_known
           -> (* We are in the case --to-known-prover *)
      assert (!opt_to_known);
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
    | None -> SameProver

exception NoAlt

let run_one ~action env config filters pk fname =
  let env_session,_,_ =
    read_update_session ~allow_obsolete:!opt_force_obsolete env config fname in
  let to_prover = get_to_prover pk env_session.session config in
  let s = Stack.create () in
  session_iter_proof_attempt_by_filter filters
    (fun pr -> Stack.push pr s) env_session.session;
  Stack.iter (fun pr ->
    try
      let prover = match to_prover with To_prover pk -> Some pk
        | Convert mprover ->
          Some (Mprover.find_exn NoAlt pr.proof_prover mprover)
        | SameProver -> None
      in
      let prn = match prover with
        | None -> pr
        | Some prover ->
      (* If such a prover already exists on the goal *)
          let exists =
            (PHprover.mem (goal_external_proofs pr.proof_parent) prover) in
          let replace = not exists || match !opt_replace with
            | Always -> true | Never -> false
            | Interactive ->
              interactive
                (PHprover.find (goal_external_proofs pr.proof_parent) prover)
            | Not_valid ->
              let rm =
                PHprover.find (goal_external_proofs pr.proof_parent) prover
              in
              not (Opt.inhabited (proof_verified rm))
          in
          if not replace then raise Exit;
          copy_external_proof ~keygen ~prover ~env_session pr
      in
      if !tobe_obsolete then set_obsolete prn;
      begin match !tobe_archived with
        | None -> ()
        | Some b -> set_archived prn b end;
      raise Exit
    with
      | NoAlt -> () (* a known prover or no alternative has been found *)
      | Exit  ->    (* normal or existing prover not replaced *)
        match action with
          | CopyArchive -> set_archived pr true
          | Mod when to_prover <> SameProver -> remove_external_proof pr
          | _ -> ()
  ) s;
  save_session config env_session.session

let read_to_prover config =
  match !opt_to_prover with
    | None -> None
    | Some fpr ->
      Some (prover_of_filter_prover config fpr)


let run ~action () =
  let env,config,should_exit1 = read_env_spec () in
  let filters,should_exit2 = read_filter_spec config in
  if should_exit1 || should_exit2 then exit 1;
  (* sanitize --to-prover and --to-known-prover for Copy* *)
  if action<>Mod && (!opt_to_prover <> None) = (!opt_to_known) then begin
    eprintf "The option --to-prover@ and@ --to-known-prover@ are@ exclusive@ \
but@ one@ is@ needed.@.";
    exit 1
  end;
  (* get the provers *)
  let pk = read_to_prover config in
  try
    iter_files (run_one ~action env config filters pk)
  with OutdatedSession as e ->
    eprintf "@.%a@ You@ can@ allow@ it@ with@ the@ option@ -F.@."
      Exn_printer.exn_printer e


let cmd_copy =
  { cmd_spec     = spec;
    cmd_desc     = "copy proof based on a filter";
    cmd_name     = "copy";
    cmd_run      = run ~action:Copy;
  }


let cmd_archive =
  { cmd_spec     = spec;
    cmd_desc     = "same as copy but archive the source";
    cmd_name     = "copy-archive";
    cmd_run      = run ~action:CopyArchive;
  }


let cmd_mod =
  { cmd_spec = spec;
    cmd_desc     = "modify proof based on filter";
    cmd_name     = "mod";
    cmd_run      = run ~action:Mod;
  }
