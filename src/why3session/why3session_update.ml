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

open Why3
open Why3session_lib
open Session_itp

type action =
  | RenameFile of string * string
  | MarkObsolete (* optionally with given prover filter *)
  | RemoveProofs
  | AddProver of string

let actions = ref ([] : action list)

let spec_update =
  let open Getopt in
  [
    ( KLong "rename-file",
      Hnd1
        ( APair (':', AString, AString),
          fun (src, dst) -> actions := RenameFile (src, dst) :: !actions ),
      "<old>:<new> rename file" );
    ( KLong "mark-obsolete",
      Hnd0 (fun () -> actions := MarkObsolete :: !actions),
      " mark proofs (specified as filters below) as obsolete" );
    ( KLong "remove-proofs",
      Hnd0 (fun () -> actions := RemoveProofs :: !actions),
      " delete proofs (specified as filters below)" );
    ( KLong "add-provers",
      Hnd1
        ( AList (':', AString),
          fun pl ->
            actions := List.fold_left (fun l p -> AddProver p :: l) !actions pl
        ),
      "<provers> add a proof attempt with the specified provers\nto every proof node of the session" );
  ]
  @ Why3session_lib.filter_spec

let do_action ~config ~env ~session action =
  ignore env;
  match action with
  | RenameFile (src, dst) ->
    let src, dst = rename_file session src dst in
    let dir = get_dir session in
    let src = Sysutil.system_dependent_absolute_path dir src in
    let dst = Sysutil.system_dependent_absolute_path dir dst in
    assert (Sys.file_exists src);
    assert (not (Sys.is_directory src));
    assert (not (Sys.file_exists dst));
    Sys.rename src dst
  | MarkObsolete ->
    let f, e = Why3session_lib.read_filter_spec config in
    if e then exit 1;
    Why3session_lib.session_iter_proof_attempt_by_filter session f (fun id _ ->
        (* Format.eprintf "proof id %a marked as obsolete@."
           Session_itp.print_proofAttemptID id; *)
        mark_obsolete session id)
  | RemoveProofs ->
    let f, e = Why3session_lib.read_filter_spec config in
    if e then exit 1;
    Why3session_lib.session_iter_proof_attempt_by_filter session f
      (fun _ pa_node ->
        let parent = pa_node.parent in
        let prover = pa_node.prover in
        remove_proof_attempt session parent prover)
  | AddProver p ->
    let f, e = Why3session_lib.read_filter_spec config in
    if e then exit 1;
    let p =
      let filter_prover = Whyconf.parse_filter_prover p in
      Whyconf.filter_one_prover config filter_prover
    in
    let main = Whyconf.get_main config in
    let limits =
      {
        Call_provers.limit_time = Whyconf.timelimit main;
        Call_provers.limit_steps = 0;
        Call_provers.limit_mem = Whyconf.memlimit main;
      }
    in
    Why3session_lib.session_iter_proof_node_id_by_filter session f (fun pn ->
        let _ = graft_proof_attempt session pn p.Whyconf.prover ~limits in
        ())

let run_update () =
  let config, env = Whyconf.Args.complete_initialization () in
  iter_session_files (fun fname ->
      let session = read_session fname in
      List.iter (do_action ~config ~env ~session) !actions;
      save_session session)

let cmd_update =
  {
    cmd_spec = spec_update;
    cmd_desc = "update session from the command line";
    cmd_usage = "<session>\nUpdate session from the command line.";
    cmd_name = "update";
    cmd_run = run_update;
  }
