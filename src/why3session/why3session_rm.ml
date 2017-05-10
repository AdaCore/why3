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

open Why3
open Why3session_lib
open Session_itp
open Format

type filter_prover =
  | Prover of Whyconf.prover
  | ProverId of string

(**
   TODO remove_transformation,...
**)

(** Currently doesn't share the configuration of ide *)
type replace = Interactive | Always | Not_valid (*| Never*)
let opt_remove = ref Always
let set_remove s () = opt_remove := s

let spec =
  ("--clean",
   Arg.Unit (fun () -> set_remove Not_valid ();
     set_filter_verified_goal FT_Yes),
   " remove unsuccessful proof attempts \
    associated to proved goals \
    (same as --filter-verified-goal yes --conservative)")::
  ("--interactive",
   Arg.Unit (set_remove Interactive), " ask before replacing proof_attempt")::
  ("-i",
   Arg.Unit (set_remove Interactive), " same as --interactive")::
  ("--force", Arg.Unit (set_remove Always),
   " remove all selected proof_attempt (default)")::
  ("-f", Arg.Unit (set_remove Always), " same as --force")::
  ("--conservative", Arg.Unit (set_remove Not_valid),
   " don't remove proof_attempt which are not obsolete and valid")::
  ("-c", Arg.Unit (set_remove Not_valid), " same as --conservative")::
(*  ("--never", Arg.Unit (set_remove Never),
   " never remove a proof")::
  ("-n", Arg.Unit (set_remove Never), " same as --never")::*)
  (force_obsolete_spec @ filter_spec @ common_options)

let rec interactive to_remove =
  eprintf "Do you want to remove the external proof %a (y/n)@."
    print_external_proof to_remove;
  let answer = read_line () in
  match answer with
    | "y" -> true
    | "n" -> false
    | _ -> interactive to_remove

let run_one env config filters fname =
  let env_session,_,_ =
    read_update_session ~allow_obsolete:!opt_force_obsolete env config fname in
  session_iter_proof_attempt_by_filter filters
    (fun pr ->
      let remove = match !opt_remove with
        | Always -> true (*| Never -> false*)
        | Interactive -> interactive pr
        | Not_valid -> not (Opt.inhabited (proof_verified pr)) in
      if remove then remove_external_proof pr) env_session.session;
  save_session config env_session.session


let run () =
  let env,config,should_exit1 = read_env_spec () in
  let filters,should_exit2 = read_filter_spec config in
  if should_exit1 || should_exit2 then exit 1;
  iter_files (run_one env config filters)


let cmd =
  { cmd_spec = spec;
    cmd_desc     = "remove proof based on a filter";
    cmd_name     = "rm";
    cmd_run      = run;
  }
