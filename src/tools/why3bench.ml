(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Call_provers
open Session_itp
open Controller_itp
open Format

module Main : functor () -> sig end
 = functor () -> struct

let force = ref false
let save_interval = ref 60.0

let usage_msg =
  "<session directory>\n\
  Run provers on all proof attempts missing a result in the specified session."

let session_dir = Queue.create ()

let opts =
  let open Getopt in
  [
    ( Key ('d', "delay"),
      Hnd1 (AFloat, fun i -> save_interval := i),
      "<sec> set the interval between session saves (default: 60)" );
    ( Key ('f', "force"),
      Hnd0 (fun () -> force := true),
      " replay all the proof attempts instead of just those\nwith obsolete results or no results" );
  ]

let config, env =
  Whyconf.Args.initialize opts (fun f -> Queue.add f session_dir) usage_msg

module C = Make (Unix_scheduler.Unix_scheduler)

let () =
  let d = if Queue.length session_dir = 1 then session_dir else
      begin
        eprintf "You must specify exactly one session directory@.";
        Whyconf.Args.exit_with_usage usage_msg;
      end
  in
  let dir =
    try Server_utils.get_session_dir ~allow_mkdir:false d with
    | Invalid_argument s ->
        eprintf "Error: %s@." s;
        Whyconf.Args.exit_with_usage usage_msg
  in
  let session = load_session dir in
  let controller = create_controller config env session in
  let found_obs, found_detached =
    try reload_files ~ignore_shapes:true controller with
    | Errors_list l ->
      List.iter (fun e -> eprintf "%a@." Exn_printer.exn_printer e) l;
      exit 1
  in
  if found_obs then eprintf "[Warning] session is obsolete@.";
  if found_detached then
    eprintf "[Warning] found detached goals or theories or transformations@.";
  set_session_max_tasks (Whyconf.running_provers_max (Whyconf.get_main config));
  let time = ref (Unix.gettimeofday ()) in
  let update_monitor w s r =
    let t = Unix.gettimeofday () in
    if t > !time +. !save_interval then
      begin
        time := t;
        eprintf "\nSaving session...%!";
        save_session controller.controller_session;
        eprintf " done.\n%!";
      end;
    eprintf "Progress: %d/%d/%d                       \r%!" w s r
  in
  C.register_observer update_monitor;
  let filter pa =
    !force ||
    pa.proof_obsolete ||
    match pa.proof_state with
    | None -> true
    | Some pa ->
      match pa.pr_answer with
        (* Cases where no proof attempt has been made *)
        | HighFailure _ | Failure "" -> true
        | Valid | Invalid | Timeout | OutOfMemory | StepLimitExceeded
        | Unknown _ | Failure _ -> false
  in
  C.replay ~valid_only:false ~obsolete_only:false controller ~filter
    ~callback:(fun _ _ -> ())
    ~notification:ignore
    ~final_callback:(fun _ _ ->
      eprintf "\nReplay completed, saving session...%!";
      save_session controller.controller_session;
      eprintf " done@.";
      exit 0)
    ~any:None;
  Unix_scheduler.Unix_scheduler.main_loop ~prompt:"" (fun _ -> ())

end

let () = Whyconf.register_command "bench" (module Main)
