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

(*
open Why3
open Why3session_lib
open Whyconf
open Session_itp
open Format
open Debug
module Todo = Session_scheduler.Todo
module C = Call_provers

(**
   TODO add_transformation,...

   TODO:
    filter_state
    filter_time
    filter_?

**)

(** To prover *)

type edit_mode =
| Edit_all
| Edit_diff
| Edit_none

let opt_edit = ref Edit_none

let set_edit_opt = function
  | "all"  -> opt_edit := Edit_all
  | "diff" -> opt_edit := Edit_diff
  | "none" -> opt_edit := Edit_none
  | _ -> assert false

type save_mode =
| Save_all
| Save_obsolete
| Save_none

let opt_save = ref Save_none

let set_save_opt = function
  | "all"  -> opt_save := Save_all
  | "obsolete" -> opt_save := Save_obsolete
  | "none" -> opt_save := Save_none
  | _ -> assert false

type outofsync_mode =
| Outofsync_usual
| Outofsync_success
| Outofsync_none

let opt_outofsync = ref Outofsync_success

let set_outofsync_opt = function
  | "usual"  -> opt_outofsync := Outofsync_usual
  | "success" -> opt_outofsync := Outofsync_success
  | "none" -> opt_outofsync := Outofsync_none
  | _ -> assert false


type verbosity =
| Vnormal
| Vquiet
| Vverbose

let opt_verbosity = ref Vnormal


let spec =
  [
   "--edit", Arg.Symbol (["all";"diff";"none"],set_edit_opt),
   " set when the user can edit an interactive proof:\
     - all: edit all the proofs not proved valid\
     - diff: edit all the proofs that have a different result\
     - none: never ask (default)";
   "-e", Arg.Unit (fun () -> set_edit_opt "all"),
   " same as --edit all";
   "--modif", Arg.Symbol (["all";"obsolete";"none"],set_save_opt),
   " set when modification of proofs are saved:\
     - all: apply all modifications\
     - obsolete: modify only the proofs that were obsolete or are new\
     - none: modify nothing (default)";
   "-m", Arg.Unit (fun () -> set_save_opt "all"),
   " same as --modif all";
   "--out-of-sync", Arg.Symbol (["none";"success";"usual"],set_outofsync_opt),
   " set what to do with sessions which are out-of-sync with the \
     original file or with why3:\
     - none: don't open sessions which are out-of-sync\
     - success: save them only if all the goals are proved at the end (default)\
     - usual: don't consider them specially";
   "--quiet",Arg.Unit (fun () -> opt_verbosity := Vquiet),
   " remove the progression";
  ]@
    (force_obsolete_spec @ filter_spec @ common_options)

module O = struct
  type key = unit

  let create ?parent:_ () = ()

  let remove _row = ()

  let reset () = ()

  let init = fun _row _any -> ()

  let notify _any = ()


  let uninstalled_prover eS unknown =
    try
      Whyconf.get_prover_upgrade_policy eS.whyconf unknown
    with Not_found -> Whyconf.CPU_keep

  module Scheduler = Session_scheduler.Base_scheduler(struct end)

  include Scheduler

  let wait_level = 100
  let wait_margin = 10
  let must_wait = ref false

  let nb_file_todo = ref 0

  let notify_timer_state w s r =
    let level = w + s in
    if level > wait_level + wait_margin then must_wait := true
    else if level < wait_level - wait_margin then must_wait := false;
    if !opt_verbosity <> Vquiet then
      Printf.eprintf "Progress: %d/%d/%d/%d                       \r%!"
        !nb_file_todo w s r
end

module M = Session_scheduler.Make(O)

let print_res fname pa ps old_ps =
  dprintf verbose
    "@[<hov 2>From file %s:@\nResult@ for@ the@ proof@ attempt@ %a:\
             @ %a@\nPreviously@ it@ was@ %a@]@."
    fname print_external_proof pa print_attempt_status ps
    print_attempt_status old_ps

let print_proof_goal fmt pa =
  pp_print_string fmt (goal_name pa.proof_parent).Ident.id_string


let same_result r1 r2 =
  match r1.Call_provers.pr_answer, r2.Call_provers.pr_answer with
    | Call_provers.Valid, Call_provers.Valid
    | Call_provers.Invalid, Call_provers.Invalid
    | Call_provers.Timeout, Call_provers.Timeout
    | Call_provers.OutOfMemory, Call_provers.OutOfMemory
    | Call_provers.HighFailure, Call_provers.HighFailure -> true
    | Call_provers.Unknown u1, Call_provers.Unknown u2 -> u1 = u2
    | Call_provers.Failure f1, Call_provers.Failure f2 -> f1 = f2
    | _ -> false

let same_status old_res new_res =
  match old_res, new_res with
  | InternalFailure old_exn, InternalFailure new_exn ->
    (Printexc.to_string old_exn) = (Printexc.to_string new_exn)
  | Done(old_res), Done(new_res) -> same_result old_res new_res
  | _ -> false

let is_valid pr =
  match pr.Call_provers.pr_answer with
  | Call_provers.Valid -> true
  | _ -> false

let to_edit_queue = Queue.create ()

let is_successful env = (* means all goals proved*)
  try
    let rec iter = function
        | File f -> file_iter iter f
        | Theory th -> theory_iter iter th
        | Goal g -> if not (Opt.inhabited (goal_verified g)) then raise Exit
        | Proof_attempt _ | Transf _ | Metas _ -> assert false in
    session_iter iter env.session;
    true
  with Exit -> false


let run_one sched env config filters interactive_provers fname =
  let env_session, out_of_sync, missed =
    read_update_session ~allow_obsolete:(!opt_outofsync <> Outofsync_none)
      env config fname in
  if out_of_sync then
    dprintf verbose "@[From@ file@ %s: out of sync@]@." fname;
  if missed then
    dprintf verbose "@[From@ file@ %s: merge missed new goals@]@." fname;
  let todo = Todo.create () (fun () _ -> ())
    (fun () ->
      if !opt_save <> Save_none &&
        (not (out_of_sync || missed)
         || !opt_outofsync = Outofsync_usual
           || (!opt_outofsync = Outofsync_success
              && is_successful env_session ))
      then save_session config env_session.session) in
  Todo.start todo;
  let stack = Stack.create () in
  session_iter_proof_attempt_by_filter filters
    (fun pr -> Stack.push pr stack) env_session.session;
  Stack.iter (fun pr ->
    Todo.start todo;
    let rec callback pa p _timelimit old_res status =
      match old_res, status with
      | _, M.Starting -> ()
      | _, M.StatusChange (Running|Scheduled) -> ()
      | _, M.StatusChange (Interrupted) -> Todo.stop todo
      | _, M.MissingFile efname ->
        dprintf verbose
          "@[From@ file@ %s:@\nThe@ edited@ file@ %s@ for@ the@ proof@ of@ %a@ \
           is@ missing@]@."
          fname efname print_proof_goal pa;
        Todo.stop todo
      | _, M.MissingProver ->
        dprintf verbose
          "@[From@ file@ %s:@\nThe@ prover@ %a@ for@ the@ proof@ of@ %a@ is@ \
           not@ installed@]@."
          fname Whyconf.print_prover p
          print_proof_goal pa;
        Todo.stop todo
      | Some old_res, M.StatusChange (Done new_res)
          when !opt_edit = Edit_all
          && Sprover.mem pa.proof_prover interactive_provers
          && not (is_valid new_res) ->
        queue_proof pa old_res new_res
      | Some old_res, M.StatusChange (Done new_res)
          when !opt_edit = Edit_diff
          && Sprover.mem pa.proof_prover interactive_provers
          && not (is_valid new_res)
          && not (same_result old_res new_res) ->
        queue_proof pa old_res new_res
      | Some old_res, M.StatusChange (Done new_res)
        when same_result old_res new_res ->
        dprintf verbose
          "@[From@ file@ %s:@\nThe@ prover@ %a for@ the@ proof@ of@ \
           %a@ give@ the@ same@ result@ %a@ as@ before@ %a.@]@."
          fname print_prover pa.proof_prover print_proof_goal pa
          C.print_prover_result old_res
          C.print_prover_result new_res;
          if !opt_save = Save_all ||
            (pa.proof_obsolete && !opt_save = Save_obsolete) then
            set_proof_state ~obsolete:false ~archived:false (Done new_res) pa;
        Todo.stop todo
      | None, M.StatusChange (Done new_res) ->
        dprintf verbose
          "@[From@ file@ %s:@\nThe@ prover@ %a@ for@ the@ proof,@ previously@ \
           undone,@ of@ %a@ give@ the@ new@ result@ %a.@]@."
          fname print_prover pa.proof_prover
          print_proof_goal pa C.print_prover_result new_res;
        if !opt_save = Save_obsolete then
          set_proof_state ~obsolete:false ~archived:false (Done new_res) pa;
        Todo.stop todo
      | Some old_res, M.StatusChange (Done new_res) when pa.proof_obsolete ->
        dprintf verbose
          "@[From@ file@ %s:@\nThe@ prover@ %a@ for@ the@ proof@ of@ %a@ give@ \
           the@ result@ %a@ instead@ of@ the@ obsolete@ %a.@]@."
          fname print_prover pa.proof_prover print_proof_goal pa
          C.print_prover_result new_res C.print_prover_result old_res;
        if !opt_save = Save_obsolete || !opt_save = Save_all then
          set_proof_state ~obsolete:false ~archived:false (Done new_res) pa;
        Todo.stop todo
      | Some old_res, M.StatusChange (Done new_res) ->
        dprintf verbose
          "@[From@ file@ %s:@\nThe@ prover@ %a@ for@ the@ proof@ of@ %a@ give@ \
           the@ result@ %a@ instead@ of@ %a.@]@."
          fname print_prover pa.proof_prover print_proof_goal pa
          C.print_prover_result new_res C.print_prover_result old_res;
        if !opt_save = Save_all then
          set_proof_state ~obsolete:false ~archived:false (Done new_res) pa;
        Todo.stop todo
      | _, M.StatusChange (InternalFailure exn) ->
        dprintf verbose
          "@[From@ file@ %s:@\nThe@ prover@ %a@ for@ the@ proof@ of@ %a@ \
             failed@ with@ the@ error@ %a@]@."
          fname print_prover pa.proof_prover print_proof_goal pa
          Exn_printer.exn_printer exn;
        Todo.stop todo
    and queue_proof a old_res new_res =
      if not (Queue.is_empty to_edit_queue) then
        Queue.push (a,old_res,new_res) to_edit_queue
      else
        edit_proof a old_res new_res
    and edit_proof a old_res new_res =
      printf "@[<hov 2>From@ file@ %s:@\n\
           Do@ you@ want@ to@ edit@ %a@ that@ fail@ with@ the@ result@ \
           %a@\nPreviously@ %a.@]@."
        fname print_external_proof a C.print_prover_result new_res
        C.print_prover_result old_res;
      let checkyn = ask_yn_nonblock ~callback:(fun b ->
        if b then
          let callback_edit pa =
            M.run_external_proof_v3 ~use_steps:false
              env_session sched pa
	      callback in
          M.edit_proof_v3 env_session sched
	    ~cntexample:false
            ~default_editor:"" (* TODO? *)
            ~callback:callback_edit a
        else
          Todo.stop todo;
        if not (Queue.is_empty to_edit_queue) then
          let (a,old_res,new_res) = Queue.pop to_edit_queue in
          edit_proof a old_res new_res
      ) in
      O.timeout ~ms:100 checkyn
    in
    M.run_external_proof_v3 ~use_steps:false env_session sched pr callback
  ) stack;
  Todo.stop todo

let run () =
  let env,config,should_exit1 = read_env_spec () in
  let filters,should_exit2 = read_filter_spec config in
  if should_exit1 || should_exit2 then exit 1;
  let sched = M.init (Whyconf.running_provers_max (Whyconf.get_main config)) in
  let interactive_provers =
    if !opt_edit <> Edit_none then
      Mprover.map_filter
        (fun p -> if p.Whyconf.interactive then Some () else None)
        (Whyconf.get_provers config)
    else Sprover.empty
  in
  try
    let files = Queue.create () in
    iter_files (fun f -> incr O.nb_file_todo; Queue.add f files);
    let run_one_by_one () =
      !O.must_wait ||
        let f = Queue.pop files in
        begin try
                run_one sched env config filters interactive_provers f
          with e when not (Debug.test_flag Debug.stack_trace) ->
            eprintf "@[From@ file@ %s:@\n%a.@]@." f Exn_printer.exn_printer e
        end;
        decr O.nb_file_todo;
        not (Queue.is_empty files) in
    if not (Queue.is_empty files) then
      M.schedule_any_timeout sched run_one_by_one;
    O.main_loop ()
  with OutdatedSession as e ->
    eprintf "@.%a@ You@ can@ allow@ it@ with@ the@ option@ -F.@."
      Exn_printer.exn_printer e


let cmd =
  { cmd_spec     = spec;
    cmd_desc     = "run the proof attempt that corresponds to the filter";
    cmd_name     = "run";
    cmd_run      = run;
  }
*)
