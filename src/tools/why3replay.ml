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

open Format
open Why3

(** {2 Warnings} *)

(* warnings are shown on standard output instead of standard error:
   they are not an error but should be present in the reporting of the
   replay *)

let display_warning ?loc msg =
  match loc with
    | None -> printf "%s@." msg
    | Some l -> printf "%a: %s@." Loc.gen_report_position l msg

let () = Warning.set_hook display_warning

let debug = Debug.register_info_flag
    ~desc:"of@ the@ progression@ of@ a@ replay"
    "replay"

let files = Queue.create ()
let opt_stats = ref true
let opt_force = ref false
let opt_obsolete_only = ref false
let opt_use_steps = ref false
let opt_merging_only = ref false
(*
let opt_bench = ref false
*)
let opt_provers = ref []
let opt_verbose = ref true


(** {2 Smoke detector} *)

type smoke_detector =
  | SD_None (** No smoke detector *)
  | SD_Top  (** Negation added at the top of the goals *)
  | SD_Deep
(** Negation added under implication and universal quantification *)


let opt_smoke = ref SD_None

let set_opt_smoke = function
  | "none" -> opt_smoke := SD_None
  | "top" ->  opt_smoke := SD_Top
  | "deep" ->  opt_smoke := SD_Deep
  | _ -> assert false

let usage_msg = Format.sprintf
  "Usage: %s [options] <project directory>"
  (Filename.basename Sys.argv.(0))

let option_list = [
  ("-f",
   Arg.Set opt_force,
   " enforce saving the session after replay");
  ("--force",
   Arg.Set opt_force,
   " same as -f");
  ("--use-steps",
   Arg.Set opt_use_steps,
   " replay using recorded number of proof steps (when possible)");
  ("--obsolete-only",
   Arg.Set opt_obsolete_only,
   " replay only if session is obsolete");
  ("--merging-only",
   Arg.Set opt_merging_only,
   " check merging of session");
  ("-P",
   Arg.String (fun s ->
     opt_provers := Whyconf.parse_filter_prover s :: !opt_provers),
   "<prover> restrict replay to given prover");
  ("--prover",
   Arg.String (fun s ->
     opt_provers := Whyconf.parse_filter_prover s :: !opt_provers),
   " same as -P");
  ("--smoke-detector",
   Arg.Symbol (["none";"top";"deep"],set_opt_smoke),
   " try to detect if the context is self-contradicting") ;
(*
  ("--bench",
   Arg.Set opt_bench, " run as bench (experimental)");
 *)
  ("--no-stats",
   Arg.Clear opt_stats,
   " do not print statistics") ;
  ("-q",
   Arg.Clear opt_verbose,
   " run quietly");
  ("--quiet",
   Arg.Clear opt_verbose,
   " same as -q") ]

let add_file f = Queue.push f files

let config, _, env =
  Whyconf.Args.initialize option_list add_file usage_msg

module C = Controller_itp.Make(Unix_scheduler.Unix_scheduler)

let () =
  Controller_itp.set_session_max_tasks (Whyconf.running_provers_max (Whyconf.get_main config));
  C.register_observer
    (fun w s r ->
      if Debug.test_flag debug then
        Printf.eprintf "Progress: %d/%d/%d                       \r%!" w s r)

let print_result = Call_provers.print_prover_result

module S = Session_itp

let goal_statistics ses (goals,n,m) g =
  if S.pn_proved ses g then (goals,n+1,m+1) else (g::goals,n,m+1)

let theory_statistics ses (ths,n,m) th =
  let goals,n1,m1 =
    List.fold_left (goal_statistics ses) ([],0,0) (S.theory_goals th) in
  ((th,goals,n1,m1)::ths,n+n1,m+m1)

let file_statistics ses _ f (files,n,m) =
  let ths,n1,m1 =
    List.fold_left (theory_statistics ses) ([],0,0) (S.file_theories f) in
  ((f,ths,n1,m1)::files,n+n1,m+m1)

let print_statistics ses files =
  let print_goal g =
    printf "         +--goal %s not proved@."
           (S.get_proof_name ses g).Ident.id_string
  in
  let print_theory (th,goals,n,m) =
    if n<m then begin
      printf "      +--theory %s: %d/%d@."
        (S.theory_name th).Ident.id_string n m;
      List.iter print_goal (List.rev goals)
    end
  in
  let print_file (f,ths,n,m) =
    if n<m then begin
      printf "   +--file [%a]: %d/%d@." S.print_file_path (S.file_path f) n m;
      List.iter print_theory (List.rev ths)
    end
  in
  List.iter print_file (List.rev files)


let print_report ses (id,p,l,r) =
  let g = S.get_proof_name ses id in
  printf "   goal '%s', prover '%a': " g.Ident.id_string Whyconf.print_prover p;
  match !opt_smoke with
  | SD_None ->
     begin
       match r with
       | C.Result(new_res,old_res) ->
          printf "%a instead of %a (timelimit=%d, memlimit=%d, steplimit=%d)@."
                 print_result new_res print_result old_res
                 l.Call_provers.limit_time
                 l.Call_provers.limit_mem
                 l.Call_provers.limit_steps
       | C.No_former_result new_res ->
          printf "no former result available, new result is: %a@."
                 print_result new_res
       | C.CallFailed msg ->
          printf "internal failure '%a'@." Exn_printer.exn_printer msg;
       | C.Replay_interrupted ->
          printf "replay interrupted@."
       | C.Edited_file_absent f ->
          printf "proof script absent (%s)@." f
       | C.Prover_not_installed ->
          printf "not installed@."
     end
  | _ ->
     let res =
       match r with
       | C.Result(new_res,_old_res) -> new_res
       | C.No_former_result new_res -> new_res
       | _ -> assert false
     in
     printf "result is: %a -> Smoke detected!@."
                 print_result res


let same_result r1 r2 =
  match r1.Call_provers.pr_answer, r2.Call_provers.pr_answer with
    | Call_provers.Valid, Call_provers.Valid -> true
    | Call_provers.Invalid, Call_provers.Invalid -> true
    | Call_provers.Timeout, Call_provers.Timeout -> true
    | Call_provers.OutOfMemory, Call_provers.OutOfMemory -> true
    | Call_provers.Unknown _, Call_provers.Unknown _-> true
    | Call_provers.Failure _, Call_provers.Failure _-> true
    | _ -> false

let run_replay some_merge_miss found_obs cont =
  let session = cont.Controller_itp.controller_session in
  let final_callback found_upgraded_prover report =
    Debug.dprintf debug "@.";
    let files,n,m =
      S.Hfile.fold (file_statistics session)
        (S.get_files session) ([],0,0)
    in
    let report =
      match !opt_smoke with
      | SD_None ->
         List.filter
           (function
             | (_,_,_,C.Result(new_res,old_res)) ->
                not (same_result new_res old_res)
             | _ -> true)
           report
      | _ ->
         List.filter
           (function
             | (_,_,_,C.Result({Call_provers.pr_answer = Call_provers.Valid} ,_))
               -> true
             | (_,_,_,C.No_former_result({Call_provers.pr_answer = Call_provers.Valid}))
               -> true
             | _ -> false)
           report
    in
    let save () =
      Debug.dprintf debug "Saving session...@?";
      S.save_session session;
      Debug.dprintf debug " done@." in
    printf " %d/%d " n m;
    if report = [] && not some_merge_miss then
      begin
        match !opt_smoke with
        | SD_None ->
           printf "(replay OK%s%s)@."
                  (if found_obs then ", obsolete session" else "")
                  (if found_upgraded_prover then ", upgraded prover" else "");
           if !opt_stats && n<m then print_statistics session files;
           Debug.dprintf debug "Everything replayed OK.@.";
           if !opt_force || found_obs || found_upgraded_prover then save ();
           exit 0
        | _ ->
           printf "No smoke detected@.";
           exit 0
      end
    else
      let report = List.rev report in
      begin
        printf "(replay failed%s)@."
          (if some_merge_miss then ", with some merge miss" else "");
        List.iter (print_report session) report;
        eprintf "Replay failed.@.";
        if !opt_force then save ();
        exit 1
      end
  in
  let callback paid pastatus =
    Debug.dprintf debug "[Replay] callback on node paid=%a with pastatus=%a@."
                  Session_itp.print_proofAttemptID paid Controller_itp.print_status pastatus
  in
  let notification _any =
    Debug.dprintf debug "[Replay] notified on node any@."
  in
  let update_monitor w s r =
    if !opt_verbose then
      Format.eprintf "Progress: %d/%d/%d                       \r%!" w s r
  in
  C.register_observer update_monitor;
  if !opt_provers = [] then
    let () =
      C.replay ~valid_only:false ~obsolete_only:!opt_obsolete_only ~use_steps:!opt_use_steps
               ~callback ~notification ~final_callback cont ~any:None
    in ()
  else
    let filter a =
      List.exists
        (fun p -> Whyconf.filter_prover p a.Session_itp.prover)
        !opt_provers in
    C.replay ~valid_only:false ~obsolete_only:!opt_obsolete_only ~use_steps:!opt_use_steps
             ~filter ~callback ~notification ~final_callback cont ~any:None

let transform_smoke cont tr_name =
  let session = cont.Controller_itp.controller_session in
  (* filter the proof attempts *)
  let (to_remove,to_transform) =
    Session_itp.fold_all_session
      session
      (fun ((to_remove,to_transform) as acc) any ->
       match any with
       | Session_itp.APn pnid ->
          let valid,other =
            Whyconf.Hprover.fold
              (fun _pr paid (valid,other) ->
               if Session_itp.pa_proved session paid then
                 (paid::valid,other)
               else (valid,paid::other))
              (Session_itp.get_proof_attempt_ids session pnid)
              ([],[])
          in
          let to_transform =
            match valid with
            | [] -> to_transform
            | _ -> (pnid,valid)::to_transform
          in (List.rev_append other to_remove,to_transform)
       | _ -> acc)
      ([],[])
  in
  List.iter
    (fun paid ->
     let pa = Session_itp.get_proof_attempt_node session paid in
     Session_itp.remove_proof_attempt
       session pa.Session_itp.parent pa.Session_itp.prover)
    to_remove;
  List.iter
    (fun (pn,paids) ->
     let tasks =
       Session_itp.apply_trans_to_goal
         ~allow_no_effect:true session cont.Controller_itp.controller_env
         tr_name [] pn
     in
     let tid = Session_itp.graft_transf session pn tr_name [] tasks in
     match Session_itp.get_sub_tasks session tid with
     | [new_pn] ->
        List.iter
          (fun paid ->
           let pa = Session_itp.get_proof_attempt_node session paid in
           Session_itp.remove_proof_attempt
             session pa.Session_itp.parent pa.Session_itp.prover;
           let _new_paid =
             Session_itp.graft_proof_attempt
               session new_pn pa.Session_itp.prover
               ~limit:pa.Session_itp.limit in
           ())
          paids
     | _ -> assert false)
    to_transform

(*
let run_as_bench env_session =
  let sched =
    M.init (Whyconf.running_provers_max (Whyconf.get_main config))
  in
  eprintf "Provers:@ ";
  let provers =
    Whyconf.Mprover.fold
      (fun _ p acc ->
        if p.Whyconf.interactive then acc else
          begin
            eprintf "%a@ " Whyconf.print_prover p.Whyconf.prover;
            p.Whyconf.prover :: acc
          end)
      (Whyconf.get_provers env_session.Session.whyconf) []
  in
  eprintf "@.";
  let callback () =
    eprintf "Saving session...@?";
    Session.save_session config env_session.Session.session;
    eprintf " done.@.";
    exit 0
  in
  let limit = { Call_provers.empty_limit with Call_provers.limit_time = 2} in
  M.play_all env_session sched ~callback ~limit provers;
  main_loop ();
  eprintf "main replayer (in bench mode) exited unexpectedly@.";
  exit 1
 *)


let () =
  let dir =
    try
      Server_utils.get_session_dir ~allow_mkdir:false files
    with Invalid_argument s ->
      Format.eprintf "Error: %s@." s;
      Whyconf.Args.exit_with_usage option_list usage_msg
  in
  if not (Queue.is_empty files) then
    Whyconf.Args.exit_with_usage option_list usage_msg;
  try
    Debug.dprintf debug "Opening session '%s'...@?" dir;
    let ses,shape_version = S.load_session dir in
    let cont = Controller_itp.create_controller config env ses in
    (* update the session *)
    let found_obs, found_detached =
      try
        Controller_itp.reload_files cont ~shape_version
      with
      | Controller_itp.Errors_list l ->
          List.iter (fun e -> Format.eprintf "%a@." Exn_printer.exn_printer e) l;
          exit 1
    in
    Debug.dprintf debug " done.@.";
    if !opt_obsolete_only && not (found_detached || found_obs)
    then
      begin
        eprintf "Session is not obsolete, hence not replayed@.";
        printf "@.";
        exit 0
      end;
    if found_obs then eprintf "[Warning] session is obsolete@.";
    if found_detached then eprintf "[Warning] found detached goals or theories or transformations@.";
    if !opt_merging_only then
      exit (if found_detached then 1 else 0);
(*
    if !opt_bench then run_as_bench env_session;
 *)
    let tr =
      match !opt_smoke with
      | SD_None -> None
      | SD_Top -> Some "smoke_detector_top"
      | SD_Deep -> Some "smoke_detector_deep"
    in
    begin match tr with
    | Some _ when found_obs || found_detached ->
       eprintf "Cannot run smoke detection in presence of obsolete proofs or detached goals@.";
       exit 1
    | Some tr -> transform_smoke cont tr
    | None -> ()
    end;
    run_replay found_detached found_obs cont;
    Debug.dprintf debug "[Replay] starting scheduler@.";
    Unix_scheduler.Unix_scheduler.main_loop ~prompt:"" (fun _ -> ());
    eprintf "main replayer loop exited unexpectedly@.";
    exit 1
  with
    | e when not (Debug.test_flag Debug.stack_trace) ->
      eprintf "Error while opening session with database '%s': %a@."
        dir
        Exn_printer.exn_printer e;
      eprintf "Aborting...@.";
      exit 1


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3replay.opt"
End:
*)
