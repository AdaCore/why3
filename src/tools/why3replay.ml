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


module S = Session

let debug = Debug.register_info_flag
    ~desc:"of@ the@ progression@ of@ a@ replay"
    "replay"

let () = Debug.set_flag debug

let opt_file = ref None
let opt_stats = ref true
let opt_force = ref false
let opt_obsolete_only = ref false
let opt_use_steps = ref false
let opt_bench = ref false
let opt_provers = ref []



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
  "Usage: %s [options] [<file.why>|<project directory>]"
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
   " replay only if session is obsolete") ;
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
  ("--bench",
   Arg.Set opt_bench, " run as bench (experimental)");
  ("--no-stats",
   Arg.Clear opt_stats,
   " do not print statistics") ;
  ("-q",
   Arg.Unit (fun () -> Debug.unset_flag debug),
   " run quietly");
  ("--quiet",
   Arg.Unit (fun () -> Debug.unset_flag debug),
   " same as -q") ]

let add_opt_file f = match !opt_file with
  | Some _ ->
      raise (Arg.Bad "only one parameter")
  | None ->
      opt_file := Some f

let config, _, env =
  Whyconf.Args.initialize option_list add_opt_file usage_msg

(* let () = *)
(*   if !opt_smoke <> Session.SD_None && !opt_force then begin *)
(*     Format.printf "You can't force when detecting smoke@."; *)
(*     exit 1 *)
(*   end *)

let fname =
  match !opt_file with
  | None -> Whyconf.Args.exit_with_usage option_list usage_msg
  | Some f -> f

let found_upgraded_prover = ref false

module O =
  struct
     type key = int

     let create ?parent () =
       match parent with
         | None -> 0
         | Some  n -> n+1

     let remove _row = ()

     let reset () = ()

let init =
(*
  let cpt = ref 0 in
*)
  fun _row _any ->
(*
    incr cpt;
    Hashtbl.add model_index !cpt any;

    let _name =
      match any with
        | S.Goal g -> S.goal_expl g
        | S.Theory th -> th.S.theory_name.Ident.id_string
        | S.File f -> Filename.basename f.S.file_name
        | S.Proof_attempt a ->
          let p = a.S.proof_prover in
          p.C.prover_name ^ " " ^ p.C.prover_version
        | S.Transf tr -> tr.S.transf_name
    in
*)
    (* eprintf "Item '%s' loaded@." name *)
    ()


let notify _any = ()
(*
  match any with
    | M.Goal g ->
        printf "Goal '%s' proved: %b@." (M.goal_expl g) (M.goal_proved g)
    | M.Theory th ->
        printf "Theory '%s' verified: %b@." (M.theory_name th) (M.verified th)
    | M.File file ->
        printf "File '%s' verified: %b@." (Filename.basename file.M.file_name)
          file.M.file_verified
    | M.Proof_attempt a ->
        let p = a.M.prover in
        printf "Proof with '%s %s' gives %a@."
          p.Session.prover_name p.Session.prover_version
          print_result a.M.proof_state
    | M.Transformation tr ->
        printf "Transformation '%s' proved: %b@."
          (Session.transformation_id tr.M.transf) tr.M.transf_proved
*)

(*
let unknown_prover _ _ = None

let replace_prover _ _ = false
*)

let uninstalled_prover _eS unknown =
  try
    let p =
      Whyconf.get_prover_upgrade_policy config unknown
    in
    if p <> Whyconf.CPU_keep then found_upgraded_prover := true;
    p
  with Not_found ->
    Whyconf.CPU_keep

module Scheduler = Session_scheduler.Base_scheduler(struct end)

include Scheduler

end

module M = Session_scheduler.Make(O)

let print_result = Call_provers.print_prover_result

let main_loop = O.main_loop

let project_dir =
  try
    Session.get_project_dir fname
  with Not_found -> failwith "file does not exist"

let goal_statistics (goals,n,m) g =
  if Opt.inhabited (S.goal_verified g) then (goals,n+1,m+1) else (g::goals,n,m+1)

let theory_statistics (ths,n,m) th =
  let goals,n1,m1 =
    List.fold_left goal_statistics ([],0,0) th.S.theory_goals in
  ((th,goals,n1,m1)::ths,n+n1,m+m1)

let file_statistics _ f (files,n,m) =
  let ths,n1,m1 =
    List.fold_left theory_statistics ([],0,0) f.S.file_theories in
  ((f,ths,n1,m1)::files,n+n1,m+m1)

let print_statistics files =
  let print_goal g =
      printf "         +--goal %s not proved@." (S.goal_name g).Ident.id_string
  in
  let print_theory (th,goals,n,m) =
    if n<m then begin
      printf "      +--theory %s: %d/%d@."
        th.S.theory_name.Ident.id_string n m;
      List.iter print_goal (List.rev goals)
    end
  in
  let print_file (f,ths,n,m) =
    if n<m then begin
      printf "   +--file %s: %d/%d@." f.S.file_name n m;
      List.iter print_theory (List.rev ths)
    end
  in
  List.iter print_file (List.rev files)


let print_report (g,p,l,r) =
  printf "   goal '%s', prover '%a': " g.Ident.id_string Whyconf.print_prover p;
  match r with
  | M.Result(new_res,old_res) ->
    (* begin match !opt_smoke with *)
    (*   | Session.SD_None -> *)
        printf "%a instead of %a (timelimit=%d, memlimit=%d, steplimit=%d)@."
          print_result new_res print_result old_res
          l.Call_provers.limit_time
          l.Call_provers.limit_mem
          l.Call_provers.limit_steps
    (*   | _ -> *)
    (*     printf "Smoke detected!!!@." *)
    (* end *)
  | M.No_former_result new_res ->
      printf "no former result available, new result is: %a@."
        print_result new_res
  | M.CallFailed msg ->
      printf "internal failure '%a'@." Exn_printer.exn_printer msg;
  | M.Edited_file_absent f ->
      printf "proof script absent (%s)@." f
 | M.Prover_not_installed ->
      printf "not installed@."


let same_result r1 r2 =
  match r1.Call_provers.pr_answer, r2.Call_provers.pr_answer with
    | Call_provers.Valid, Call_provers.Valid -> true
    | Call_provers.Invalid, Call_provers.Invalid -> true
    | Call_provers.Timeout, Call_provers.Timeout -> true
    | Call_provers.OutOfMemory, Call_provers.OutOfMemory -> true
    | Call_provers.Unknown _, Call_provers.Unknown _-> true
    | Call_provers.Failure _, Call_provers.Failure _-> true
    | _ -> false

let add_to_check_no_smoke config some_merge_miss found_obs env_session sched =
  let session = env_session.S.session in
  let callback report =
    Debug.dprintf debug "@.";
    let files,n,m =
      S.PHstr.fold file_statistics
        session.S.session_files ([],0,0)
    in
    let report =
      List.filter
        (function
          | (__,_,_,M.Result(new_res,old_res)) ->
            not (same_result new_res old_res)
          | _ -> true)
        report
    in
    let save () =
      Debug.dprintf debug "Saving session...@?";
      S.save_session config session;
      Debug.dprintf debug " done@." in
    printf " %d/%d " n m;
    if report = [] && not some_merge_miss then
      begin
        printf "(replay OK%s%s)@."
          (if found_obs then ", obsolete session" else "")
          (if !found_upgraded_prover then ", upgraded prover" else "");
        if !opt_stats && n<m then print_statistics files;
        Debug.dprintf debug "Everything replayed OK.@.";
        if !opt_force || found_obs || !found_upgraded_prover then save ();
        exit 0
      end
    else
      let report = List.rev report in
      begin
        printf "(replay failed%s)@."
          (if some_merge_miss then ", with some merge miss" else "");
        List.iter print_report report;
        eprintf "Replay failed.@.";
        if !opt_force then save ();
        exit 1
      end
  in
  if !opt_provers = [] then
    M.check_all ~release:true ~use_steps:!opt_use_steps
      ~callback env_session sched
  else
    let filter a =
      List.exists
        (fun p -> Whyconf.filter_prover p a.Session.proof_prover)
        !opt_provers in
    M.check_all ~release:true ~use_steps:!opt_use_steps
      ~filter ~callback env_session sched

let add_to_check_smoke env_session sched =
  let callback report =
    Debug.dprintf debug "@.";
    let report =
      List.filter
        (function
          | (_,_,_,M.Result({Call_provers.pr_answer = Call_provers.Valid} ,_))
            -> true
          | (_,_,_,M.No_former_result({Call_provers.pr_answer = Call_provers.Valid}))
            -> true
          | _ -> false) report
    in
    if report = [] then begin
      Debug.dprintf debug "No smoke detected.@.";
      exit 0
    end
    else begin
      List.iter print_report report;
      eprintf "Smoke detected.@.";
      exit 1
    end
  in
  M.check_all ~release:true ~use_steps:!opt_use_steps
    ~callback env_session sched

let add_to_check config some_merge_miss found_obs =
  match !opt_smoke with
    | SD_None -> add_to_check_no_smoke config some_merge_miss found_obs;
    | _ ->
      assert (not some_merge_miss);
      assert (not found_obs);
      add_to_check_smoke

let transform_smoke env_session =
  let trans tr_name s =
    Session_tools.filter_proof_attempt
      (fun p -> Opt.inhabited (S.proof_verified p)) s.S.session;
    Session_tools.transform_proof_attempt ~keygen:O.create s tr_name
  in
  match !opt_smoke with
    | SD_None -> ()
    | SD_Top -> trans "smoke_detector_top" env_session
    | SD_Deep -> trans "smoke_detector_deep" env_session


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


let () =
  try
    Debug.dprintf debug "Opening session...@?";
    O.verbose := Debug.test_flag debug;
    let env_session,found_obs,some_merge_miss =
      let session, use_shapes = S.read_session project_dir in
      M.update_session ~allow_obsolete:true ~release:false ~use_shapes
        session env config
    in
    Debug.dprintf debug " done.@.";
    if !opt_obsolete_only && not found_obs
    then
      begin
        eprintf "Session is not obsolete, hence not replayed@.";
        printf "@.";
        exit 0
      end;
    if !opt_bench then run_as_bench env_session;
    let () = transform_smoke env_session in
    let sched =
      M.init (Whyconf.running_provers_max (Whyconf.get_main config))
    in
    if found_obs then eprintf "[Warning] session is obsolete@.";
    if some_merge_miss then eprintf "[Warning] some goals were missed during merge@.";
    add_to_check config some_merge_miss found_obs env_session sched;
    main_loop ();
    eprintf "main replayer loop exited unexpectedly@.";
    exit 1
  with
    | S.OutdatedSession ->
      eprintf "The session database '%s' is outdated, cannot replay@."
        project_dir;
      eprintf "Aborting...@.";
      exit 1
    | e when not (Debug.test_flag Debug.stack_trace) ->
      eprintf "Error while opening session with database '%s' : %a@."
        project_dir
        Exn_printer.exn_printer e;
      eprintf "Aborting...@.";
      exit 1


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3replay.byte"
End:
*)
