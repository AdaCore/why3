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


open Format
open Why3
module S = Session

let includes = ref []
let file = ref None
let opt_version = ref false
let opt_stats = ref true
let opt_force = ref false
let opt_convert_unknown_provers = ref false


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

let opt_config = ref None
let opt_extra = ref []

let spec = Arg.align [
  ("-L",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> add s to loadpath") ;
  ("--library",
   Arg.String (fun s -> includes := s :: !includes),
   " same as -L") ;
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   " same as -L (obsolete)") ;
  ("-C", Arg.String (fun s -> opt_config := Some s),
   "<file> Read configuration from <file>") ;
  ("--config", Arg.String (fun s -> opt_config := Some s),
   " same as -C") ;
  ("--extra-config", Arg.String (fun s -> opt_extra := !opt_extra @ [s]),
   "<file> Read additional configuration from <file>") ;
  ("-force",
   Arg.Set opt_force,
   " enforce saving of session even if replay failed") ;
  ("-smoke-detector",
   Arg.Symbol (["none";"top";"deep"],set_opt_smoke),
   " try to detect if the context is self-contradicting") ;
  ("-s",
   Arg.Clear opt_stats,
   " do not print statistics") ;
  ("-v",
   Arg.Set opt_version,
   " print version information") ;
  "--convert-unknown-provers", Arg.Set opt_convert_unknown_provers,
  " try to find compatible provers for all unknown provers";
  Debug.Opt.desc_debug_list;
  Debug.Opt.desc_shortcut "parse_only" "--parse-only" " Stop after parsing";
  Debug.Opt.desc_shortcut
    "type_only" "--type-only" " Stop after type checking";
  Debug.Opt.desc_debug_all;
  Debug.Opt.desc_debug;

]

let version_msg = Format.sprintf "Why3 replayer, version %s (build date: %s)"
  Config.version Config.builddate

let usage_str = Format.sprintf
  "Usage: %s [options] [<file.why>|<project directory>]"
  (Filename.basename Sys.argv.(0))

let set_file f = match !file with
  | Some _ ->
      raise (Arg.Bad "only one parameter")
  | None ->
      file := Some f

let () = Arg.parse spec set_file usage_str

let () =
  if !opt_version then begin
    Format.printf "%s@." version_msg;
    exit 0
  end

(* let () = *)
(*   if !opt_smoke <> Session.SD_None && !opt_force then begin *)
(*     Format.printf "You can't force when detecting smoke@."; *)
(*     exit 1 *)
(*   end *)


let fname = match !file with
  | None ->
      Arg.usage spec usage_str;
      exit 1
  | Some f ->
      f

let config = Whyconf.read_config !opt_config
let config = List.fold_left Whyconf.merge_config config !opt_extra

let loadpath = (Whyconf.loadpath (Whyconf.get_main config))
  @ List.rev !includes

let env = Env.create_env loadpath

let () = Whyconf.load_plugins (Whyconf.get_main config)

let () =
  Debug.Opt.set_flags_selected ();
  if Debug.Opt.option_list () then exit 0

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

let unknown_prover _ _ = None

let replace_prover _ _ = false

module Scheduler = Session_scheduler.Base_scheduler(struct end)

include Scheduler

end

module M = Session_scheduler.Make(O)

let print_result fmt
    {Call_provers.pr_answer=ans; Call_provers.pr_output=out;
     Call_provers.pr_time=_t} =
(*
  fprintf fmt "%a (%.1fs)" Call_provers.print_prover_answer ans t;
*)
  fprintf fmt "%a" Call_provers.print_prover_answer ans;
  if ans == Call_provers.HighFailure then
    fprintf fmt "@\nProver output:@\n%s@." out

let main_loop = O.main_loop
(*
let model_index = Hashtbl.create 257
*)

let project_dir =
  try
    Session.get_project_dir fname
  with Not_found -> failwith "file does not exist"

let goal_statistics (goals,n,m) g =
  if g.S.goal_verified then (goals,n+1,m+1) else (g::goals,n,m+1)

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
      printf "         +--goal %s not proved@." g.S.goal_name.Ident.id_string
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


let print_report (g,p,r) =
  printf "   goal '%s', prover '%a': " g.Ident.id_string Whyconf.print_prover p;
  match r with
  | M.Result(new_res,old_res) ->
    (* begin match !opt_smoke with *)
    (*   | Session.SD_None -> *)
        printf "%a instead of %a@."
          print_result new_res print_result old_res
    (*   | _ -> *)
    (*     printf "Smoke detected!!!@." *)
    (* end *)
  | M.No_former_result new_res ->
      printf "no former result available : %a@." print_result new_res
  | M.CallFailed msg ->
      printf "internal failure '%a'@." Exn_printer.exn_printer msg;
  | M.Prover_not_installed ->
      printf "not installed@."


let same_result r1 r2 =
  match r1.Call_provers.pr_answer, r2.Call_provers.pr_answer with
    | Call_provers.Valid, Call_provers.Valid -> true
    | Call_provers.Invalid, Call_provers.Invalid -> true
    | Call_provers.Timeout, Call_provers.Timeout -> true
    | Call_provers.Unknown _, Call_provers.Unknown _-> true
    | Call_provers.Failure _, Call_provers.Failure _-> true
    | _ -> false

let add_to_check_no_smoke config found_obs env_session sched =
      let session = env_session.S.session in
      let callback report =
        eprintf "@.";
	let files,n,m =
          S.PHstr.fold file_statistics
            session.S.session_files ([],0,0)
	in
        let report = List.filter (function
          | (_,_,M.Result(new_res,old_res)) ->not (same_result new_res old_res)
          | _ -> true) report in
        if report = [] then begin
            if found_obs then
              if n=m then
                printf " %d/%d (replay OK, all proved: obsolete session \
updated)@." n m
              else
                if !opt_force then
                  printf " %d/%d (replay OK, but not all proved: obsolete \
session updated since -force was given)@." n m
                else
                  printf " %d/%d (replay OK, but not all proved: obsolete \
session NOT updated)@." n m
            else
              printf " %d/%d@." n m ;
            if !opt_stats && n<m then print_statistics files;
            eprintf "Everything replayed OK.@.";
            if found_obs && (n=m || !opt_force) then
              begin
                eprintf "Updating obsolete session...@?";
                S.save_session config session;
                eprintf " done@."
              end;
            exit 0
        end
        else
          begin
            printf " %d/%d (replay failed)@." n m ;
            List.iter print_report report;
            eprintf "Replay failed.@.";
            exit 1
          end
    in
    M.check_all ~callback env_session sched

let add_to_check_smoke env_session sched =
  let callback report =
    eprintf "@.";
    let report = List.filter (function
      | (_,_,M.Result({Call_provers.pr_answer = Call_provers.Valid} ,_))
        -> true
      | (_,_,M.No_former_result({Call_provers.pr_answer = Call_provers.Valid}))
        -> true
      | _ -> false) report in
    if report = [] then begin
        eprintf "No smoke detected.@.";
        exit 0
    end
    else begin
        List.iter print_report report;
        eprintf "Smoke detected.@.";
        exit 1
    end
  in
  M.check_all ~callback env_session sched

let add_to_check config found_obs =
  match !opt_smoke with
    | SD_None -> add_to_check_no_smoke config found_obs;
    | _ -> assert (not found_obs); add_to_check_smoke

let transform_smoke env_session =
  let trans tr_name s =
    Session_tools.filter_proof_attempt S.proof_verified s.S.session;
    Session_tools.transform_proof_attempt ~keygen:O.create s tr_name in
  match !opt_smoke with
    | SD_None -> ()
    | SD_Top -> trans "smoke_detector_top" env_session
    | SD_Deep -> trans "smoke_detector_deep" env_session


let () =
  try
    eprintf "Opening session...@?";
    let env_session,found_obs =
      let session = S.read_session project_dir in
      M.update_session ~allow_obsolete:true session env config in
    transform_smoke env_session;
    if !opt_convert_unknown_provers then M.convert_unknown_prover env_session;
    let sched =
      M.init (Whyconf.running_provers_max (Whyconf.get_main config)) in
    if found_obs then begin
      if (* !opt_smoke <> Session.SD_None *) false then begin
        eprintf
          "[Error] I can't run the smoke detector if the session is obsolete";
        exit 1
      end;
      eprintf "[Warning] session is obsolete@.";
    end;
    (* M.smoke_detector := !opt_smoke; *)
    eprintf " done.";
    add_to_check config found_obs env_session sched;
    main_loop (); 
    eprintf "main replayer exited unexpectedly@."; 
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
compile-command: "unset LANG; make -C ../.. bin/why3replayer.byte"
End:
*)
