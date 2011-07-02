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


let includes = ref []
let file = ref None
let opt_version = ref false
let opt_stats = ref true

let spec = Arg.align [
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> add s to loadpath") ;
(*
  ("-f",
   Arg.String (fun s -> input_files := s :: !input_files),
   "<f> add file f to the project (ignored if it is already there)") ;
*)
  ("-s",
   Arg.Clear opt_stats,
   " do not print statistics") ;
  ("-v",
   Arg.Set opt_version,
   " print version information") ;
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

let fname = match !file with
  | None ->
      Arg.usage spec usage_str;
      exit 1
  | Some f ->
      f

let config = Whyconf.read_config None

let loadpath = (Whyconf.loadpath (Whyconf.get_main config))
  @ List.rev !includes

let env = Env.create_env_of_loadpath loadpath

let provers = Whyconf.get_provers config

let provers =
  Util.Mstr.fold (Session.get_prover_data env) provers Util.Mstr.empty

let usleep t = ignore (Unix.select [] [] [] t)


let idle_handler = ref None
let timeout_handler = ref None

module M = Session.Make
  (struct
     type key = int

     let create ?parent () =
       match parent with
         | None -> 0
         | Some  n -> n+1

     let remove _row = ()

     let reset () = ()

     let idle f =
       match !idle_handler with
         | None -> idle_handler := Some f;
         | Some _ -> failwith "Replay.idle: already one handler installed"

     let timeout ~ms f =
       match !timeout_handler with
         | None -> timeout_handler := Some(float ms /. 1000.0 ,f);
         | Some _ -> failwith "Replay.timeout: already one handler installed"

   end)



let main_loop () =
  let last = ref (Unix.gettimeofday ()) in
  while true do
    let time = Unix.gettimeofday () -. !last in
    (* attempt to run timeout handler *)
    let timeout =
      match !timeout_handler with
        | None -> false
        | Some(ms,f) ->
            if time > ms then
              let b = f () in
              if b then true else
                begin
                  timeout_handler := None;
                  true
                end
            else false
    in
    if timeout then
      last := Unix.gettimeofday ()
    else
      (* attempt to run the idle handler *)
      match !idle_handler with
        | None ->
            begin
              let ms =
                match !timeout_handler with
                  | None -> 100.0 (* raise Exit *)
                  | Some(ms,_) -> ms
              in
              usleep (ms -. time)
            end
        | Some f ->
            let b = f () in
            if b then () else
              begin
                idle_handler := None;
              end
  done

open Format

(*
let model_index = Hashtbl.create 257
*)

let init =
(*
  let cpt = ref 0 in
*)
  fun _row any ->
(*
    incr cpt;
    Hashtbl.add model_index !cpt any;
*)
    let _name =
      match any with
        | M.Goal g -> M.goal_expl g
        | M.Theory th -> M.theory_name th
        | M.File f -> Filename.basename f.M.file_name
        | M.Proof_attempt a ->
            begin
              match a.M.prover with
                | M.Detected_prover p ->
                    p.Session.prover_name ^ " " ^ p.Session.prover_version
                | M.Undetected_prover s -> s
            end
        | M.Transformation tr -> Session.transformation_id tr.M.transf
    in
    (* eprintf "Item '%s' loaded@." name *)
    ()

(*
let string_of_result result =
  match result with
    | Session.Undone -> "undone"
    | Session.Scheduled -> "scheduled"
    | Session.Running -> "running"
    | Session.InternalFailure _ -> "internal failure"
    | Session.Done r -> match r.Call_provers.pr_answer with
        | Call_provers.Valid -> "valid"
        | Call_provers.Invalid -> "invalid"
        | Call_provers.Timeout -> "timeout"
        | Call_provers.Unknown _ -> "unknown"
        | Call_provers.Failure _ -> "failure"
        | Call_provers.HighFailure -> "high failure"

let print_result fmt res =
  let t = match res with
    | Session.Done { Call_provers.pr_time = time } ->
        Format.sprintf "(%.1f)" time
    | _ -> ""
  in
  fprintf fmt "%s%s" (string_of_result res) t
*)


let print_result fmt
    {Call_provers.pr_answer=ans; Call_provers.pr_output=out;
     Call_provers.pr_time=_t} =
(*
  fprintf fmt "%a (%.1fs)" Call_provers.print_prover_answer ans t;
*)
  fprintf fmt "%a" Call_provers.print_prover_answer ans;
  if ans == Call_provers.HighFailure then
    fprintf fmt "@\nProver output:@\n%s@." out

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

let project_dir =
  if Sys.file_exists fname then
    begin
      if Sys.is_directory fname then
        begin
          eprintf "Info: found directory '%s' for the project@." fname;
          fname
        end
      else
        begin
          eprintf "Info: found regular file '%s'@." fname;
          let d =
            try Filename.chop_extension fname
            with Invalid_argument _ -> fname
          in
          eprintf "Info: using '%s' as directory for the project@." d;
          d
        end
    end
  else
    failwith "file does not exist"

let goal_statistics (goals,n,m) g =
  if M.goal_proved g then (goals,n+1,m+1) else (g::goals,n,m+1)

let theory_statistics (ths,n,m) th =
  let goals,n1,m1 = List.fold_left goal_statistics ([],0,0) (M.goals th) in
  ((th,goals,n1,m1)::ths,n+n1,m+m1)

let file_statistics (files,n,m) f =
  let ths,n1,m1 = List.fold_left theory_statistics ([],0,0) f.M.theories in
  ((f,ths,n1,m1)::files,n+n1,m+m1)

let print_statistics files =
  List.iter
    (fun (f,ths,n,m) ->
       if n<m then
         begin
           printf "   +--file %s: %d/%d@." f.M.file_name n m;
           List.iter
             (fun (th,goals,n,m) ->
                if n<m then
                  begin
                    printf "      +--theory %s: %d/%d@."
                      (M.theory_name th) n m;
                    List.iter
                      (fun g ->
                         printf "         +--goal %s not proved@." (M.goal_name g))
                      (List.rev goals)
                  end)
             (List.rev ths)
         end)
    (List.rev files)

let print_report (g,p,r) =
  printf "   goal '%s', prover '%s': " g p;
  match r with
  | M.Wrong_result(new_res,old_res) ->
      printf "%a instead of %a@."
        print_result new_res print_result old_res
  | M.No_former_result ->
      printf "no former result available@."
  | M.CallFailed msg ->
      printf "internal failure '%a'@." Exn_printer.exn_printer msg;
  | M.Prover_not_installed ->
      printf "not installed@."

let () =
  try
    eprintf "Opening session...@?";
    M.open_session ~env ~config ~init ~notify project_dir;
    M.maximum_running_proofs :=
      Whyconf.running_provers_max (Whyconf.get_main config);
    eprintf " done@.";
    let callback report =
      let files,n,m =
        List.fold_left file_statistics ([],0,0) (M.get_all_files ())
      in
      printf " %d/%d@." n m ;
      match report with
        | [] ->
            if !opt_stats && n<m then print_statistics files;
            eprintf "Everything OK.@.";
            exit 0
        | _ ->
            List.iter print_report report;
            eprintf "Check failed.@.";
            exit 1
    in
    M.check_all ~callback;
    try main_loop ()
    with Exit -> eprintf "main replayer exited unexpectedly@."
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "Error while opening session with database '%s' : %a@." project_dir
      Exn_printer.exn_printer e;
    eprintf "Aborting...@.";
    exit 1


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3replayer.byte"
End:
*)
