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

(**************************************************************************)
(* Specific source code for computing statistics is a contribution by     *)
(* David MENTRE <dmentre@linux-france.org>, 2011                          *)
(**************************************************************************)

open Why3
open Why3session_lib
open Whyconf
open Format
open Session
open Util

let opt_print_provers = ref false
let opt_print_edited = ref false
let opt_tree_print = ref false
let opt_stats_print = ref false
let opt_project_dir = ref false
let opt_print0 = ref false

let spec =
  ("--provers", Arg.Set opt_print_provers,
   " provers used in the session" ) ::
  ("--edited-files", Arg.Set opt_print_edited,
   " edited proof scripts in the session" ) ::
  ("--stats", Arg.Set opt_stats_print,
   " prints various proofs statistics" ) ::
  ("--tree", Arg.Set opt_tree_print,
   " session contents as a tree in textual format" ) ::
  ("--dir", Arg.Set opt_project_dir,
   " prints the directory of the session" ) ::
  ("--print0", Arg.Set opt_print0,
   " use the null character instead of newline" ) ::
    common_options


type proof_stats =
    { mutable nb_goals : int;
      mutable nb_proved_goals : int;
      mutable no_proof : Sstr.t;
      mutable only_one_proof : Sstr.t;
      prover_min_time : float Hprover.t;
      prover_avg_time : float Hprover.t;
      prover_max_time : float Hprover.t;
      prover_num_proofs : int Hprover.t;
      prover_data : (string) Hprover.t
    }

let new_proof_stats () =
  { nb_goals = 0;
    nb_proved_goals = 0;
    no_proof = Sstr.empty;
    only_one_proof = Sstr.empty;
    prover_min_time = Hprover.create 3;
    prover_avg_time = Hprover.create 3;
    prover_max_time = Hprover.create 3;
    prover_num_proofs =  Hprover.create 3;
    prover_data = Hprover.create 3 }

let apply_f_on_hashtbl_entry ~tbl ~f ~name  =
  try
    let cur_time = Hprover.find tbl name in
    Hprover.replace tbl name (f (Some cur_time))
  with Not_found ->
    Hprover.add tbl name (f None)

let update_min_time tbl (prover, time) =
  apply_f_on_hashtbl_entry
    ~tbl
    ~f:(function
      | Some cur_time -> if time < cur_time then time else cur_time
      | None -> time)
    ~name:prover

let update_max_time tbl (prover, time) =
  apply_f_on_hashtbl_entry
    ~tbl
    ~f:(function
      | Some cur_time -> if time > cur_time then time else cur_time
      | None -> time)
    ~name:prover

let update_avg_time tbl (prover, time) =
  apply_f_on_hashtbl_entry
    ~tbl
    ~f:(function
      | Some cur_time -> cur_time +. time
      | None -> time)
    ~name:prover

let update_count tbl (prover, _time) =
  apply_f_on_hashtbl_entry
    ~tbl
    ~f:(function
      | Some n -> n + 1
      | None -> 1)
    ~name:prover

let update_perf_stats stats prover_and_time =
  update_min_time stats.prover_min_time prover_and_time;
  update_max_time stats.prover_max_time prover_and_time;
  update_avg_time stats.prover_avg_time prover_and_time;
  update_count stats.prover_num_proofs prover_and_time

let string_of_prover p = Pp.string_of_wnl print_prover p

let rec stats_of_goal prefix_name stats goal =
  stats.nb_goals <- stats.nb_goals + 1;
  let proof_list =
    PHprover.fold
      (fun prover proof_attempt acc ->
        match proof_attempt.proof_state with
          | Done result ->
            begin
              match result.Call_provers.pr_answer with
                | Call_provers.Valid ->
                  (prover, result.Call_provers.pr_time) :: acc
                | _ ->
                  acc
            end
          | _ -> acc)
      goal.goal_external_proofs
      []
  in
  List.iter (update_perf_stats stats) proof_list;
  PHstr.iter (stats_of_transf prefix_name stats) goal.goal_transformations;
  if not goal.goal_verified then
    let goal_name = prefix_name ^ goal.goal_name.Ident.id_string in
    stats.no_proof <- Sstr.add goal_name stats.no_proof
  else
    begin
      stats.nb_proved_goals <- stats.nb_proved_goals + 1;
      match proof_list with
      | [ (prover, _) ] ->
        let goal_name = prefix_name ^ goal.goal_name.Ident.id_string in
        stats.only_one_proof <-
          Sstr.add
          (goal_name ^ " : " ^ (string_of_prover prover))
          stats.only_one_proof
      | _ -> ()
    end

and stats_of_transf prefix_name stats _ transf =
  let prefix_name = prefix_name ^ transf.transf_name  ^ " / " in
  List.iter (stats_of_goal prefix_name stats) transf.transf_goals

let stats_of_theory file stats theory =
  let goals = theory.theory_goals in
  let prefix_name = file.file_name ^ " / " ^ theory.theory_name.Ident.id_string
    ^  " / " in
  List.iter (stats_of_goal prefix_name stats) goals

let stats_of_file stats _ file =
  let theories = file.file_theories in
  List.iter (stats_of_theory file stats) theories

let fill_prover_data stats session =
  Sprover.iter
    (fun prover ->
      Hprover.add stats.prover_data prover
        (prover.prover_name ^ " " ^ prover.prover_version))
    (get_used_provers session)

let finalize_stats stats =
  Hprover.iter
    (fun prover time ->
      let n = Hprover.find stats.prover_num_proofs prover in
      Hprover.replace stats.prover_avg_time prover
        (time /. (float_of_int n)))
    stats.prover_avg_time

let print_stats stats =
  printf "== Number of goals ==@\n  total: %d  proved: %d@\n@\n"
    stats.nb_goals stats.nb_proved_goals;

  printf "== Goals not proved ==@\n  @[";
  Sstr.iter (fun s -> printf "%s@\n" s) stats.no_proof;
  printf "@]@\n";

  printf "== Goals proved by only one prover ==@\n  @[";
  Sstr.iter (fun s -> printf "%s@\n" s) stats.only_one_proof;
  printf "@]@\n";

  printf "== Number of proofs per prover ==@\n  @[";
  Hprover.iter (fun prover n -> printf "%-10s: %d@\n"
    (string_of_prover prover) n)
    stats.prover_num_proofs;
  printf "@]@\n";

  printf "== Minimum time per prover ==@\n  @[";
  Hprover.iter (fun prover time -> printf "%-10s : %.3f s@\n"
    (string_of_prover prover) time)
    stats.prover_min_time;
  printf "@]@\n";

  printf "== Maximum time per prover ==@\n  @[";
  Hprover.iter (fun prover time -> printf "%-10s : %.3f s@\n"
    (string_of_prover prover) time)
    stats.prover_max_time;
  printf "@]@\n";

  printf "== Average time per prover ==@\n  @[";
  Hprover.iter (fun prover time -> printf "%-10s : %.3f s@\n"
    (string_of_prover prover) time)
    stats.prover_avg_time;
  printf "@]@\n"

let run_one fname =
  let project_dir = Session.get_project_dir fname in
  if !opt_project_dir then printf "%s@." project_dir;
  let session = Session.read_session project_dir in
  let sep = if !opt_print0 then Pp.print0 else Pp.newline in
  if !opt_print_provers then
    printf "%a@."
      (Pp.print_iter1 Sprover.iter sep print_prover)
      (get_used_provers session);
  if !opt_print_edited then
    session_iter_proof_attempt
      (fun pr ->
        Util.option_iter (fun s -> printf "%s%a" s sep ())
          (get_edited_as_abs session pr))
      session;
  if !opt_tree_print then
    printf "%a@." print_session session;
  if !opt_stats_print then
    begin
      let stats = new_proof_stats () in
      fill_prover_data stats session;
      PHstr.iter (stats_of_file stats) session.session_files;
      finalize_stats stats;
      print_stats stats
    end


let run () =
  let _,_,should_exit1 = read_env_spec () in
  if should_exit1 then exit 1;
  iter_files run_one


let cmd =
  { cmd_spec = spec;
    cmd_desc = "print informations and statistics about a session.";
    cmd_name = "info";
    cmd_run  = run;
  }


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3session.byte"
End:
*)
