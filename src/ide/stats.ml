(**************************************************************************)
(*                                                                        *)
(*  copyright 2011 David MENTRE <dmentre@linux-france.org>                *)
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
open Util
open Session_ro

let includes = ref []
let file = ref None
let opt_version = ref false
let opt_stats = ref true

type proof_stats =
    { mutable no_proof : Sstr.t;
      mutable only_one_proof : Sstr.t;
      prover_min_time : (string, float) Hashtbl.t;
      prover_avg_time : (string, float) Hashtbl.t;
      prover_max_time : (string, float) Hashtbl.t;
      prover_num_proofs : (string, int) Hashtbl.t;
      prover_data : (string, string) Hashtbl.t
    }

let new_proof_stats () =
  { no_proof = Sstr.empty;
    only_one_proof = Sstr.empty;
    prover_min_time = Hashtbl.create 3;
    prover_avg_time = Hashtbl.create 3;
    prover_max_time = Hashtbl.create 3;
    prover_num_proofs =  Hashtbl.create 3;
    prover_data = Hashtbl.create 3 }

let apply_f_on_hashtbl_entry ~tbl ~f ~name  =
  try
    let cur_time = Hashtbl.find tbl name in
    Hashtbl.replace tbl name (f (Some cur_time))
  with Not_found ->
    Hashtbl.add tbl name (f None)

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

let stats_of_goal file theory stats goal =
  let ext_proofs = goal.external_proofs in
  let proof_id = file.file_name ^ " / " ^ theory.theory_name
    ^  " / " ^ goal.goal_name in
  let proof_list =
    Mstr.fold
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
      ext_proofs
      [] in
  match proof_list with
    | [] ->
      stats.no_proof <- Sstr.add proof_id stats.no_proof
    | [ (prover, time) ] ->
      stats.only_one_proof <-
        Sstr.add (proof_id ^ " : " ^ prover) stats.only_one_proof;
      update_perf_stats stats (prover, time)
    | _ :: _ ->
      List.iter (update_perf_stats stats) proof_list

let stats_of_theory file stats theory =
  let goals = theory.goals in
  List.iter (stats_of_goal file theory stats) goals

let stats_of_file stats file =
  let theories = file.theories in
  List.iter (stats_of_theory file stats) theories

let fill_prover_data stats =
  let provers = Mstr.empty (* FIXME get_provers ()*) in
  Mstr.iter
    (fun prover data ->
      Hashtbl.add stats.prover_data prover
        (data.Session.prover_name ^ " " ^ data.Session.prover_version))
    provers

let extract_stats_from_file stats fname =
  let env = read_config ~includes:!includes None in
  let project_dir = get_project_dir fname in
  try
    let file_list = read_project_dir ~allow_obsolete:true ~env project_dir in
    fill_prover_data stats;
    List.iter (stats_of_file stats) file_list
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "Error while opening session with database '%s' : %a@." project_dir
      Exn_printer.exn_printer e;
    eprintf "Aborting...@.";
    exit 1

let finalize_stats stats =
  Hashtbl.iter
    (fun prover time ->
      let n = Hashtbl.find stats.prover_num_proofs prover in
      Hashtbl.replace stats.prover_avg_time prover (time /. (float_of_int n)))
    stats.prover_avg_time

let print_stats stats =
  printf "== Provers used ==@\n  @[";
  Hashtbl.iter (fun prover data -> printf "%-10s: %s@\n" prover data)
    stats.prover_data;
  printf "@]@\n";

  printf "== Goals not proved ==@\n  @[";
  Sstr.iter (fun s -> printf "%s@\n" s) stats.no_proof;
  printf "@]@\n";

  printf "== Goals proved by only one prover ==@\n  @[";
  Sstr.iter (fun s -> printf "%s@\n" s) stats.only_one_proof;
  printf "@]@\n";

  printf "== Number of proofs per prover ==@\n  @[";
  Hashtbl.iter (fun prover n -> printf "%-10s: %d@\n" prover n)
    stats.prover_num_proofs;
  printf "@]@\n";

  printf "== Minimum time per prover ==@\n  @[";
  Hashtbl.iter (fun prover time -> printf "%-10s : %.3f s@\n" prover time)
    stats.prover_min_time;
  printf "@]@\n";

  printf "== Maximum time per prover ==@\n  @[";
  Hashtbl.iter (fun prover time -> printf "%-10s : %.3f s@\n" prover time)
    stats.prover_max_time;
  printf "@]@\n";

  printf "== Average time per prover ==@\n  @[";
  Hashtbl.iter (fun prover time -> printf "%-10s : %.3f s@\n" prover time)
    stats.prover_avg_time;
  printf "@]@\n"

let spec = Arg.align [
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> add s to loadpath") ;
  ("-v",
   Arg.Set opt_version,
   " print version information") ;
]

let version_msg = Format.sprintf "Why3 statistics, version 0.1"

let usage_str = Format.sprintf
  "Usage: %s [options] [<file.why>|<project directory>]"
  (Filename.basename Sys.argv.(0))

let set_file f = match !file with
  | Some _ ->
      raise (Arg.Bad "only one parameter")
  | None ->
      file := Some f

let _ =
  Arg.parse spec set_file usage_str;

  if !opt_version then begin
    Format.printf "%s@." version_msg;
    exit 0
  end;

  let fname = match !file with
    | None ->
      Arg.usage spec usage_str;
      exit 1
    | Some f ->
      f in

  let stats = new_proof_stats () in
  let _ = extract_stats_from_file stats fname in
  finalize_stats stats;
  print_stats stats
