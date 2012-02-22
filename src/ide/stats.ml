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
module C = Whyconf

open Session

let includes = ref []
let files = Queue.create ()
let opt_version = ref false
let opt_stats = ref true
let opt_config = ref None
let allow_obsolete = ref true

let spec = Arg.align [
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> add s to loadpath") ;
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " Same as -C";
  ("--strict",
   Arg.Clear allow_obsolete,
   " Forbid obsolete session");
  ("-v",
   Arg.Set opt_version,
   " print version information") ;
    Debug.Opt.desc_debug_list;
    Debug.Opt.desc_debug_all;
    Debug.Opt.desc_debug;
]

let version_msg = Format.sprintf "Why3 statistics, version 0.1"

let usage_str = Format.sprintf
  "Usage: %s [options] [<file.why>|<project directory>]"
  (Filename.basename Sys.argv.(0))

let set_file f = Queue.add f files

let () = Arg.parse spec set_file usage_str

let () =
  if !opt_version then begin
    Format.printf "%s@." version_msg;
    exit 0
  end

let allow_obsolete = !allow_obsolete

let () =
  Debug.Opt.set_flags_selected ();
  if  Debug.Opt.option_list () then exit 0

let string_of_prover p = Pp.string_of_wnl C.print_prover p

type proof_stats =
    { mutable no_proof : Sstr.t;
      mutable only_one_proof : Sstr.t;
      prover_min_time : float C.Hprover.t;
      prover_avg_time : float C.Hprover.t;
      prover_max_time : float C.Hprover.t;
      prover_num_proofs : int C.Hprover.t;
      prover_data : (string) C.Hprover.t
    }

let new_proof_stats () =
  { no_proof = Sstr.empty;
    only_one_proof = Sstr.empty;
    prover_min_time = C.Hprover.create 3;
    prover_avg_time = C.Hprover.create 3;
    prover_max_time = C.Hprover.create 3;
    prover_num_proofs =  C.Hprover.create 3;
    prover_data = C.Hprover.create 3 }

let apply_f_on_hashtbl_entry ~tbl ~f ~name  =
  try
    let cur_time = C.Hprover.find tbl name in
    C.Hprover.replace tbl name (f (Some cur_time))
  with Not_found ->
    C.Hprover.add tbl name (f None)

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

let rec stats_of_goal prefix_name stats goal =
  let ext_proofs = goal.goal_external_proofs in
  let proof_id = prefix_name ^ goal.goal_name.Ident.id_string in
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
      ext_proofs
      [] in
  let no_transf = PHstr.length goal.goal_transformations = 0 in
  begin match proof_list with
    | [] when no_transf ->
      stats.no_proof <- Sstr.add proof_id stats.no_proof
    | [ (prover, time) ] when no_transf ->
      stats.only_one_proof <-
        Sstr.add
        (proof_id ^ " : " ^ (string_of_prover prover))
           stats.only_one_proof;
      update_perf_stats stats (prover, time)
    | _ ->
      List.iter (update_perf_stats stats) proof_list end;
  PHstr.iter (stats_of_transf prefix_name stats) goal.goal_transformations

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
  C.Sprover.iter
    (fun prover ->
      C.Hprover.add stats.prover_data prover
        (prover.C.prover_name ^ " " ^ prover.C.prover_version))
    (get_used_provers session)

let extract_stats_from_file stats fname =
  let project_dir = get_project_dir fname in
  try
    let session = read_session project_dir in
    fill_prover_data stats session;
    PHstr.iter (stats_of_file stats) session.session_files
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "Error while opening session with database '%s' : %a@." project_dir
      Exn_printer.exn_printer e;
    eprintf "Aborting...@.";
    exit 1

let finalize_stats stats =
  C.Hprover.iter
    (fun prover time ->
      let n = C.Hprover.find stats.prover_num_proofs prover in
      C.Hprover.replace stats.prover_avg_time prover
        (time /. (float_of_int n)))
    stats.prover_avg_time

let print_stats stats =
  printf "== Provers available ==@\n  @[";
  C.Hprover.iter (fun prover data -> printf "%-10s: %s@\n"
    (string_of_prover prover) data)
    stats.prover_data;
  printf "@]@\n";

  printf "== Goals not proved ==@\n  @[";
  Sstr.iter (fun s -> printf "%s@\n" s) stats.no_proof;
  printf "@]@\n";

  printf "== Goals proved by only one prover ==@\n  @[";
  Sstr.iter (fun s -> printf "%s@\n" s) stats.only_one_proof;
  printf "@]@\n";

  printf "== Number of proofs per prover ==@\n  @[";
  C.Hprover.iter (fun prover n -> printf "%-10s: %d@\n"
    (string_of_prover prover) n)
    stats.prover_num_proofs;
  printf "@]@\n";

  printf "== Minimum time per prover ==@\n  @[";
  C.Hprover.iter (fun prover time -> printf "%-10s : %.3f s@\n"
    (string_of_prover prover) time)
    stats.prover_min_time;
  printf "@]@\n";

  printf "== Maximum time per prover ==@\n  @[";
  C.Hprover.iter (fun prover time -> printf "%-10s : %.3f s@\n"
    (string_of_prover prover) time)
    stats.prover_max_time;
  printf "@]@\n";

  printf "== Average time per prover ==@\n  @[";
  C.Hprover.iter (fun prover time -> printf "%-10s : %.3f s@\n"
    (string_of_prover prover) time)
    stats.prover_avg_time;
  printf "@]@\n"

let () =
  Queue.iter (fun fname ->
    let stats = new_proof_stats () in
    let _ = extract_stats_from_file stats fname in
    finalize_stats stats;
    print_stats stats) files
