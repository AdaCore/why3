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

(**************************************************************************)
(* Specific source code for computing statistics is a contribution by     *)
(* David MENTRE <dmentre@linux-france.org>, 2011                          *)
(**************************************************************************)

open Why3
open Why3session_lib
open Whyconf
open Format
open Session_itp
open Wstdlib

let opt_print_provers = ref false
let opt_print_edited = ref false
let opt_tree_print = ref false
let opt_stats_print = ref false
let opt_hist_print = ref false
let opt_project_dir = ref false
let opt_print0 = ref false

let spec =
  ("--provers", Arg.Set opt_print_provers,
   " provers used in the session" ) ::
  ("--edited-files", Arg.Set opt_print_edited,
   " edited proof scripts in the session" ) ::
  ("--stats", Arg.Set opt_stats_print,
   " print various proofs statistics" ) ::
  ("--graph", Arg.Set opt_hist_print,
   " print a graph of the total time needed for \
     proving a given number of goals for each provers" ) ::
  ("--tree", Arg.Set opt_tree_print,
   " session contents as a tree in textual format" ) ::
  ("--dir", Arg.Set opt_project_dir,
   " print the directory of the session" ) ::
  ("--print0", Arg.Set opt_print0,
   " use the null character instead of newline" ) ::
    common_options


type proof_stats =
    { mutable nb_root_goals : int;
      mutable nb_sub_goals : int;
      mutable max_time : float;
      mutable nb_proved_root_goals : int;
      mutable nb_proved_sub_goals : int;
      mutable no_proof : Sstr.t;
      mutable only_one_proof : Sstr.t;
      prover_hist : int Mfloat.t Hprover.t;
      prover_min_time : float Hprover.t;
      prover_sum_time : float Hprover.t;
      prover_max_time : float Hprover.t;
      prover_num_proofs : int Hprover.t;
      (* prover_data : (string) Hprover.t *)
    }

let new_proof_stats () =
  { nb_root_goals = 0;
    nb_sub_goals = 0;
    max_time = 0.0;
    nb_proved_root_goals = 0;
    nb_proved_sub_goals = 0;
    no_proof = Sstr.empty;
    only_one_proof = Sstr.empty;
    prover_hist = Hprover.create 3;
    prover_min_time = Hprover.create 3;
    prover_sum_time = Hprover.create 3;
    prover_max_time = Hprover.create 3;
    prover_num_proofs =  Hprover.create 3;
    (* prover_data = Hprover.create 3  *)}

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

let update_sum_time tbl (prover, time) =
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

let update_hist tbl (prover, time) =
  let h =
    try Hprover.find tbl prover
    with Not_found -> Mfloat.empty
  in
  let h =
    try
      let c = Mfloat.find time h in
      Mfloat.add time (succ c) h
    with Not_found ->
      Mfloat.add time 1 h
  in
  Hprover.replace tbl prover h

let update_perf_stats stats ((_,t) as prover_and_time) =
  if t > stats.max_time then stats.max_time <- t;
  update_min_time stats.prover_min_time prover_and_time;
  update_max_time stats.prover_max_time prover_and_time;
  update_sum_time stats.prover_sum_time prover_and_time;
  update_count stats.prover_num_proofs prover_and_time;
  update_hist stats.prover_hist prover_and_time

let string_of_prover p = Pp.string_of_wnl print_prover p

let rec stats_of_goal ~root prefix_name stats ses goal =
  if root
  then stats.nb_root_goals <- stats.nb_root_goals + 1
  else stats.nb_sub_goals <- stats.nb_sub_goals + 1;
  let proof_list =
    List.fold_left
      (fun acc pa ->
        match pa.proof_state with
          | Some result ->
            begin
              match result.Call_provers.pr_answer with
                | Call_provers.Valid ->
                  (pa.prover, result.Call_provers.pr_time) :: acc
                | _ ->
                  acc
            end
          | _ -> acc)
      [] (get_proof_attempts ses goal)
  in
  List.iter (update_perf_stats stats) proof_list;
  List.iter (stats_of_transf prefix_name stats ses) (get_transformations ses goal);
  let goal_name = prefix_name ^ (get_proof_name ses goal).Ident.id_string in
  if not (pn_proved ses goal) then
    stats.no_proof <- Sstr.add goal_name stats.no_proof
  else
    begin
      if root then
        stats.nb_proved_root_goals <- stats.nb_proved_root_goals + 1
      else
        stats.nb_proved_sub_goals <- stats.nb_proved_sub_goals + 1;
      match proof_list with
      | [ (prover, _) ] ->
        stats.only_one_proof <-
          Sstr.add
          (goal_name ^ ": " ^ (string_of_prover prover))
          stats.only_one_proof
      | _ -> ()
    end

and stats_of_transf prefix_name stats ses transf =
  let prefix_name = prefix_name ^ (get_transf_string ses transf) ^ " / " in
  List.iter (stats_of_goal ~root:false prefix_name stats ses) (get_sub_tasks ses transf)

let stats_of_theory file stats ses theory =
  let goals = theory_goals theory in
  let prefix_name = string_of_file_path (file_path file) ^ " / " ^
                      (theory_name theory).Ident.id_string ^  " / " in
  List.iter (stats_of_goal ~root:true prefix_name stats ses) goals

let stats_of_file stats ses _ file =
  let theories = file_theories file in
  List.iter (stats_of_theory file stats ses) theories



type goal_stat =
  | No of (transID * (proofNodeID * goal_stat) list) list
  | Yes of (prover * float) list * (transID * (proofNodeID * goal_stat) list) list

let rec stats2_of_goal ~nb_proofs ses g : goal_stat =
  let proof_list =
    List.fold_left
      (fun acc proof_attempt ->
        match proof_attempt.proof_state with
          | Some result ->
            begin
              match result.Call_provers.pr_answer with
                | Call_provers.Valid ->
                  (proof_attempt.prover, result.Call_provers.pr_time) :: acc
                | _ ->
                  acc
            end
          | _ -> acc)
      [] (get_proof_attempts ses g)
  in
  let l =
    List.fold_left
      (fun acc tr ->
        match stats2_of_transf ~nb_proofs ses tr with
          | [] -> acc
          | r -> (tr,List.rev r)::acc)
      [] (get_transformations ses g)
  in
  if match nb_proofs with
    | 0 -> not (pn_proved ses g)
    | 1 -> List.length proof_list = 1
    | _ -> assert false
      then Yes(proof_list,l) else No(l)

and stats2_of_transf ~nb_proofs ses tr : (proofNodeID * goal_stat) list =
  List.fold_left
    (fun acc g ->
      match stats2_of_goal ~nb_proofs ses g with
        | No [] -> acc
        | r -> (g,r)::acc)
    [] (get_sub_tasks ses tr)

let print_res ~time fmt (p,t) =
  fprintf fmt "%a" print_prover p;
  if time then fprintf fmt " (%.2f)" t

let rec print_goal_stats ~time depth ses (g,l) =
  for _i=1 to depth do printf "  " done;
  printf "+-- goal %s" (get_proof_name ses g).Ident.id_string;
  match l with
    | No l ->
      printf "@\n";
      List.iter (print_transf_stats ~time (depth+1) ses) l
    | Yes(pl,l) ->
      begin
        match pl with
          | [] -> printf "@\n"
          | _ -> printf ": %a@\n"
            (Pp.print_list pp_print_space (print_res ~time)) pl
      end;
      List.iter (print_transf_stats ~time (depth+1) ses) l

and print_transf_stats ~time depth ses (tr,l) =
  for _i=1 to depth do printf "  " done;
  printf "+-- transformation %s@\n" (get_transf_string ses tr);
  List.iter (print_goal_stats ~time (depth+1) ses) l

let stats2_of_theory ~nb_proofs ses th =
  List.fold_left
    (fun acc g ->
      match stats2_of_goal ~nb_proofs ses g with
        | No [] -> acc
        | r -> (g,r)::acc)
    [] (theory_goals th)

let print_theory_stats ~time ses (th,r) =
  printf "  +-- theory %s@\n" (theory_name th).Ident.id_string;
  List.iter (print_goal_stats ~time 2 ses) r

let stats2_of_file ~nb_proofs ses file =
  List.fold_left
    (fun acc th ->
      match stats2_of_theory ~nb_proofs ses th with
        | [] -> acc
        | r -> (th,List.rev r)::acc)
    [] (file_theories file)

let stats2_of_session ~nb_proofs ses acc =
  Hfile.fold
    (fun _ f acc ->
      match stats2_of_file ~nb_proofs ses f with
        | [] -> acc
        | r -> (f,List.rev r)::acc)
    (get_files ses) acc

let print_file_stats ~time ses (f,r) =
  printf "+-- file [%a]@\n" print_file_path (file_path f);
  List.iter (print_theory_stats ~time ses) r

let print_session_stats ~time ses = List.iter (print_file_stats ~time ses)


(*
let fill_prover_data stats session =
  Sprover.iter
    (fun prover ->
      Hprover.add stats.prover_data prover
        (string_of_prover prover))
    (get_used_provers session)
*)

(*
let finalize_stats stats =
  Hprover.iter
    (fun prover time ->
      let n = Hprover.find stats.prover_num_proofs prover in
      Hprover.replace stats.prover_avg_time prover
        (time /. (float_of_int n)))
    stats.prover_avg_time
*)

let print_stats ses r0 r1 stats =
  printf "== Number of root goals ==@\n  total: %d  proved: %d@\n@\n"
    stats.nb_root_goals stats.nb_proved_root_goals;

  printf "== Number of sub goals ==@\n  total: %d  proved: %d@\n@\n"
    stats.nb_sub_goals stats.nb_proved_sub_goals;

  printf "== Goals not proved ==@\n  @[";
  print_session_stats ~time:false ses r0;
  (* Sstr.iter (fun s -> printf "%s@\n" s) stats.no_proof; *)
  printf "@]@\n";

  printf "== Goals proved by only one prover ==@\n  @[";
  print_session_stats ~time:false ses r1;
  (* Sstr.iter (fun s -> printf "%s@\n" s) stats.only_one_proof; *)
  printf "@]@\n";

  printf "== Statistics per prover: number of proofs, time (minimum/maximum/average) in seconds ==@\n  @[";
  Hprover.iter (fun prover n ->
    let sum_times = Hprover.find stats.prover_sum_time prover in
    printf "%-20s: %3d %6.2f %6.2f %6.2f@\n"
      (string_of_prover prover) n
      (Hprover.find stats.prover_min_time prover)
      (Hprover.find stats.prover_max_time prover)
      (sum_times /. (float_of_int n)))
    stats.prover_num_proofs;
  printf "@]@\n"


let run_one stats r0 r1 fname =
  let ses,_ = read_session fname in
  let sep = if !opt_print0 then Pp.print0 else Pp.newline in
  if !opt_print_provers then
    printf "%a@."
      (Pp.print_iter1 Sprover.iter sep print_prover)
      (get_used_provers ses);
  if !opt_print_edited then begin
      failwith "option print_edited non implemented" (* TODO *)
(*    session_iter_proof_attempt
      (fun pr ->
        Opt.iter (fun s -> printf "%s%a" s sep ())
          (get_edited_as_abs session pr))
      session;
 *)
    end;
  if !opt_tree_print then
    begin
      failwith "option print_tree not implemented"
(*
      printf "%a@." print_session ses;
 *)
    end;
  if !opt_stats_print || !opt_hist_print then
    begin
      (* fill_prover_data stats session; *)
      Hfile.iter (stats_of_file stats ses) (get_files ses);
      r0 := stats2_of_session ~nb_proofs:0 ses !r0;
      r1 := stats2_of_session ~nb_proofs:1 ses !r1
    end;
  if !opt_stats_print then
    begin
      (* finalize_stats stats; *)
      print_stats ses !r0 !r1 stats
    end

(**** print histograms ******)

let print_hist stats =
  let main_file,main_ch =
    Filename.open_temp_file "why3session" ".gnuplot"
  in
  let main_fmt = formatter_of_out_channel main_ch in
  fprintf main_fmt "set logscale y@\n";
  fprintf main_fmt "set key rmargin@\n";
  let max_sum_times =
    Hprover.fold
      (fun _ s acc -> max s acc)
      stats.prover_sum_time 0.0
  in
  let (_:int) =
  Hprover.fold
    (fun p h acc ->
      let pf,ch = Filename.open_temp_file "why3session" ".data" in
      if acc = 1 then
        fprintf main_fmt "plot [0:%d] [0.1:%.2f] "
          (stats.nb_proved_sub_goals + stats.nb_proved_root_goals)
          max_sum_times
      else
        fprintf main_fmt "replot";
      fprintf main_fmt
        " \"%s\" using 2:1 title \"%s\" with linespoints ps 0.2@\n"
        pf (string_of_prover p);
      let fmt = formatter_of_out_channel ch in
      (* The time is also accumulated in order to obtain the total cpu time
          taken to reach the given number of proved goal *)
      (* fprintf fmt "0.1 0@\n"; *)
      let (_ : float * int) =
        Mfloat.fold
          (fun t c (acct,accc) ->
            let accc = c + accc in
            let acct = (float c) *. t +. acct in
            fprintf fmt "%.2f %d@\n" acct accc;
            (acct,accc))
          h (0.1,0)
      in
      fprintf fmt "@.";
      close_out ch;
      acc+1)
    stats.prover_hist 1
  in
  fprintf main_fmt "pause -1 \"Press any key\"@\n";
  fprintf main_fmt "set terminal pdfcairo@\n";
  fprintf main_fmt "set output \"why3session.pdf\"@\n";
  fprintf main_fmt "replot@.";
  close_out main_ch;
  let cmd = "gnuplot " ^ main_file in
  eprintf "Running command %s@." cmd;
  let ret = Sys.command cmd in
  if ret <> 0 then
    eprintf "Command %s failed@." cmd
  else
    eprintf "See also results in file why3session.pdf@."

(****** run on all files  ******)

let run () =
  let _env,_config,should_exit1 = read_env_spec () in
  if should_exit1 then exit 1;
  let stats = new_proof_stats () in
  let r0 = ref [] and r1 = ref [] in
  iter_files (run_one stats r0 r1);
  if !opt_hist_print then print_hist stats


let cmd =
  { cmd_spec = spec;
    cmd_desc = "print informations and statistics about a session";
    cmd_name = "info";
    cmd_run  = run;
  }


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3session.byte"
End:
*)
