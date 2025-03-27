(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
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
let opt_provers_stats = ref false
let opt_session_stats = ref false
let opt_project_dir = ref false
let opt_print0 = ref false
let opt_graph_all = ref false
let opt_graph_hist = ref false
let opt_graph_scatter = ref false

let set_opt_graph graph_type =
    match graph_type with
    | Some "scatter"  -> opt_graph_scatter := true
    | Some "hist"     -> opt_graph_hist:= true
    | Some "all"      -> opt_graph_all := true
    | Some _          -> opt_graph_all := true;
                         eprintf "Unknown graph style, using default: all@."
    | None            -> opt_graph_all := true

let spec =
  let open Getopt in
  [ KLong "provers", Hnd0 (fun () -> opt_print_provers := true),
    " print provers used in the session";
    KLong "session-stats", Hnd0 (fun () -> opt_session_stats := true),
    " print proofs statistics per sessions";
    KLong "provers-stats", Hnd0 (fun () -> opt_provers_stats := true),
    " print statistics of prover usage for all given sessions";
    KLong "dir", Hnd0 (fun () -> opt_project_dir := true),
    " print the directory of the session";
    KLong "print0", Hnd0 (fun () -> opt_print0 := true),
    " use the null character instead of newline";
    KLong "graph", HndOpt (AString, set_opt_graph),
    "[all|hist|scatter] print graphs comparing the time used\nby different provers (default: all)";
  ]

let warn_no_data =
  Loc.register_warning "no_graph_data" "Warn that not enough data is present for generating graphs or reports"

type proof_stats =
    { mutable nb_root_goals : int;
      mutable nb_sub_goals : int;
      mutable max_time : float;
      mutable nb_proved_root_goals : int;
      mutable nb_proved_sub_goals : int;
      mutable no_proof : Sstr.t;
      mutable only_one_proof : Sstr.t;
      graph_data : int Mfloat.t Hprover.t;
      prover_min_time : float Hprover.t;
      prover_sum_time : float Hprover.t;
      prover_max_time : float Hprover.t;
      prover_successful_proofs : int Hprover.t;
      prover_all_proofs : int Hprover.t;
      mutable proof_node_proofs : (session * (Ident.ident * float Mprover.t) Hpn.t) list;
    }

let new_proof_stats () =
  { nb_root_goals = 0;
    nb_sub_goals = 0;
    max_time = 0.0;
    nb_proved_root_goals = 0;
    nb_proved_sub_goals = 0;
    no_proof = Sstr.empty;
    only_one_proof = Sstr.empty;
    graph_data = Hprover.create 3;
    prover_min_time = Hprover.create 3;
    prover_sum_time = Hprover.create 3;
    prover_max_time = Hprover.create 3;
    prover_successful_proofs =  Hprover.create 3;
    prover_all_proofs =  Hprover.create 3;
    proof_node_proofs = []}

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
  update_count stats.prover_successful_proofs prover_and_time;
  update_hist stats.graph_data prover_and_time

let string_of_prover p = Pp.string_of_wnl print_prover p

let rec stats_of_goal ~root prefix_name stats hpn ses goal =
  if root
  then stats.nb_root_goals <- stats.nb_root_goals + 1
  else stats.nb_sub_goals <- stats.nb_sub_goals + 1;
  let proof_list =
    List.fold_left
      (fun acc pa ->
         let n = try
             Hprover.find stats.prover_all_proofs pa.prover
           with Not_found -> 0
         in
         Hprover.replace stats.prover_all_proofs pa.prover (n+1);
        match pa.proof_state with
          | Some result ->
            begin
              match result.Call_provers.pr_answer with
                | Call_provers.Valid ->
                  Mprover.add pa.prover result.Call_provers.pr_time acc
                | _ ->
                  acc
            end
          | _ -> acc)
      Mprover.empty (get_proof_attempts ses goal)
  in
  let goal_name = get_proof_name ses goal in
  Hpn.add hpn goal (goal_name,proof_list);
  Mprover.iter (fun x y -> update_perf_stats stats (x,y)) proof_list;
  List.iter (stats_of_transf prefix_name stats hpn ses) (get_transformations ses goal);
  let goal_name = prefix_name ^ (get_proof_name ses goal).Ident.id_string in
  if not (pn_proved ses goal) then
    stats.no_proof <- Sstr.add goal_name stats.no_proof
  else
    begin
      if root then
        stats.nb_proved_root_goals <- stats.nb_proved_root_goals + 1
      else
        stats.nb_proved_sub_goals <- stats.nb_proved_sub_goals + 1;
      if Mprover.cardinal proof_list = 1 then
        let (prover, _) = Mprover.choose proof_list in
        stats.only_one_proof <-
          Sstr.add
          (goal_name ^ ": " ^ (string_of_prover prover))
          stats.only_one_proof
    end

and stats_of_transf prefix_name stats hpn ses transf =
  let prefix_name = prefix_name ^ (get_transf_string ses transf) ^ " / " in
  List.iter (stats_of_goal ~root:false prefix_name stats hpn ses) (get_sub_tasks ses transf)

let stats_of_theory file stats hpn ses theory =
  let goals = theory_goals theory in
  let prefix_name = Pp.sprintf "%a" Sysutil.print_file_path (file_path file) ^ " / " ^
                      (theory_name theory).Ident.id_string ^  " / " in
  List.iter (stats_of_goal ~root:true prefix_name stats hpn ses) goals

let stats_of_file stats ses _ file =
  let hpn = Hpn.create 3 in
  let theories = file_theories file in
  List.iter (stats_of_theory file stats hpn ses) theories;
  stats.proof_node_proofs <- (ses,hpn) :: stats.proof_node_proofs

type goal_stat =
  | No of (transID * (proofNodeID * goal_stat) list) list
  | Yes of (float Mprover.t) * (transID * (proofNodeID * goal_stat) list) list

let rec stats2_of_goal ~nb_proofs ses g : goal_stat =
  let proof_list =
    List.fold_left
      (fun acc proof_attempt ->
        match proof_attempt.proof_state with
          | Some result ->
            begin
              match result.Call_provers.pr_answer with
                | Call_provers.Valid ->
                  Mprover.add proof_attempt.prover result.Call_provers.pr_time acc
                | _ ->
                  acc
            end
          | _ -> acc)
      Mprover.empty (get_proof_attempts ses g)
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
    | 1 -> Mprover.cardinal proof_list = 1
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
  print_prover fmt p;
  if time then fprintf fmt " (%.2f)" t

let rec print_goal_stats ~time depth ses (g,l) =
  for _i=1 to depth do printf "  " done;
  printf "+-- goal %s" (get_proof_name ses g).Ident.id_string;
  match l with
    | No l ->
      printf "@\n";
      List.iter (print_transf_stats ~time (depth+1) ses) l
    | Yes(pl,l) ->
      let pl = Mprover.bindings pl in
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

let stats2_of_session ~nb_proofs ses =
  Hfile.fold
    (fun _ f acc ->
       match stats2_of_file ~nb_proofs ses f with
       | [] -> acc
       | r -> (f,List.rev r)::acc)
    (get_files ses) []

let print_file_stats ~time ses (f,r) =
  printf "+-- file [%a]@\n" Sysutil.print_file_path (file_path f);
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

let print_session_stats ses r0 r1 stats =
  printf "= Statistics for session %s@\n@\n" (get_dir ses);
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
  printf "@]@\n"


let print_overall_stats stats =
  printf "== Statistics per prover: number of proof attempts, successful ones, time (minimum/maximum/average) in seconds ==@\n  @[";
  let l = Hprover.fold (fun prover n acc ->
      let ns,min,max,avg =
        try
          let ns = Hprover.find stats.prover_successful_proofs prover in
          let sum_times = Hprover.find stats.prover_sum_time prover in
          ns,Hprover.find stats.prover_min_time prover,
          Hprover.find stats.prover_max_time prover,
          sum_times /. (float_of_int n)
        with Not_found -> 0,0.0,0.0,0.0
      in (string_of_prover prover,n,ns,min,max,avg)::acc)
      stats.prover_all_proofs []
  in
  let l = List.sort (fun (p1,_,_,_,_,_) (p2,_,_,_,_,_) -> compare p1 p2) l in
  List.iter (fun (p,n,ns, min,max,avg) ->
    printf "%-30s: %5d %5d %6.2f %6.2f %6.2f@\n" p n ns min max avg)
    l;
  printf "@]@\n"

let number_of_sessions = ref 0

let run_one stats fname =
  incr number_of_sessions;
  let ses = read_session fname in
  let sep = if !opt_print0 then Pp.print0 else Pp.newline in
  if !opt_print_provers then
    printf "%a@."
      (Pp.print_iter1 Sprover.iter sep print_prover)
      (get_used_provers ses);
  (* fill_prover_data stats session; *)
  Hfile.iter (stats_of_file stats ses) (get_files ses);
  let r0 = stats2_of_session ~nb_proofs:0 ses in
  let r1 = stats2_of_session ~nb_proofs:1 ses in
  if !opt_session_stats then
    begin
      (* finalize_stats stats; *)
      print_session_stats ses r0 r1 stats
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
    stats.graph_data 1
  in
  fprintf main_fmt "pause -1 \"Press any key\\n\"@\n";
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

(** Generate pairs of provers for the scatter and hist plots.*)
let generate_provers_pairs stats =
  let all_provers =
    List.fold_left (fun acc (_ses,hpn) ->
        Hpn.fold (fun _pn (_,provers_and_times) acc ->
            (List.fold_left
               Sprover.add_left acc (Mprover.keys provers_and_times))
          ) hpn acc)
       Sprover.empty stats.proof_node_proofs
  in
  let (_, pairs) =
    Sprover.fold (fun prover (visited, pairs) ->
      (prover::visited, List.append pairs (List.map (fun x -> (x,prover)) visited))
    ) all_provers ([],[])
  in pairs

(** Print one comparison scatter plot for each pair of provers in the session*)
let print_compare_scatter stats =
  let all_provers_pairs = generate_provers_pairs stats
  in
  if all_provers_pairs = [] then eprintf "Not enough provers in the session@\n";
  let comparison_datafiles = List.map (
  fun (prover1, prover2) ->
    let pf,ch = Filename.open_temp_file "why3session" ".data" in
    let fmt = formatter_of_out_channel ch in
    let empty = ref true in
    let max_time = max (Hprover.find stats.prover_max_time prover1)  (Hprover.find stats.prover_max_time prover2)
    in
    let () =
      List.iter (fun (_ses, hpn) ->
          Hpn.iter (
            fun _pn (_,provers_and_times) ->
              let time1 =
                try Mprover.find prover1 provers_and_times
                with Not_found -> max_time
              in let time2 =
                   try Mprover.find prover2 provers_and_times
                   with Not_found -> max_time
              in fprintf fmt "%.2f %.2f@\n" time1 time2;
              empty := false
          ) hpn)
        stats.proof_node_proofs
    in
    let () =
      fprintf fmt "@.";
      close_out ch
    in
    if not !empty then pf else ""
    ) all_provers_pairs
  in
  let main_file,main_ch = Filename.open_temp_file "why3session" ".gnuplot"
  in
  let main_fmt = formatter_of_out_channel main_ch in
  fprintf main_fmt "set key off@\n";
  let print_plot (filename,(prover1, prover2)) =
    let max_time = max (Hprover.find stats.prover_max_time prover1) (Hprover.find stats.prover_max_time prover2)
    in
    let prover1_name = string_of_prover prover1 in
    let prover2_name = string_of_prover prover2 in
      if filename <> "" then
        (fprintf main_fmt "set title \"%s vs %s\"@\n" prover1_name prover2_name;
        fprintf main_fmt "set xlabel \"%s\" @\n" prover1_name;
        fprintf main_fmt "set ylabel \"%s\" @\n" prover2_name;
        fprintf main_fmt "plot [0:%.2f] [0:%.2f] x, '%s' with points pt 7@\n" max_time max_time filename;
        fprintf main_fmt "pause -1 \"Press any key\\n\"@\n";
        fprintf main_fmt "replot@.")
  in
  List.iter print_plot (List.combine comparison_datafiles all_provers_pairs);
  close_out main_ch;
  let cmd = "gnuplot " ^ main_file in
  eprintf "Running command %s@." cmd;
  let ret = Sys.command cmd in
  if ret <> 0 then
    eprintf "Command %s failed@." cmd

(** Print one comparison histogram for each pair of provers in the session*)
let print_compare_hist stats =
  let all_provers_pairs = generate_provers_pairs stats
  in
  if all_provers_pairs = [] then eprintf "Not enough provers in the session. No graph will be produced.@\n";
  let ratio_and_exclusives (prover1, prover2) =
    let (out_list, p1_only, p2_only) =
      List.fold_left (fun acc (_ses,hpn) ->
          Hpn.fold (
         fun _pn (ident,provers_and_times) (out_list, p1_only, p2_only) ->
      match Mprover.find_opt prover1 provers_and_times, Mprover.find_opt prover2 provers_and_times with
          | Some time1, Some time2 ->
          (* For some time, Alt-Ergo reported null times and this got stored in sessions.
          Eventually this should be removed*)
            let time1 = if (time1 = Float.zero) then time1 +. 0.000001 else time1 in
            let time2 = if (time2 = Float.zero) then time2 +. 0.000001 else time2 in
             ((time1, time2, ident.Ident.id_string) :: out_list), p1_only, p2_only
          | Some _    , None       -> (out_list, p1_only + 1, p2_only    )
          | None      , Some _     -> (out_list, p1_only    , p2_only + 1)
          | None      , None       -> (out_list, p1_only , p2_only)
       ) hpn acc)
        ([], 0, 0) stats.proof_node_proofs
    in
    let p2_name = (string_of_prover prover2) in
    let p1_name = (string_of_prover prover1) in
    if out_list == [] then
      Loc.warning warn_no_data
      "Not enough data points to compare %s and %s, graph will not be produced.@." p1_name p2_name;
    ((p1_name, p2_name), out_list |> List.sort (fun (t1a,t2a,_) (t1b,t2b,_) -> Float.compare (t1a/.t2a) (t1b/.t2b)),
    p1_only, p2_only)
  in
  let print_ratio_list (pair, ratio_list, p1_only, p2_only) =
    let datafile,ch = Filename.open_temp_file "why3session" ".data" in
    let fmt = formatter_of_out_channel ch in
    List.iter (fun (t1,t2,ident_name) -> fprintf fmt "%.6f %s %.6f %.6f@." (t1/.t2) ident_name t1 t2) ratio_list;
    fprintf fmt "@.";
    close_out ch;
    (pair, datafile, p1_only, p2_only)
  in
  let datafiles_and_exclusives =
    all_provers_pairs |> List.map ratio_and_exclusives |> List.filter (fun (_,l, _, _) -> l != []) |> List.map print_ratio_list
  in
  let main_file,main_ch = Filename.open_temp_file "why3session" ".gnuplot"
  in
  let main_fmt = formatter_of_out_channel main_ch in
  fprintf main_fmt "set key off@\n";
  let print_plot ((prover1_name, prover2_name), filename, p1_only, p2_only) =
        fprintf main_fmt {|prover1 = "%s"@.prover2 = "%s"@.|} prover1_name prover2_name;
        fprintf main_fmt {|filename = "%s"@.|} filename;
        fprintf main_fmt {|exclusives = "\n%d additional goals are only proved by ".prover1.", %d only by ".prover2@.|} p1_only p2_only;
        fprintf main_fmt
{|set key off
Label(Ident,T1,T2) = sprintf("%%s\n%%s: %%.6f\n %%s: %%.6f", stringcolumn(Ident), prover1, column(T1), prover2, column(T2))
stats filename using (log($1)) nooutput
geometric_mean = exp(STATS_mean)
set xlabel "Percentage of goals"
set ylabel sprintf("Time ratio: %%s over %%s", prover1, prover2)
set autoscale xfix
set logsc y
set ytics (1,1)
do for [i=1:5] {set ytics add (sprintf("1/%%.d",10**i) 1./10**i)}
do for [i=1:5] {set ytics add (sprintf("%%.d",10**i) 10**i)}
set xtics (0,0)
do for [i=1:10] {set xtics add (sprintf("%%d",10*i) i*STATS_records/10)}
if (geometric_mean>1) {set ytics add (sprintf("Average: %%.2f", geometric_mean) geometric_mean)}
else {if (geometric_mean != 0) {set ytics add (sprintf("Average:\n1/%%.2f", 1/geometric_mean) geometric_mean)}}
stats filename using ($1<1) nooutput prefix "IMPROV"
percent_improve = IMPROV_sum/STATS_records*100
if (percent_improve > 50) {title_string = sprintf("%%s is faster than %%s on %%.2f %%%% of %%d goals", prover1, prover2, percent_improve, STATS_records)}
else {title_string = sprintf("%%s is faster than %%s on %%.2f %%%% of %%d goals", prover2, prover1, 100-percent_improve, STATS_records)}
set title title_string.exclusives
plot filename using 0:1:(Label(2,3,4)) with labels hypertext point pointsize 0.5 linecolor rgb "blue", geometric_mean title "Mean", 1
pause -1 "Press any key\n"
replot@.|};
(*      filename using 0:1:2:(0.1) linecolor rgb "blue" with labels hypertext  *)
  in
  List.iter print_plot datafiles_and_exclusives;
  close_out main_ch;
  let cmd = "gnuplot " ^ main_file in
  eprintf "Running command %s@." cmd;
  let ret = Sys.command cmd in
  if ret <> 0 then
    eprintf "Command %s failed@." cmd
(****** run on all files  ******)

let run () =
  let _,_ = Whyconf.Args.complete_initialization () in
  let stats = new_proof_stats () in
  iter_session_files (run_one stats);
  printf "%d session(s) read, with a total of %d proof goals.@." !number_of_sessions
    (stats.nb_root_goals + stats.nb_sub_goals);
  if !opt_provers_stats then print_overall_stats stats;
  if !opt_graph_all then print_hist stats;
  if !opt_graph_scatter then print_compare_scatter stats;
  if !opt_graph_hist then print_compare_hist stats

let cmd =
  { cmd_spec = spec;
    cmd_desc = "print informations and statistics about a session";
    cmd_usage = "<session>\nPrint informations and statistics about the session.";
    cmd_name = "info";
    cmd_run  = run;
  }


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3session.byte"
End:
*)
