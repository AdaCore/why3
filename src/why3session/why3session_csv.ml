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

open Why3
open Why3session_lib
open Format

module Hprover = Whyconf.Hprover
module S = Session_itp

let orig_dir = Sys.getcwd ()

let opt_output_dir = ref "./"

let opt_provers = ref []
let opt_aggregate = ref false
let opt_print_csv = ref false

let simple_read_opt_prover s =
  try
    Whyconf.parse_filter_prover s
  with Whyconf.ParseFilterProver _ ->
    raise (Arg.Bad
             "--filter-prover name[,version[,alternative]|,,alternative] \
                regexp must start with ^")


let opt_value_not_valid = ref "-1."
type gnuplot =
  | PDF
  | PNG
  | SVG
  | QT
  | GP

let opt_gnuplot = ref []
let select_gnuplot = function
  | "pdf" -> opt_gnuplot := PDF::!opt_gnuplot
  | "png" -> opt_gnuplot := PNG::!opt_gnuplot
  | "svg" -> opt_gnuplot := SVG::!opt_gnuplot
  | "qt"  -> opt_gnuplot := QT::!opt_gnuplot
  | "gp" -> opt_gnuplot := GP::!opt_gnuplot
  | _ -> assert false (** absurd: Arg already filtered bad cases *)

type gnuplot_x =
  | Xtime
  | Xgoals

let opt_gnuplot_x = ref Xtime

let select_gnuplot_x = function
  | "time" -> opt_gnuplot_x := Xtime
  | "goals" -> opt_gnuplot_x := Xgoals
  | _ -> assert false (** absurd: Arg already filtered bad cases *)


let opt_data = ref false
let opt_by_time = ref false

let spec =
  ("-o",
   Arg.Set_string opt_output_dir,
   "<dir> where to produce files (default: session dir)") ::
  ("--filter-prover",
   Arg.String (fun s ->
     opt_provers := (simple_read_opt_prover s)::!opt_provers),
   " select the provers")::
    ("--data", Arg.Set opt_data,
     " for all the goals give the time taken by each provers that proved it")::
    ("--aggregate", Arg.Set opt_aggregate,
     " aggregate all the input into one file named \
       aggregate_data.* and aggregate.*")::
    ("--value-not-valid", Arg.Set_string opt_value_not_valid,
     " value used when the external proof is not valid (only for --data)")::
    ("--valid_by_time", Arg.Set opt_by_time,
     " give the evolution of the number of goal proved \
      for each provers (default)")::
    ("--gnuplot", Arg.Symbol (["pdf";"png";"svg";"qt";"gp"],select_gnuplot),
     " run gnuplot on the produced file (currently only with --valid_by_time)\
      (gp write the gnuplot script used for generating the other case)")::
    ("--gnuplot-x", Arg.Symbol (["time";"goals"],select_gnuplot_x),
     " select the data used for the x axes time or number of goal proved \
      (default time)")::
    ("--output-csv", Arg.Set opt_print_csv,
     " print the csv, set by default when --gnuplot is not set")::
    common_options

(** Normal *)

let print_cell fmt pa =
  match pa.S.proof_state with
  | S.Done {Call_provers.pr_answer = Call_provers.Valid;
                  pr_time = time} -> fprintf fmt "%f" time
  | _ -> fprintf fmt "%s" !opt_value_not_valid

let rec print_line fmt provers a =
  begin match a with
  | S.Goal a ->
    fprintf fmt "\"%s\"" a.S.goal_name.Ident.id_string;
    Whyconf.Sprover.iter (fun p ->
      try
        let pa = S.PHprover.find a.S.goal_external_proofs p in
        fprintf fmt ",%a" print_cell pa
      with Not_found ->
        fprintf fmt ",") provers;
    fprintf fmt "\n@?" (* no @\n since we use Pp.wnl *)
  | _ -> () end;
  S.iter (print_line fmt provers) a

let run_one_normal filter_provers fmt fname =
  let project_dir = S.get_project_dir fname in
  let session,_use_shapes = S.read_session project_dir in
  let provers = S.get_used_provers session in
  let provers =
    match filter_provers with
    | [] -> provers
    | _ ->
      Whyconf.Sprover.filter
        (fun p ->
          List.exists
          (fun f -> Whyconf.filter_prover f p) filter_provers) provers in
  fprintf fmt ",%a\n@?"
    (Pp.print_iter1 Whyconf.Sprover.iter Pp.comma (Pp.asd Whyconf.print_prover))
    provers;
  S.session_iter (print_line fmt provers) session


let run_normal dir filter_provers =
  if !opt_aggregate then
    let out = open_out (Filename.concat dir "aggregate_data.csv") in
    let fmt = formatter_of_out_channel out in
    Pp.wnl fmt;
    iter_files (run_one_normal filter_provers fmt);
    close_out out
  else
    iter_files (fun fname ->
      let out = open_out
        (Filename.concat dir
           ((try Filename.chop_extension fname with _ -> fname)^"_data.csv")) in
      let fmt = formatter_of_out_channel out in
      Pp.wnl fmt;
      run_one_normal filter_provers fmt fname;
      close_out out)


(** By time *)

let print_float_list =
  Pp.print_list_delim ~start:Pp.lsquare ~stop:Pp.rsquare ~sep:Pp.semi Pp.float

let grab_valid_time provers_time provers pa =
  let prover = pa.S.proof_prover in
  if Whyconf.Sprover.mem prover provers then
    match pa.S.proof_state with
    | S.Done {Call_provers.pr_answer = Call_provers.Valid;
                    pr_time = time} ->
      let l = Whyconf.Hprover.find_def provers_time [] prover in
      Whyconf.Hprover.replace provers_time prover (time::l)
  | _ -> ()

let run_one_by_time provers_time filter_provers fname =
  let project_dir = S.get_project_dir fname in
  let session,_use_shapes = S.read_session project_dir in
  let provers = S.get_used_provers session in
  let provers =
    match filter_provers with
    | [] -> provers
    | _ ->
      Whyconf.Sprover.filter
        (fun p ->
          List.exists
          (fun f -> Whyconf.filter_prover f p) filter_provers) provers in
  S.session_iter_proof_attempt
    (grab_valid_time provers_time provers) session


let print_provers_time (provers_time : float list Whyconf.Hprover.t) fmt =
  let provers_time =
    Whyconf.Hprover.fold (fun p e acc -> Whyconf.Mprover.add p e acc)
      provers_time Whyconf.Mprover.empty in
  fprintf fmt ",%a\n@?"
    (Pp.print_iter2 Whyconf.Mprover.iter Pp.comma Pp.nothing
       (Pp.asd Whyconf.print_prover) Pp.nothing)
    provers_time;
  let l = Whyconf.Mprover.values provers_time in
  let l = List.map (fun l ->
    let sorted = List.fast_sort Pervasives.compare l in
    (ref sorted,ref 0)) l in
  let rec print_line (l : (float list ref * int ref) list) =
    (* get the minimum *)
    let lmin = List.fold_left (fun acc (e,_) ->
      match !e with
      | [] -> acc
      | a::_ -> min a acc) max_float l in
    if lmin = max_float then () (* finished *)
    else begin
      (* remove the minimum and increase the number of proved *)
      let rec remove nb = function
        | [] -> []
        | a::e when a = lmin -> incr nb; remove nb e
        | e -> e in
      List.iter (fun (e,nb) -> e:=remove nb !e) l;
      (* Print the current number of proved *)
      fprintf fmt "%f,%a\n@?" lmin
        (Pp.print_list Pp.comma (fun fmt (_,nb) -> pp_print_int fmt (!nb)))
        l;
      print_line l end in
  print_line l

let create_gnuplot_by_time nb_provers fmt =
  let timeaxe, goalsaxe =
    match !opt_gnuplot_x with | Xtime -> "x","y" | Xgoals -> "y","x"
  in
  Format.pp_print_string fmt
"\
set datafile separator \",\"\n\
set key autotitle columnhead\n\
set object rectangle from screen 0,0 to screen 1,1 behind\n\
set key rmargin width -4 samplen 2\n";
  Format.fprintf fmt "set logscale %s 10\n" timeaxe;
  Format.fprintf fmt "set %slabel \"time(s)\"\n" timeaxe;
  Format.fprintf fmt "set %slabel \"number of solved goals\"\n\n" goalsaxe;
  Format.pp_print_string fmt "plot \\\n";
  for i=1 to nb_provers do
    begin match !opt_gnuplot_x with
    | Xtime ->
      Format.fprintf fmt
        "data_filename using ($1):($%i) with steps title columnhead(%i)"
        (i+1) (i+1)
    | Xgoals ->
      Format.fprintf fmt
        "data_filename using ($%i):($1) with fsteps title columnhead(%i)"
        (i+1) (i+1)
    end;
    if i <> nb_provers then Format.pp_print_string fmt ",\\\n";
  done

let print_file out f : unit =
    let fmt = formatter_of_out_channel out in
    Pp.wnl fmt;
    f fmt;
    close_out out

let print_args fmt args =
  (Pp.print_iter1 Array.iter
     (fun fmt () -> Format.pp_print_string fmt " ") (* no @\n *)
     (fun fmt -> Format.fprintf fmt "%S"))
   fmt args

let call_gnuplot arg1 arg2 csv_file gp_file =
  let args =
    [| "gnuplot"; "-e"; arg1; "-e"; arg2;
       "-e"; Printf.sprintf "data_filename = \"%s\"" (Opt.get csv_file);
       Opt.get gp_file |] in
  Debug.dprintf verbose "exec:%a@." print_args args;
  let pid = Unix.create_process "gnuplot" args
      Unix.stdin Unix.stdout Unix.stderr  in
  match Unix.waitpid [] pid with
  | _, Unix.WEXITED 0 -> ()
  | _ -> Format.eprintf "Command failed:%a@." print_args args


let run_by_time_gen dir canonical_name iter =
  let to_remove = Stack.create () in
  let canonical_name = Filename.concat dir canonical_name in
  (* compute stats *)
  let provers_time = Whyconf.Hprover.create 5 in
  iter provers_time;
  (* print .csv if necessary *)
  let csv_file =
     if !opt_gnuplot = [] || !opt_print_csv then
       let fname = canonical_name ^ ".csv" in
       print_file (open_out fname)
         (fun fmt -> print_provers_time provers_time fmt);
       Some fname
     else if !opt_gnuplot <> [] then
       let fname,ch = Filename.open_temp_file "why3session" ".csv" in
       Stack.push fname to_remove;
       print_file ch
         (fun fmt -> print_provers_time provers_time fmt);
       Some fname
     else None
  in

  (* create .gp if necessary *)
  let nb_provers = Whyconf.Hprover.length provers_time in
  let gp_file =
    if List.mem GP !opt_gnuplot
    then let fname = canonical_name ^ ".gp" in
      print_file (open_out fname)
        (fun fmt -> create_gnuplot_by_time nb_provers fmt);
      Some fname
    else if !opt_gnuplot <> [] then
      let fname,ch = Filename.open_temp_file "why3session" ".gp" in
      Stack.push fname to_remove;
      print_file ch
        (fun fmt -> create_gnuplot_by_time nb_provers fmt);
      Some fname
    else None
  in

  (* output .png, .pdf, .csv and run .qt if necessary *)
  if List.mem PNG !opt_gnuplot then
    call_gnuplot
      "set terminal pngcairo size 600, 400"
      (Printf.sprintf "set output \"%s.png\"" canonical_name)
      csv_file gp_file;
  if List.mem PDF !opt_gnuplot then
    call_gnuplot
      "set terminal pdfcairo"
      (Printf.sprintf "set output \"%s.pdf\"" canonical_name)
      csv_file gp_file;
  if List.mem SVG !opt_gnuplot then
    call_gnuplot
      "set terminal svg"
      (Printf.sprintf "set output \"%s.svg\"" canonical_name)
      csv_file gp_file;
  if List.mem QT !opt_gnuplot then
    call_gnuplot
      "set terminal qt persist"
      ""
      csv_file gp_file;
  (* Clean up temporary files *)
  Stack.iter Sys.remove to_remove


let run_by_time dir filter_provers =
  if !opt_aggregate then
    run_by_time_gen dir "aggregate.csv"
      (fun provers_time ->
         iter_files (run_one_by_time provers_time filter_provers))
  else
    iter_files (fun fname ->
        run_by_time_gen dir (try Filename.chop_extension fname with _ -> fname)
          (fun provers_time ->
             run_one_by_time provers_time filter_provers fname)
      )

(* Common *)

let run () =
  let _,whyconf,should_exit1 = read_env_spec () in
  if should_exit1 then exit 1;
  let filter_provers =
    List.map (Whyconf.filter_prover_with_shortcut whyconf) !opt_provers in
  let dir = Sysutil.absolutize_filename orig_dir (!opt_output_dir) in
  if !opt_data then run_normal dir filter_provers;
  if !opt_by_time || not (!opt_data) then run_by_time dir filter_provers

let cmd =
  { cmd_spec = spec;
    cmd_desc =
      "output session as a table or graph for simple processing or viewing";
    cmd_name = "csv";
    cmd_run  = run;
  }
