(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
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
module S = Session

let opt_output_dir = ref ""

let opt_provers = ref []
let opt_aggregate = ref false

let simple_read_opt_prover s =
  try
    Whyconf.parse_filter_prover s
  with Whyconf.ParseFilterProver _ ->
    raise (Arg.Bad
             "--filter-prover name[,version[,alternative]|,,alternative] \
                regexp must start with ^")


let opt_value_not_valid = ref "-1."
let opt_gnuplot = false

type style =
| Normal
| By_Time

let opt_style = ref Normal

let set_style s =
  match s with
  | "normal" -> opt_style := Normal
  | "by_time" -> opt_style := By_Time
  | _  -> assert false

(* TODO *)
let print_gnuplot =
"set datafile separator \",\"
set key autotitle columnhead

set term png
set logscale xy 10
set object rectangle from screen 0,0 to screen 1,1 behind

set output \"%s\"
set xlabel \"%a\"
max(x,y) = x > y ? x : y
plot     \"aggregate.csv\" using (max($4,0.001)):(max($3,0.001))
"

let spec =
  ("-o",
   Arg.Set_string opt_output_dir,
   "<dir> where to produce LaTeX files (default: session dir)") ::
  ("--filter-prover",
   Arg.String (fun s ->
     opt_provers := (simple_read_opt_prover s)::!opt_provers),
   " select the provers")::
    ("--aggregate", Arg.Set opt_aggregate,
     " aggregate all the input into one")::
    ("--value-not-valid", Arg.Set_string opt_value_not_valid,
     " value used when the external proof is not valid")::
    ("--style", Arg.Symbol (["normal";"by_time"],set_style)," set the style")
      :: (common_options)

(** Normal *)

let print_cell fmt pa =
  match pa.Session.proof_state with
  | Session.Done {Call_provers.pr_answer = Call_provers.Valid;
                  pr_time = time} -> fprintf fmt "%f" time
  | _ -> fprintf fmt "%s" !opt_value_not_valid

let rec print_line fmt provers a =
  begin match a with
  | Session.Goal a ->
    fprintf fmt "\"%s\"" a.Session.goal_name.Ident.id_string;
    Whyconf.Sprover.iter (fun p ->
      try
        let pa = Session.PHprover.find a.Session.goal_external_proofs p in
        fprintf fmt ",%a" print_cell pa
      with Not_found ->
        fprintf fmt ",") provers;
    fprintf fmt "\n@?" (** no @\n since we use Pp.wnl *)
  | _ -> () end;
  Session.iter (print_line fmt provers) a

let run_one_normal filter_provers fmt fname =
  let project_dir = Session.get_project_dir fname in
  let session = Session.read_session project_dir in
  let provers = Session.get_used_provers session in
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
  Session.session_iter (print_line fmt provers) session


let run_normal dir filter_provers =
  if !opt_aggregate then
    let out = open_out (Filename.concat dir "aggregate.csv") in
    let fmt = formatter_of_out_channel out in
    Pp.wnl fmt;
    iter_files (run_one_normal filter_provers fmt);
    close_out out
  else
    iter_files (fun fname ->
      let out = open_out
        (Filename.concat dir
           ((try Filename.chop_extension fname with _ -> fname)^".csv")) in
      let fmt = formatter_of_out_channel out in
      Pp.wnl fmt;
      run_one_normal filter_provers fmt fname;
      close_out out)


(** By time *)

let print_float_list =
  Pp.print_list_delim ~start:Pp.lsquare ~stop:Pp.rsquare ~sep:Pp.semi Pp.float

let rec grab_valid_time provers_time provers pa =
  let prover = pa.Session.proof_prover in
  if Whyconf.Sprover.mem prover provers then
    match pa.Session.proof_state with
    | Session.Done {Call_provers.pr_answer = Call_provers.Valid;
                    pr_time = time} ->
      let l = Whyconf.Hprover.find_def provers_time [] prover in
      Whyconf.Hprover.replace provers_time prover (time::l)
  | _ -> ()

let run_one_by_time provers_time filter_provers fname =
  let project_dir = Session.get_project_dir fname in
  let session = Session.read_session project_dir in
  let provers = Session.get_used_provers session in
  let provers =
    match filter_provers with
    | [] -> provers
    | _ ->
      Whyconf.Sprover.filter
        (fun p ->
          List.exists
          (fun f -> Whyconf.filter_prover f p) filter_provers) provers in
  Session.session_iter_proof_attempt
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
    (** get the minimum *)
    let lmin = List.fold_left (fun acc (e,_) ->
      match !e with
      | [] -> acc
      | a::_ -> min a acc) max_float l in
    if lmin = max_float then () (** finished *)
    else begin
      (** remove the minimum and increase the number of proved *)
      let rec remove nb = function
        | [] -> []
        | a::e when a = lmin -> incr nb; remove nb e
        | e -> e in
      List.iter (fun (e,nb) -> e:=remove nb !e) l;
      (** Print the current number of proved *)
      fprintf fmt "%f,%a\n@?" lmin
        (Pp.print_list Pp.comma (fun fmt (_,nb) -> pp_print_int fmt (!nb)))
        l;
      print_line l end in
  print_line l


let run_by_time dir filter_provers =
  if !opt_aggregate then
    let out = open_out (Filename.concat dir "aggregate.csv") in
    let fmt = formatter_of_out_channel out in
    Pp.wnl fmt;
    let provers_time = Whyconf.Hprover.create 5 in
    iter_files (run_one_by_time provers_time filter_provers);
    print_provers_time provers_time fmt;
    close_out out
  else
    iter_files (fun fname ->
      let out = open_out
        (Filename.concat dir
           ((try Filename.chop_extension fname with _ -> fname)^".csv")) in
      let fmt = formatter_of_out_channel out in
      Pp.wnl fmt;
      let provers_time = Whyconf.Hprover.create 5 in
      run_one_by_time provers_time filter_provers fname;
      print_provers_time provers_time fmt;
      close_out out)

(* Common *)

let run () =
  let _,whyconf,should_exit1 = read_env_spec () in
  if should_exit1 then exit 1;
  let filter_provers =
    List.map (Whyconf.filter_prover_with_shortcut whyconf) !opt_provers in
  let dir = !opt_output_dir in
  match !opt_style with
  | Normal -> run_normal dir filter_provers
  | By_Time -> run_by_time dir filter_provers

let cmd =
  { cmd_spec = spec;
    cmd_desc = "output session as a table for simple processing.";
    cmd_name = "csv";
    cmd_run  = run;
  }
