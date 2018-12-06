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
open Session_itp
open Why3session_lib

module Hprover = Whyconf.Hprover

let opt_style = ref 1
let opt_output_dir = ref ""
let opt_longtable = ref false
let opt_elements = ref None

let add_element s =
  let l = match !opt_elements with
    | None -> [s]
    | Some r -> s :: r
  in
  opt_elements := Some l

let spec =
  ("-style",
   Arg.Set_int opt_style,
   "<n> set output style (1 or 2, default 1)") ::
  ("-o",
   Arg.Set_string opt_output_dir,
   "<dir> where to produce LaTeX files (default: session dir)") ::
  ("-e",
   Arg.String add_element,
   "<path> produce a table for the element denoted by <path>") ::
  ("-longtable",
   Arg.Set opt_longtable,
   " use 'longtable' environment instead of 'tabular'") ::
  common_options


(* Statistics in LaTeX*)

(*
let provers_latex_stats_goal provers goal =
  goal_iter_proof_attempt (fun a ->
    Hprover.replace provers a.S.proof_prover a.S.proof_prover) goal

let provers_latex_stats provers theory =
  S.theory_iter_proof_attempt (fun a ->
    Hprover.replace provers a.S.proof_prover a.S.proof_prover) theory

let provers_latex_stats_file provers file =
  S.file_iter_proof_attempt (fun a ->
    Hprover.replace provers a.S.proof_prover a.S.proof_prover) file
 *)

let protect s =
  let b = Buffer.create 7 in
  for i = 0 to String.length s - 1 do
    match s.[i] with
	'_' -> Buffer.add_string b "\\_"
      | c -> Buffer.add_char b c
  done;
  Buffer.contents b


let column n depth provers =
  if n == 1 then
    if depth > 1 then
      (List.length provers) + depth
    else
      (List.length provers) + depth + 1
  else
    (List.length provers) +  1

let print_head n depth provers fmt =
  if n == 1 then
    if (depth > 1) then
      fprintf fmt "\\hline \\multicolumn{%d}{|c|}{Proof obligations } "
        depth
    else
      fprintf fmt "\\hline \\multicolumn{%d}{|c|}{Proof obligations } "
        (depth + 1)
  else
    fprintf fmt "\\hline Proof obligations ";
  List.iter (fun a -> fprintf fmt "& \\provername{%a} " Whyconf.print_prover a)
    provers;
  fprintf fmt "\\\\ @."

let print_tabular_head n depth provers fmt =
  fprintf fmt "\\begin{tabular}";
  fprintf fmt "{|l|";
  for _i = 0 to depth do fprintf fmt "l|" done;
  for _i = 1 to (List.length provers) do fprintf fmt "c|" done;
  fprintf fmt "}@.";
  print_head n depth provers fmt

let print_tabular_foot fmt =
  fprintf fmt "\\hline \\end{tabular}@."


let print_result_prov s proofs prov fmt=
  List.iter (fun p ->
  try
    let pr = get_proof_attempt_node s (Hprover.find proofs p) in
    let s = pr.proof_state in
      match s with
	| Some res ->
	    begin
	      match res.Call_provers.pr_answer with
		| Call_provers.Valid ->
                  fprintf fmt "& \\valid{%.2f} " res.Call_provers.pr_time
		| Call_provers.Invalid ->
                  fprintf fmt "& \\invalid{%.2f} " res.Call_provers.pr_time
		| Call_provers.Timeout ->
                  fprintf fmt "& \\timeout{%ds} "
                    pr.limit.Call_provers.limit_time
		| Call_provers.OutOfMemory ->
                  fprintf fmt "& \\outofmemory{%dM} "
                    pr.limit.Call_provers.limit_mem
		| Call_provers.StepLimitExceeded ->
                  fprintf fmt "& \\steplimitexceeded "
		| Call_provers.Unknown _ ->
                  fprintf fmt "& \\unknown{%.2f} " res.Call_provers.pr_time
		| Call_provers.Failure _ ->
                  fprintf fmt "& \\failure "
		| Call_provers.HighFailure ->
                  fprintf fmt "& \\highfailure "

	    end
	| None -> fprintf fmt "(no result)"
  with Not_found -> fprintf fmt "& \\noresult") prov;
  fprintf fmt "\\\\ @."


let rec goal_latex_stat s fmt prov depth depth_max subgoal g =
  let column = column 1 depth prov
  in
    if depth > 0 then
      if subgoal > 0 then
	fprintf fmt "\\cline{%d-%d}@." (depth + 1) column
      else ()
    else
      fprintf fmt "\\hline@.";
    if depth_max > 1 then
      begin
	if subgoal > 0 then
	  begin
	    if(depth < depth_max)  then
	      for _i = 1 to depth do
                fprintf fmt " & "
              done
	    else
	      for _i = 1 to depth - 1 do
                fprintf fmt " & "
              done
	  end
	else
	  if(depth < depth_max) then
	    if depth > 0 then
              fprintf fmt " & "
      end
    else
      begin
	if subgoal > 0  then
	  for _i = 1 to depth do fprintf fmt " & " done
	else
	  if depth > 0 then fprintf fmt " & "
      end;
    if (depth <= 1) then
      fprintf fmt "\\explanation{%s} "
              (protect (goal_full_name s g))
    else
      fprintf fmt " " ;
    let proofs = get_proof_attempt_ids s g in
      if (Hprover.length proofs) > 0 then
	begin
	  if depth_max <= 1 then
	    begin
	      if depth > 0 then
		for _i = depth to (depth_max - depth) do
                  fprintf fmt "& " done
	      else
		for _i = depth to (depth_max - depth - 1) do
                  fprintf fmt "& " done
	    end
	  else
	    if depth > 0 then
	      for _i = depth to (depth_max - depth - 1) do
		fprintf fmt "& " done
	    else
	      for _i = depth to (depth_max - depth - 2) do
		fprintf fmt "& " done;
	  print_result_prov s proofs prov fmt;
	end;
      let tr = get_transformations s g in
	if List.length tr > 0 then
	  if Hprover.length proofs > 0 then
	    fprintf fmt "\\cline{%d-%d}@." (depth + 2) column;
	List.iter (fun tr ->
          let goals = get_sub_tasks s tr in
	  let _ = List.fold_left (fun subgoal g ->
              goal_latex_stat s fmt prov (depth + 1) depth_max (subgoal) g;
               subgoal + 1) 0 goals in
	    () ) tr


let style_2_row fmt ?(transf=false) depth prov subgoal expl=
  let column = column 2 depth prov in
  if depth > 0 || transf then
    fprintf fmt "\\cline{%d-%d}@." 2 column
  else
    fprintf fmt "\\hline@.";
  for _i = 1 to depth do fprintf fmt "\\quad" done;
  let macro = if transf then "transformation" else "explanation" in
  if depth = 0 || transf then
    fprintf fmt "\\%s{%s} " macro expl
  else
    fprintf fmt "\\subgoal{%s}{%d} " expl (subgoal + 1)

let rec goal_latex2_stat s fmt prov depth depth_max subgoal g =
  let proofs = get_proof_attempt_ids s g in
  if Hprover.length proofs > 0 then
    begin
      style_2_row fmt depth prov subgoal
                  (protect (goal_full_name s g));
      print_result_prov s proofs prov fmt
    end
 else
    if (*depth = 0*) true then
      begin
        style_2_row fmt depth prov subgoal
                    (protect (goal_full_name s g));
	fprintf fmt "& \\multicolumn{%d}{|c|}{}\\\\ @."
          (List.length prov)
      end;
  let tr = get_transformations s g in
  if List.length tr > 0 then
    begin
      List.iter
        (fun tr ->
         let name = get_transf_string s tr in
         style_2_row fmt ~transf:true (depth+1) prov subgoal
                     (protect name);
	 fprintf fmt "& \\multicolumn{%d}{|c|}{}\\\\@."
                 (List.length prov);
	 let goals = get_sub_tasks s tr in
	 let _ = List.fold_left
                   (fun subgoal g ->
	            goal_latex2_stat s fmt prov (depth + 1) depth_max (subgoal) g;
	            subgoal + 1) 0 goals in
	 () ) tr
    end
 else
   if (Hprover.length proofs) == 0 && depth <> 0 then
     fprintf fmt "\\\\@."

let latex_tabular_goal n s fmt depth provers g =
  print_tabular_head n depth provers fmt;
  if n == 1 then
    goal_latex_stat s fmt provers 0 depth 0 g
  else
    goal_latex2_stat s fmt provers 0 depth  0 g;
  print_tabular_foot fmt

let latex_tabular_aux n s fmt depth provers t =
  if n == 1 then
    List.iter (goal_latex_stat s fmt provers 0 depth 0) (theory_goals t)
  else
    List.iter (goal_latex2_stat s fmt provers 0 depth  0) (theory_goals t)

let latex_tabular n s fmt depth provers t =
  print_tabular_head n depth provers fmt;
  latex_tabular_aux n s fmt depth provers t;
  print_tabular_foot fmt


let latex_tabular_file n s fmt depth provers f =
  print_tabular_head n depth provers fmt;
  List.iter (latex_tabular_aux n s fmt depth provers) (file_theories f);
  print_tabular_foot fmt


let latex_longtable n s fmt depth name provers t=
  fprintf fmt "\\begin{longtable}";
  fprintf fmt "{| l |";
  for _i = 0 to (List.length provers) + depth do fprintf fmt "c |" done;
  fprintf fmt "}@.";
  (* First head *)
  print_head n depth provers fmt;
  fprintf fmt "\\hline \\endfirsthead @.";
  (* Other heads : "Continued... " added *)
  fprintf fmt "\\multicolumn{%d}{r}{\\textit{Continued from previous page}} \
\\\\ @." (List.length provers + 1) ;
  fprintf fmt "\\hline @.";
  print_head n depth provers fmt;
  fprintf fmt "\\hline \\endhead @.";
  (* Other foots : "Continued..." added *)
  fprintf fmt "\\hline \\multicolumn{%d}{r}{\\textit{Continued on next page}} \
\\\\ @." (List.length provers);
  (* Last foot : nothing *)
  fprintf fmt "\\endfoot \\endlastfoot @.";
  if n == 1 then
    List.iter (goal_latex_stat s fmt provers 0 depth 0) (theory_goals t)
  else
    List.iter (goal_latex2_stat s fmt provers 0 depth  0) (theory_goals t);
  fprintf fmt "\\hline \\caption{%s statistics} @." (protect name);
  fprintf fmt "\\label{%s} \\end{longtable}@." (protect name)


let theory_latex_stat n s table dir t =
  let provers = get_used_provers_theory s t in
  let provers = Whyconf.Sprover.fold (fun pr acc -> pr :: acc)
    provers [] in
  let provers = List.sort Whyconf.Prover.compare provers in
  let depth = theory_depth s t in
  let name = (theory_name t).Ident.id_string in
  let ch = open_out (Filename.concat dir(name^".tex")) in
  let fmt = formatter_of_out_channel ch in
    if table = "tabular" then
      begin
      latex_tabular n s fmt depth provers t
      end
    else
      latex_longtable n s fmt depth name provers t;
    close_out ch

let file_latex_stat n s table  dir f =
   List.iter (theory_latex_stat n s table dir) (file_theories f)

let standalone_goal_latex_stat n s _table dir g =
  let provers = get_used_provers_goal s g in
  let provers = Whyconf.Sprover.fold (fun pr acc -> pr :: acc)
    provers [] in
  let provers = List.sort Whyconf.Prover.compare provers in
  let depth = goal_depth s g in
  let name = (get_proof_name s g).Ident.id_string in
  let ch = open_out (Filename.concat dir (name^".tex")) in
  let fmt = formatter_of_out_channel ch in
  latex_tabular_goal n s fmt depth provers g;
(*
  if table = "tabular" then
  begin
  latex_tabular_goal n fmt depth provers g
  end
  else
  latex_longtable_goal n fmt depth name provers g;
*)
  close_out ch

let file_latex_stat_all n s _table dir f =
  let provers = get_used_provers_file s f in
  let provers = Whyconf.Sprover.fold (fun pr acc -> pr :: acc)
    provers [] in
  let provers = List.sort Whyconf.Prover.compare provers in
  let depth = file_depth s f in
  let name = basename (file_path f) in
  let ch = open_out (Filename.concat dir(name^".tex")) in
  let fmt = formatter_of_out_channel ch in
  latex_tabular_file n s fmt depth provers f;
(*
    if table = "tabular" then
      begin
      latex_tabular n fmt depth provers t
      end
    else
      latex_longtable n fmt depth name provers t;

*)
    close_out ch



let element_latex_stat_goal g n s table dir r =
  begin
    match r with
      | [] -> ()
      | _ ->
        eprintf "Warning: only main goals are supported@.:"
  end;
  standalone_goal_latex_stat n s table dir g

let element_latex_stat_theory s th n table dir e =
  match e with
    | [] -> theory_latex_stat n s table dir th
    | g :: r ->
      try
        let goals =
          List.map (fun g ->
                    (get_proof_name s g).Ident.id_string,g)
            (theory_goals th)
        in
        let g = List.assoc g goals in
        element_latex_stat_goal g n s table dir r
      with Not_found ->
        eprintf "Warning: goal not found in path: %s@." g

let element_latex_stat_file f n s table dir e =
  match e with
    | [] -> file_latex_stat_all n s table dir f
    | th :: r ->
      try
        let ths =
          List.map (fun th -> (theory_name th).Ident.id_string,th)
            (file_theories f)
        in
        let th = List.assoc th ths in
        element_latex_stat_theory s th n table dir r
      with Not_found ->
        eprintf "Warning: theory not found in path: %s@." th


let element_latex_stat files n s table dir e =
  eprintf "Element %s@." e;
  match Strings.split '.' e with
    | [] -> ()
    | f :: r ->
      let found = ref false in
      Hfile.iter
        (fun _ file ->
          let fname = basename (file_path file) in
          let fname = List.hd (Strings.split '.' fname) in
          if fname = f then
            begin
              found := true;
              element_latex_stat_file file n s table dir r
            end)
        files;
      if not !found then
        eprintf "Warning: file not found for element %s@." e

let print_latex_statistics n table dir session =
  let files = get_files session in
  match !opt_elements with
    | None ->
      Hfile.iter (fun _ f -> file_latex_stat n session table dir f) files
    | Some l ->
      List.iter (element_latex_stat files n session table dir) l



let table () = if !opt_longtable then "longtable" else "tabular"

let run_one fname =
  let ses,_ = read_session fname in
  let project_dir = get_dir ses in
  let dir = if !opt_output_dir = "" then project_dir else
      !opt_output_dir
  in
  print_latex_statistics !opt_style (table ()) dir ses

let run () =
  let _,_,should_exit1 = read_env_spec () in
  if should_exit1 then exit 1;
  iter_files run_one


let cmd =
  { cmd_spec = spec;
    cmd_desc = "output session in LaTeX format";
    cmd_name = "latex";
    cmd_run  = run;
  }
