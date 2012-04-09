(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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
open Why3session_lib
open Whyconf
open Format


module S = Session

let opt_style = ref 1
let opt_output_dir = ref ""
let opt_longtable = ref false

let spec =
  ("-style",
   Arg.Set_int opt_style,
   "<n> sets output style (1 or 2, default 1)") ::
  ("-o",
   Arg.Set_string opt_output_dir,
   "<path> where to produce LaTeX files (default: session dir)") ::
  ("-longtable",
   Arg.Set opt_longtable,
   " use 'longtable' environment instead of 'tabular'") ::
  common_options


(* Statistics in LaTeX*)

let rec transf_depth tr =
  List.fold_left (fun depth g -> max depth (goal_depth g)) 0 tr.S.transf_goals
and goal_depth g =
  S.PHstr.fold
    (fun _st tr depth -> max depth (1 + transf_depth tr))
    g.S.goal_transformations 0

let theory_depth t =
  List.fold_left (fun depth g -> max depth (goal_depth g)) 0 t.S.theory_goals

let rec provers_latex_stats provers theory =
  S.theory_iter_proof_attempt (fun a ->
    Hashtbl.replace provers a.S.proof_prover a.S.proof_prover) theory

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


let print_result_prov proofs prov fmt=
  List.iter (fun p ->
  try
    let pr = S.PHprover.find proofs p in
    let s = pr.S.proof_state in
      match s with
	  Session.Done res ->
	    begin
	      match res.Call_provers.pr_answer with
		  Call_provers.Valid ->
                    fprintf fmt "& \\valid{%.2f} " res.Call_provers.pr_time
		| Call_provers.Invalid -> fprintf fmt "& \\invalid "
		| Call_provers.Timeout -> fprintf fmt "& \\timeout "
		| Call_provers.Unknown _s -> fprintf fmt "& \\unknown "
		| _ -> fprintf fmt "& \\failure "
	    end
	| _ -> fprintf fmt "& Undone"
  with Not_found -> fprintf fmt "& \\noresult") prov;
  fprintf fmt "\\\\ @."


let rec goal_latex_stat fmt prov depth depth_max subgoal g =
  let column = column 1 depth prov
  in
    if depth > 0 then
      if subgoal > 0 then
	fprintf fmt "\\cline{%d-%d} @." (depth + 1) column
      else ()
    else
      fprintf fmt "\\hline @.";
    if depth_max > 1 then
      begin
	if subgoal > 0 then
	  begin
	    if(depth < depth_max)  then
	      for i = 1 to depth do
                fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " "
              done
	    else
	      for i = 1 to depth - 1 do
                fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " "
              done
	  end
	else
	  if(depth < depth_max) then
	    if depth > 0 then
              fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " "
      end
    else
      begin
	if subgoal > 0  then
	  for i = 1 to depth  do
	    fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " " done
	else
	  if depth > 0 then
	    fprintf fmt "\\explanation{%s}& \\explanation{%s}" " " " "
      end;
    if (depth <= 1) then
      fprintf fmt "\\explanation{%s} " (protect (S.goal_expl g))
    else
      fprintf fmt "\\explanation{%s}"  " ";
    let proofs = g.S.goal_external_proofs in
      if (S.PHprover.length proofs) > 0 then
	begin
	  if depth_max <= 1 then
	    begin
	      if depth > 0 then
		for i = depth to (depth_max - depth) do
                  fprintf fmt "& \\explanation{%s}" " " done
	      else
		for i = depth to (depth_max - depth - 1) do
                  fprintf fmt "& \\explanation{%s}" " " done
	    end
	  else
	    if depth > 0 then
	      for i = depth to (depth_max - depth - 1) do
		fprintf fmt "& \\explanation{%s}" " " done
	    else
	      for i = depth to (depth_max - depth - 2) do
		fprintf fmt "& \\explanation{%s}" " " done;
	  print_result_prov proofs prov fmt;
	end;
      let tr = g.S.goal_transformations in
	if S.PHstr.length tr > 0 then
	  if S.PHprover.length proofs > 0 then
	    fprintf fmt "\\cline{%d-%d} @." (depth + 2) column;
	S.PHstr.iter (fun _st tr ->
          let goals = tr.S.transf_goals in
	  let _ = List.fold_left (fun subgoal g ->
              goal_latex_stat fmt prov (depth + 1) depth_max (subgoal) g;
               subgoal + 1) 0 goals in
	    () ) tr


let rec goal_latex2_stat fmt prov depth depth_max subgoal g =
  let column = column 2 depth prov
  in
    if depth > 0 then
      fprintf fmt "\\cline{%d-%d} @." 2 column
    else
      fprintf fmt "\\hline @.";
    for i = 1 to depth do fprintf fmt "\\quad" done;
    if (depth <= 1) then
      fprintf fmt "\\explanation{%s} " (protect (S.goal_expl g))
    else
      fprintf fmt "\\explanation{%d} " (subgoal + 1);
    let proofs = g.S.goal_external_proofs in
      if (S.PHprover.length proofs) > 0 then
	print_result_prov proofs prov fmt;
      let tr = g.S.goal_transformations in
	if S.PHstr.length tr > 0 then
	  begin
	    if (S.PHprover.length proofs == 0) then
	      fprintf fmt "& \\multicolumn{%d}{|c|}{}\\\\ @."
                (List.length prov);
	    S.PHstr.iter (fun _st tr ->
		let goals = tr.S.transf_goals in
		let _ = List.fold_left (fun subgoal g ->
		  goal_latex2_stat fmt prov (depth + 1) depth_max (subgoal) g;
				subgoal + 1) 0 goals in
		  () ) tr
	  end
	else
	  if (S.PHprover.length proofs) == 0 then
	    fprintf fmt "\\\\ @."


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


let latex_tabular n fmt depth provers t =
fprintf fmt "\\begin{tabular}";
fprintf fmt "{| l |";
  for i = 0 to (List.length provers) + depth do fprintf fmt "c |" done;
  fprintf fmt "}@.";
  print_head n depth provers fmt;
  if n == 1 then
    List.iter (goal_latex_stat fmt provers 0 depth 0) t.S.theory_goals
  else
    List.iter (goal_latex2_stat fmt provers 0 depth  0) t.S.theory_goals;
  fprintf fmt "\\hline \\end{tabular}@."


let latex_longtable n fmt depth name provers t=
  fprintf fmt "\\begin{longtable}";
  fprintf fmt "{| l |";
  for i = 0 to (List.length provers) + depth do fprintf fmt "c |" done;
  fprintf fmt "}@.";
  (** First head *)
  print_head n depth provers fmt;
  fprintf fmt "\\hline \\endfirsthead @.";
  (** Other heads : "Continued... " added *)
  fprintf fmt "\\multicolumn{%d}{r}{\\textit{Continued from previous page}} \
\\\\ @." (List.length provers + 1) ;
  fprintf fmt "\\hline @.";
  print_head n depth provers fmt;
  fprintf fmt "\\hline \\endhead @.";
  (** Other foots : "Continued..." added *)
  fprintf fmt "\\hline \\multicolumn{%d}{r}{\\textit{Continued on next page}} \
\\\\ @." (List.length provers);
  (** Last foot : nothing *)
  fprintf fmt "\\endfoot \\endlastfoot @.";
  if n == 1 then
    List.iter (goal_latex_stat fmt provers 0 depth 0) t.S.theory_goals
  else
    List.iter (goal_latex2_stat fmt provers 0 depth  0) t.S.theory_goals;
  fprintf fmt "\\hline \\caption{%s statistics} @." (protect name);
  fprintf fmt "\\label{%s} \\end{longtable}@." (protect name)


let theory_latex_stat n table dir t =
  let provers = Hashtbl.create 9 in
  provers_latex_stats provers t;
  let provers = Hashtbl.fold (fun _ pr acc -> pr :: acc)
    provers [] in
  let provers = List.sort Whyconf.Prover.compare provers in
  let depth = theory_depth  t in
  let name = t.S.theory_name.Ident.id_string in
  let ch = open_out (Filename.concat dir(name^".tex")) in
  let fmt = formatter_of_out_channel ch in
    if table = "tabular" then
      begin
      latex_tabular n fmt depth provers t
      end
    else
      latex_longtable n fmt depth name provers t;
    close_out ch

let file_latex_stat n table  dir f =
   List.iter (theory_latex_stat n table dir) f.S.file_theories

let print_latex_statistics n table dir session =
  let files = session.S.session_files in
  S.PHstr.iter (fun _ f -> file_latex_stat n table dir f) files



let table () = if !opt_longtable then "longtable" else "tabular"

let run_one fname =
  let project_dir = Session.get_project_dir fname in
  let session = Session.read_session project_dir in
  let dir = if !opt_output_dir = "" then project_dir else
      !opt_output_dir
  in
  print_latex_statistics !opt_style (table ()) dir session

let run () =
  let _,_,should_exit1 = read_env_spec () in
  if should_exit1 then exit 1;
  iter_files run_one


let cmd =
  { cmd_spec = spec;
    cmd_desc = "output session in LaTeX format.";
    cmd_name = "latex";
    cmd_run  = run;
  }
