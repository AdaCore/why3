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

open Format
open Why3
open Why3session_lib

module Hprover = Whyconf.Hprover
module S = Session_itp

let output_dir = ref ""
let opt_context = ref false

type style = SimpleTree | Table

let opt_style = ref Table
let default_style = "table"

let set_opt_style = function
  | "simpletree" -> opt_style := SimpleTree
  | "table" -> opt_style := Table
  | _ ->
    eprintf "Unknown html style, ignored@."

let () = set_opt_style default_style

let opt_pp = ref []

let set_opt_pp_in,set_opt_pp_cmd,set_opt_pp_out =
  let suf = ref "" in
  let cmd = ref "" in
  (fun s -> suf := s),
  (fun s -> cmd := s),
  (fun s -> opt_pp := (!suf,(!cmd,s))::!opt_pp)

let spec =
  ("-o",
   Arg.Set_string output_dir,
   "<path> output directory ('-' for stdout)") ::
  ("--context", Arg.Set opt_context,
   " add context around the generated HTML code") ::
  ("--style", Arg.Symbol (["simpletree";"table"], set_opt_style),
   " style to use, defaults to '" ^ default_style ^ "'."
) ::
  ("--add_pp", Arg.Tuple
    [Arg.String set_opt_pp_in;
     Arg.String set_opt_pp_cmd;
     Arg.String set_opt_pp_out],
  "<suffix> <cmd> <out_suffix> declare a pretty-printer for edited proofs") ::
  ("--coqdoc",
   Arg.Unit (fun ()->
    opt_pp := (".v",("coqdoc --no-index --html -o %o %i",".html"))::!opt_pp),
  " use coqdoc to print Coq proofs") ::
  common_options

open Session_itp

type context =
    (string ->
     (formatter -> session -> unit) -> session
     -> unit, formatter, unit) format

let run_file (context : context) print_session fname =
  let ses,_ = read_session fname in
  let project_dir = get_dir ses in
  let output_dir =
    if !output_dir = "" then project_dir else !output_dir
  in
  let basename = Filename.basename project_dir in
  let cout =
    if output_dir = "-" then stdout else
      open_out (Filename.concat output_dir ("why3session.html"))
  in
  let fmt = formatter_of_out_channel cout in
  if !opt_context
  then fprintf fmt context basename (print_session basename) ses
  else print_session basename fmt ses;
  pp_print_flush fmt ();
  if output_dir <> "-" then close_out cout


module Table =
struct

  let provers_stats s provers theory =
    theory_iter_proof_attempt s (fun a ->
      Hprover.replace provers a.prover a.prover) theory

  let print_prover = Whyconf.print_prover


  let color_of_status ?(dark=false) fmt b =
    fprintf fmt "%s" (if b then
        if dark then "008000" else "C0FFC0"
      else "FF0000")

let print_results fmt s provers proofs =
  List.iter (fun p ->
    fprintf fmt "<td bgcolor=\"#";
    begin
      try
        let pr = get_proof_attempt_node s (Hprover.find proofs p) in
        let s = pr.proof_state in
        begin
          match s with
	  | Some res ->
	    begin
	      match res.Call_provers.pr_answer with
		| Call_provers.Valid ->
                  fprintf fmt "C0FFC0\">%.2f" res.Call_provers.pr_time
		| Call_provers.Invalid ->
                  fprintf fmt "FF0000\">Invalid"
		| Call_provers.Timeout ->
                  fprintf fmt "FF8000\">Timeout (%ds)"
                    pr.limit.Call_provers.limit_time
		| Call_provers.OutOfMemory ->
                  fprintf fmt "FF8000\">Out Of Memory (%dM)"
                    pr.limit.Call_provers.limit_mem
		| Call_provers.StepLimitExceeded ->
                  fprintf fmt "FF8000\">Step limit exceeded"
		| Call_provers.Unknown _ ->
                  fprintf fmt "FF8000\">%.2f" res.Call_provers.pr_time
		| Call_provers.Failure _ ->
                  fprintf fmt "FF8000\">Failure"
		| Call_provers.HighFailure ->
                  fprintf fmt "FF8000\">High Failure"
	    end
	  | None -> fprintf fmt "E0E0E0\">result missing"
        end;
        if pr.S.proof_obsolete then fprintf fmt " (obsolete)"
      with Not_found -> fprintf fmt "E0E0E0\">---"
    end;
    fprintf fmt "</td>") provers

let rec num_lines s acc tr =
  List.fold_left
    (fun acc g -> 1 +
      List.fold_left (fun acc tr -> 1 + num_lines s acc tr)
      acc (get_transformations s g))
    acc (get_sub_tasks s tr)

  let rec print_transf fmt s depth max_depth provers tr =
    fprintf fmt "<tr>";
    for _i=1 to 0 (* depth-1 *) do fprintf fmt "<td></td>" done;
    fprintf fmt "<td bgcolor=\"#%a\" colspan=\"%d\">"
      (color_of_status ~dark:false) (tn_proved s tr)
      (max_depth - depth + 1);
    (* for i=1 to depth-1 do fprintf fmt "&nbsp;&nbsp;&nbsp;&nbsp;" done; *)
    let name = (get_transf_name s tr) ^
                 (String.concat "" (get_transf_args s tr)) in
    fprintf fmt "%s</td>" name ;
    for _i=1 (* depth *) to (*max_depth - 1 + *) List.length provers do
      fprintf fmt "<td bgcolor=\"#E0E0E0\"></td>"
    done;
    fprintf fmt "</tr>@\n";
    fprintf fmt "<td rowspan=\"%d\">&nbsp;&nbsp;</td>" (num_lines s 0 tr);
    let (_:bool) = List.fold_left
      (fun is_first g ->
        print_goal fmt s is_first (depth+1) max_depth provers g;
        false)
      true (get_sub_tasks s tr)
    in ()

  and print_goal fmt s is_first depth max_depth provers g =
    if not is_first then fprintf fmt "<tr>";
    (* for i=1 to 0 (\* depth-1 *\) do fprintf fmt "<td></td>" done; *)
    fprintf fmt "<td bgcolor=\"#%a\" colspan=\"%d\">"
      (color_of_status ~dark:false) (pn_proved s g)
      (max_depth - depth + 1);
    (* for i=1 to depth-1 do fprintf fmt "&nbsp;&nbsp;&nbsp;&nbsp;" done; *)
    fprintf fmt "%s</td>" (get_proof_name s g).Ident.id_string;
(*    for i=depth to max_depth-1 do fprintf fmt "<td></td>" done; *)
    print_results fmt s provers (get_proof_attempt_ids s g);
    fprintf fmt "</tr>@\n";
    List.iter
      (print_transf fmt s depth max_depth provers)
      (get_transformations s g)

  let print_theory s fn fmt th =
    let depth = theory_depth s th in
    if depth > 0 then
    let provers = get_used_provers_theory s th in
    let provers =
      Whyconf.Sprover.fold (fun pr acc -> pr :: acc) provers []
    in
    let provers = List.sort Whyconf.Prover.compare provers in
    let name =
      try
        let (l,t,_) = Theory.restore_path (theory_name th) in
        String.concat "." ([fn]@l@[t])
      with Not_found -> fn ^ "." ^ (theory_name th).Ident.id_string
    in
    fprintf fmt "<h2><font color=\"#%a\">Theory \"%s\": "
      (color_of_status ~dark:true) (th_proved s th)
      name;
    if th_proved s th then
      fprintf fmt "fully verified in %%.02f s"
    else fprintf fmt "not fully verified";
    fprintf fmt "</font></h2>@\n";

    fprintf fmt "<table border=\"1\"><tr><td colspan=\"%d\">Obligations</td>" depth;
    (* fprintf fmt "<table border=\"1\"><tr><td>Obligations</td>"; *)
    List.iter
      (fun pr -> fprintf fmt "<td text-rotation=\"90\">%a</td>" print_prover pr)
      provers;
    fprintf fmt "</td></tr>@\n";
    List.iter (print_goal fmt s true 1 depth provers) (theory_goals th);
    fprintf fmt "</table>@\n"

  let print_file s fmt f =
    (* fprintf fmt "<h1>File %s</h1>@\n" f.file_name; *)
    let fn = Filename.basename (file_name f) in
    let fn = Filename.chop_extension fn in
    fprintf fmt "%a"
      (Pp.print_list Pp.newline (print_theory s fn)) (file_theories f)

  let print_session name fmt s =
    fprintf fmt "<h1>Why3 Proof Results for Project \"%s\"</h1>@\n" name;
    fprintf fmt "%a"
      (Pp.print_iter2 Stdlib.Hstr.iter Pp.newline Pp.nothing Pp.nothing
         (print_file s)) (get_files s)


  let context : context = "<!DOCTYPE html\
PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\
<html xmlns=\"http://www.w3.org/1999/xhtml\">\
<head>\
<title>Why3 session of %s</title>\
</head>\
<body>\
%a\
</body>\
</html>\
"

  let run_one = run_file context print_session

end



module Simple =
struct

  let print_prover = Whyconf.print_prover

  let print_proof_status fmt = function
    | None -> fprintf fmt "No result"
    | Some res -> fprintf fmt "Done: %a" Call_provers.print_prover_result res

  let print_proof_attempt s fmt pa =
    let pa = get_proof_attempt_node s pa in
    fprintf fmt "<li>%a : %a</li>"
      print_prover pa.prover
      print_proof_status pa.proof_state

  let rec print_transf s fmt tr =
    let name = (get_transf_name s tr) ^
                 (String.concat "" (get_transf_args s tr)) in
    fprintf fmt "<li>%s : <ul>%a</ul></li>"
      name
      (Pp.print_list Pp.newline (print_goal s)) (get_sub_tasks s tr)

  and print_goal s fmt g =
    fprintf fmt "<li>%s : <ul>%a%a</ul></li>"
      (get_proof_name s g).Ident.id_string
      (Pp.print_iter2 Hprover.iter Pp.newline Pp.nothing
         Pp.nothing (print_proof_attempt s))
      (get_proof_attempt_ids s g)
      (Pp.print_iter1 List.iter Pp.newline (print_transf s))
      (get_transformations s g)

  let print_theory s fmt th =
    fprintf fmt "<li>%s : <ul>%a</ul></li>"
      (theory_name th).Ident.id_string
      (Pp.print_list Pp.newline (print_goal s)) (theory_goals th)

  let print_file s fmt f =
    fprintf fmt "<li>%s : <ul>%a</ul></li>"
      (file_name f)
      (Pp.print_list Pp.newline (print_theory s)) (file_theories f)

  let print_session _name fmt s =
    fprintf fmt "<ul>%a</ul>"
      (Pp.print_iter2 Stdlib.Hstr.iter Pp.newline Pp.nothing Pp.nothing
         (print_file s)) (get_files s)


  let context : context = "<!DOCTYPE html\
PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\
<html xmlns=\"http://www.w3.org/1999/xhtml\">\
<head>\
<title>Why3 session of %s</title>\
</head>\
<body>\
%a\
</body>\
</html>\
"

  let run_one = run_file context print_session

end


let run () =
  let _,_,should_exit1 = read_env_spec () in
  if should_exit1 then exit 1;
  match !opt_style with
    | Table -> iter_files Table.run_one
    | SimpleTree -> iter_files Simple.run_one

let cmd =
  { cmd_spec = spec;
    cmd_desc = "output session in HTML format";
    cmd_name = "html";
    cmd_run  = run;
  }


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3session.byte"
End:
*)
