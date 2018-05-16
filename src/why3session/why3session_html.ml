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
open Why3session_lib

module Hprover = Whyconf.Hprover
module S = Session

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

open Session

type context =
    (string ->
     (formatter -> unit session -> unit) -> unit session
     -> unit, formatter, unit) format

let run_file (context : context) print_session fname =
  let project_dir = Session.get_project_dir fname in
  let session,_use_shapes = Session.read_session project_dir in
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
  then fprintf fmt context basename (print_session basename) session
  else print_session basename fmt session;
  pp_print_flush fmt ();
  if output_dir <> "-" then close_out cout


module Table =
struct


  let rec transf_depth tr =
    List.fold_left
      (fun depth g -> max depth (goal_depth g)) 0 tr.S.transf_goals
  and goal_depth g =
    S.PHstr.fold
      (fun _st tr depth -> max depth (1 + transf_depth tr))
      (S.goal_transformations g) 1

  let theory_depth t =
    List.fold_left
      (fun depth g -> max depth (goal_depth g)) 0 t.S.theory_goals

  let provers_stats provers theory =
    S.theory_iter_proof_attempt (fun a ->
      Hprover.replace provers a.S.proof_prover a.S.proof_prover) theory

  let print_prover = Whyconf.print_prover


  let color_of_status ?(dark=false) fmt b =
    fprintf fmt "%s" (if b then
        if dark then "008000" else "C0FFC0"
      else "FF0000")

let print_results fmt provers proofs =
  List.iter (fun p ->
    fprintf fmt "<td style=\"background-color:#";
    begin
      try
        let pr = S.PHprover.find proofs p in
        let s = pr.S.proof_state in
        begin
          match s with
	  | S.Done res ->
	    begin
	      match res.Call_provers.pr_answer with
		| Call_provers.Valid ->
                  fprintf fmt "C0FFC0\">%.2f" res.Call_provers.pr_time
		| Call_provers.Invalid ->
                  fprintf fmt "FF0000\">Invalid"
		| Call_provers.Timeout ->
                  fprintf fmt "FF8000\">Timeout (%ds)"
                    pr.S.proof_limit.Call_provers.limit_time
		| Call_provers.OutOfMemory ->
                  fprintf fmt "FF8000\">Out Of Memory (%dM)"
                    pr.S.proof_limit.Call_provers.limit_mem
		| Call_provers.StepLimitExceeded ->
                  fprintf fmt "FF8000\">Step limit exceeded"
		| Call_provers.Unknown _ ->
                  fprintf fmt "FF8000\">%.2f" res.Call_provers.pr_time
		| Call_provers.Failure _ ->
                  fprintf fmt "FF8000\">Failure"
		| Call_provers.HighFailure ->
                  fprintf fmt "FF8000\">High Failure"
	    end
	  | S.InternalFailure _ -> fprintf fmt "E0E0E0\">Internal Failure"
          | S.Interrupted -> fprintf fmt "E0E0E0\">Not yet run"
          | S.Unedited -> fprintf fmt "E0E0E0\">Not yet edited"
          | S.Scheduled | S.Running
          | S.JustEdited -> assert false
        end;
        if pr.S.proof_obsolete then fprintf fmt " (obsolete)"
      with Not_found -> fprintf fmt "E0E0E0\">---"
    end;
    fprintf fmt "</td>") provers

let rec num_lines acc tr =
  List.fold_left
    (fun acc g -> 1 +
      PHstr.fold (fun _ tr acc -> 1 + num_lines acc tr)
      (goal_transformations g) acc)
    acc tr.transf_goals

  let rec print_transf fmt depth max_depth provers tr =
    fprintf fmt "<tr>";
    fprintf fmt "<td style=\"background-color:#%a\" colspan=\"%d\">"
      (color_of_status ~dark:false) (Opt.inhabited tr.S.transf_verified)
      (max_depth - depth + 1);
    fprintf fmt "%s</td>" tr.transf_name ;
    for _i=1 to List.length provers do
      fprintf fmt "<td style=\"background-color:#E0E0E0\"></td>"
    done;
    fprintf fmt "</tr>@\n";
    fprintf fmt "<tr><td rowspan=\"%d\">&nbsp;&nbsp;</td>" (num_lines 0 tr);
    let (_:bool) = List.fold_left
      (fun needs_tr g ->
        print_goal fmt needs_tr (depth+1) max_depth provers g;
        true)
      false tr.transf_goals
    in ()

  and print_goal fmt needs_tr depth max_depth provers g =
    if needs_tr then fprintf fmt "<tr>";
    fprintf fmt "<td style=\"background-color:#%a\" colspan=\"%d\">"
      (color_of_status ~dark:false) (Opt.inhabited (S.goal_verified g))
      (max_depth - depth + 1);
    fprintf fmt "%s</td>" (S.goal_user_name g);
    print_results fmt provers (goal_external_proofs g);
    fprintf fmt "</tr>@\n";
    PHstr.iter
      (fun _ tr -> print_transf fmt depth max_depth provers tr)
      (goal_transformations g)

  let print_theory fn fmt th =
    let depth = theory_depth th in
    if depth > 0 then begin
    let provers = Hprover.create 9 in
    provers_stats provers th;
    let provers =
      Hprover.fold (fun _ pr acc -> pr :: acc) provers []
    in
    let provers = List.sort Whyconf.Prover.compare provers in
    let name =
      try
        let (l,t,_) = Theory.restore_path th.theory_name in
        String.concat "." ([fn]@l@[t])
      with Not_found -> fn ^ "." ^ th.theory_name.Ident.id_string
    in
    fprintf fmt "<h2><span style=\"color:#%a\">Theory \"%s\": "
      (color_of_status ~dark:true) (Opt.inhabited th.S.theory_verified)
      name;
    begin match th.S.theory_verified with
    | Some t -> fprintf fmt "fully verified in %.02f s" t
    | None -> fprintf fmt "not fully verified"
    end;
    fprintf fmt "</span></h2>@\n";

    fprintf fmt "<table border=\"1\"><tr><td colspan=\"%d\">Obligations</td>" depth;
    List.iter
      (fun pr -> fprintf fmt "<td text-rotation=\"90\">%a</td>" print_prover pr)
      provers;
    fprintf fmt "</tr>@\n";
    List.iter (print_goal fmt true 1 depth provers) th.theory_goals;
    fprintf fmt "</table>@\n"
    end

  let print_file fmt f =
    (* fprintf fmt "<h1>File %s</h1>@\n" f.file_name; *)
    let fn = Filename.basename f.file_name in
    let fn = Filename.chop_extension fn in
    fprintf fmt "%a"
      (Pp.print_list Pp.newline (print_theory fn)) f.file_theories

  let print_session name fmt s =
    fprintf fmt "<h1>Why3 Proof Results for Project \"%s\"</h1>@\n" name;
    fprintf fmt "%a"
      (Pp.print_iter2 PHstr.iter Pp.newline Pp.nothing Pp.nothing
         print_file) s.session_files


  let context : context = "<!DOCTYPE html \
PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\
\n<html xmlns=\"http://www.w3.org/1999/xhtml\">\
\n<head>\
\n  <meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\" />\
\n  <title>Why3 session of %s</title>\
\n</head>\
\n<body>\
\n%a\
\n</body>\
\n</html>\
\n"

  let run_one = run_file context print_session

end



module Simple =
struct

  let print_prover = Whyconf.print_prover

  let print_proof_status fmt = function
    | Interrupted -> fprintf fmt "Not yet run"
    | Unedited -> fprintf fmt "Not yet edited"
    | JustEdited | Scheduled | Running -> assert false
    | Done pr -> fprintf fmt "Done: %a" Call_provers.print_prover_result pr
    | InternalFailure exn ->
      fprintf fmt "Failure: %a"Exn_printer.exn_printer exn

  let print_proof_attempt fmt pa =
    fprintf fmt "<li>%a : %a</li>"
      print_prover pa.proof_prover
      print_proof_status pa.proof_state

  let rec print_transf fmt tr =
    fprintf fmt "<li>%s : <ul>%a</ul></li>"
      tr.transf_name
      (Pp.print_list Pp.newline print_goal) tr.transf_goals

  and print_goal fmt g =
    fprintf fmt "<li>%s : <ul>%a%a</ul></li>"
      (goal_name g).Ident.id_string
      (Pp.print_iter2 PHprover.iter Pp.newline Pp.nothing
         Pp.nothing print_proof_attempt)
      (goal_external_proofs g)
      (Pp.print_iter2 PHstr.iter Pp.newline Pp.nothing
         Pp.nothing print_transf)
      (goal_transformations g)

  let print_theory fmt th =
    fprintf fmt "<li>%s : <ul>%a</ul></li>"
      th.theory_name.Ident.id_string
      (Pp.print_list Pp.newline print_goal) th.theory_goals

  let print_file fmt f =
    fprintf fmt "<li>%s : <ul>%a</ul></li>"
      f.file_name
      (Pp.print_list Pp.newline print_theory) f.file_theories

  let print_session _name fmt s =
    fprintf fmt "<ul>%a</ul>"
      (Pp.print_iter2 PHstr.iter Pp.newline Pp.nothing Pp.nothing
         print_file) s.session_files


  let context : context = "<!DOCTYPE html \
PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\
\n<html xmlns=\"http://www.w3.org/1999/xhtml\">\
\n<head>\
\n  <meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\" />\
\n  <title>Why3 session of %s</title>\
\n</head>\
\n<body>\
\n%a\
\n</body>\
\n</html>\
\n"

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
