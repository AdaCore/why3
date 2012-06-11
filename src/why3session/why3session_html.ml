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

open Format
open Why3
open Why3session_lib

module S = Session

let output_dir = ref ""
let opt_context = ref false

type style = SimpleTree | Jstree | Table

let opt_style = ref Table
let default_style = "table"

let set_opt_style = function
  | "simple" -> opt_style := SimpleTree
  | "jstree" -> opt_style := Jstree
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
   " adds context around the generated HTML code") ::
  ("--style", Arg.Symbol (["simpletree";"jstree";"table"], set_opt_style),
   " style to use, defaults to '" ^ default_style ^ "'."
) ::
  ("--add_pp", Arg.Tuple
    [Arg.String set_opt_pp_in;
     Arg.String set_opt_pp_cmd;
     Arg.String set_opt_pp_out],
  "<suffix> <cmd> <out_suffix> declares a pretty-printer for edited proofs") ::
  ("--coqdoc",
   Arg.Unit (fun ()->
    opt_pp := (".v",("coqdoc --no-index --html -o %o %i",".html"))::!opt_pp),
  " use coqdoc to print Coq proofs") ::
  common_options

open Session
open Util

type context =
    (string ->
     (formatter -> notask session -> unit) -> notask session
     -> unit, formatter, unit) format

let run_file (context : context) print_session fname =
  let project_dir = Session.get_project_dir fname in
  let session = Session.read_session project_dir in
  let output_dir =
    if !output_dir = "" then project_dir else !output_dir
  in
  let basename = Filename.basename project_dir in
  let cout =
    if output_dir = "-" then stdout else
      open_out (Filename.concat output_dir (basename^".html"))
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
      g.S.goal_transformations 1

  let theory_depth t =
    List.fold_left
      (fun depth g -> max depth (goal_depth g)) 0 t.S.theory_goals

  let rec provers_stats provers theory =
    S.theory_iter_proof_attempt (fun a ->
      Hashtbl.replace provers a.S.proof_prover a.S.proof_prover) theory

  let print_prover = Whyconf.print_prover


  let color_of_status ?(dark=false) fmt b =
    fprintf fmt "%s" (if b then
        if dark then "008000" else "C0FFC0"
      else "FF0000")

let print_results fmt provers proofs =
  List.iter (fun p ->
    fprintf fmt "<td bgcolor=\"#";
    begin
      try
        let pr = S.PHprover.find proofs p in
        let s = pr.S.proof_state in
        match s with
	  | S.Done res ->
	    begin
	      match res.Call_provers.pr_answer with
		| Call_provers.Valid ->
                  fprintf fmt "C0FFC0\">%.2f" res.Call_provers.pr_time
		| Call_provers.Invalid ->
                  fprintf fmt "FF0000\">Invalid"
		| Call_provers.Timeout ->
                  fprintf fmt "FF8000\">Timeout"
		| Call_provers.OutOfMemory ->
                  fprintf fmt "FF8000\">Out Of Memory"
		| Call_provers.Unknown _ ->
                  fprintf fmt "FF8000\">%.2f" res.Call_provers.pr_time
		| Call_provers.Failure _ ->
                  fprintf fmt "FF8000\">Failure"
		| Call_provers.HighFailure ->
                  fprintf fmt "FF8000\">High Failure"
	    end
	  | S.Undone _ -> fprintf fmt "E0E0E0\">Undone"
	  | S.InternalFailure _ -> fprintf fmt "E0E0E0\">Internal Failure"
      with Not_found -> fprintf fmt "E0E0E0\">---"
    end;
    fprintf fmt "</td>") provers

let rec num_lines acc tr =
  List.fold_left
    (fun acc g -> 1 +
      PHstr.fold (fun _ tr acc -> 1 + num_lines acc tr)
      g.goal_transformations acc)
    acc tr.transf_goals

  let rec print_transf fmt depth max_depth provers tr =
    fprintf fmt "<tr>";
    for i=1 to 0 (* depth-1 *) do fprintf fmt "<td></td>" done;
    fprintf fmt "<td bgcolor=\"#%a\" colspan=\"%d\">"
      (color_of_status ~dark:false) tr.S.transf_verified
      (max_depth - depth + 1);
    (* for i=1 to depth-1 do fprintf fmt "&nbsp;&nbsp;&nbsp;&nbsp;" done; *)
    fprintf fmt "%s</td>" tr.transf_name ;
    for i=1 (* depth *) to (*max_depth - 1 + *) List.length provers do
      fprintf fmt "<td bgcolor=\"#E0E0E0\"></td>"
    done;
    fprintf fmt "</tr>@\n";
    fprintf fmt "<td rowspan=\"%d\">&nbsp;&nbsp;</td>" (num_lines 0 tr);
    let (_:bool) = List.fold_left
      (fun is_first g ->
        print_goal fmt is_first (depth+1) max_depth provers g;
        false)
      true tr.transf_goals
    in ()

  and print_goal fmt is_first depth max_depth provers g =
    if not is_first then fprintf fmt "<tr>";
    (* for i=1 to 0 (\* depth-1 *\) do fprintf fmt "<td></td>" done; *)
    fprintf fmt "<td bgcolor=\"#%a\" colspan=\"%d\">"
      (color_of_status ~dark:false) g.S.goal_verified (max_depth - depth + 1);
    (* for i=1 to depth-1 do fprintf fmt "&nbsp;&nbsp;&nbsp;&nbsp;" done; *)
    fprintf fmt "%s</td>" (S.goal_expl g);
(*    for i=depth to max_depth-1 do fprintf fmt "<td></td>" done; *)
    print_results fmt provers g.goal_external_proofs;
    fprintf fmt "</tr>@\n";
    PHstr.iter
      (fun _ tr -> print_transf fmt depth max_depth provers tr)
      g.goal_transformations

  let print_theory fmt th =
    let depth = theory_depth th in
    if depth > 0 then
    let provers = Hashtbl.create 9 in
    provers_stats provers th;
    let provers =
      Hashtbl.fold (fun _ pr acc -> pr :: acc) provers []
    in
    let provers = List.sort Whyconf.Prover.compare provers in
    let name = th.S.theory_name.Ident.id_string in
    fprintf fmt "<h2><font color=\"#%a\">Theory \"%s\": %s</font></h2>@\n"
      (color_of_status ~dark:true) th.S.theory_verified
      name (if th.S.theory_verified then "fully verified" else "not fully verified")
    ;

    fprintf fmt "<table border=\"1\"><tr><td colspan=\"%d\">Obligations</td>" depth;
    (* fprintf fmt "<table border=\"1\"><tr><td>Obligations</td>"; *)
    List.iter
      (fun pr -> fprintf fmt "<td text-rotation=\"90\">%a</td>" print_prover pr)
      provers;
    fprintf fmt "</td></tr>@\n";
    List.iter (print_goal fmt true 1 depth provers) th.theory_goals;
    fprintf fmt "</table>@\n"

  let print_file fmt f =
    (* fprintf fmt "<h1>File %s</h1>@\n" f.file_name; *)
    fprintf fmt "%a"
      (Pp.print_list Pp.newline print_theory) f.file_theories

  let print_session name fmt s =
    fprintf fmt "<h1>Why3 Proof Results for Project \"%s\"</h1>@\n" name;
    fprintf fmt "%a"
      (Pp.print_iter2 PHstr.iter Pp.newline Pp.nothing Pp.nothing
         print_file) s.session_files


  let context : context = "<!DOCTYPE html
PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">
<head>
<title>Why3 session of %s</title>
</head>
<body>
%a
</body>
</html>
"

  let run_one = run_file context print_session

end



module Simple =
struct

  let print_prover = Whyconf.print_prover

  let print_proof_status fmt = function
    | Undone _ -> fprintf fmt "Undone"
    | Done pr -> fprintf fmt "Done : %a" Call_provers.print_prover_result pr
    | InternalFailure exn ->
      fprintf fmt "Failure : %a"Exn_printer.exn_printer exn

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
      g.goal_name.Ident.id_string
      (Pp.print_iter2 PHprover.iter Pp.newline Pp.nothing
         Pp.nothing print_proof_attempt)
      g.goal_external_proofs
      (Pp.print_iter2 PHstr.iter Pp.newline Pp.nothing
         Pp.nothing print_transf)
      g.goal_transformations

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


  let context : context = "<!DOCTYPE html
PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">
<head>
<title>Why3 session of %s</title>
</head>
<body>
%a
</body>
</html>
"

  let run_one = run_file context print_session

end


module Jstree =
struct

  let print_verified fmt b =
    if b
    then fprintf fmt "class='verified'"
    else fprintf fmt "class='notverified'"

  let print_prover = Whyconf.print_prover

  let print_proof_status fmt = function
    | Undone _ -> fprintf fmt "<span class='notverified'>Undone</span>"
    | Done pr -> fprintf fmt "<span class='verified'>Done : %a</span>"
      Call_provers.print_prover_result pr
    | InternalFailure exn ->
      fprintf fmt "<span class='notverified'>Failure : %a</span>"
        Exn_printer.exn_printer exn

  let cmd_regexp = Str.regexp "%\\(.\\)"

  let pp_run input cmd output =
    let replace s = match Str.matched_group 1 s with
      | "%" -> "%"
      | "i" -> input
      | "o" -> output
      | _ -> failwith "unknown format specifier, use %%i, %%o"
    in
    let cmd = Str.global_substitute cmd_regexp replace cmd in
    let c = Sys.command cmd in
    if c <> 0 then
      eprintf "[Error] '%s' stopped abnormaly : code %i" cmd c

 let edited_dst = Filename.concat !output_dir "edited"

  let find_pp edited =
    let basename = Filename.basename edited in
    try
      let suff,(cmd,suff_out) =
        List.find (fun (s,_) -> ends_with basename s) !opt_pp in
      let base =
        String.sub basename 0 (String.length basename - String.length suff) in
      let base_dst = (base^suff_out) in
      if !opt_context then
        pp_run edited cmd (Filename.concat edited_dst base_dst);
      base_dst
    with Not_found ->
      eprintf "Default %s@." basename;
      (** default printer *)
      let base = try Filename.chop_extension basename with _ -> basename in
      let base_dst = base^".txt" in
      if !opt_context then
        Sysutil.copy_file edited (Filename.concat edited_dst base_dst);
      base_dst

  let print_proof_attempt fmt pa =
    match pa.proof_edited_as with
      | None ->
        fprintf fmt "@[<hov><li rel='prover' ><a href='#'>%a : %a</a></li>@]"
          print_prover pa.proof_prover
          print_proof_status pa.proof_state
      | Some f ->
        let output = find_pp f in
        fprintf fmt "@[<hov><li rel='prover' ><a href='#' \
onclick=\"showedited('%s'); return false;\">%a : %a</a></li>@]"
          output
          print_prover pa.proof_prover
          print_proof_status pa.proof_state

  let rec print_transf fmt tr =
    fprintf fmt
      "@[<hov><li rel='transf'><a href='#'>\
<span %a>%s</span></a>@,<ul>%a</ul></li>@]"
      print_verified tr.transf_verified
      tr.transf_name
      (Pp.print_list Pp.newline print_goal) tr.transf_goals

  and print_goal fmt g =
    fprintf fmt
      "@[<hov><li rel='goal'><a href='#'>\
<span %a>%s</a></a>@,<ul>%a%a</ul></li>@]"
      print_verified g.goal_verified
      g.goal_name.Ident.id_string
      (Pp.print_iter2 PHprover.iter Pp.newline Pp.nothing
         Pp.nothing print_proof_attempt)
      g.goal_external_proofs
      (Pp.print_iter2 PHstr.iter Pp.newline Pp.nothing
         Pp.nothing print_transf)
      g.goal_transformations

  let print_theory fmt th =
    fprintf fmt
      "@[<hov><li rel='theory'><a href='#'>\
<span %a>%s</span></a>@,<ul>%a</ul></li>@]"
      print_verified th.theory_verified
      th.theory_name.Ident.id_string
      (Pp.print_list Pp.newline print_goal) th.theory_goals

  let print_file fmt f =
    fprintf fmt
      "@[<hov><li rel='file'><a href='#'>\
<span %a>%s</span></a>@,<ul>%a</ul></li>@]"
      print_verified f.file_verified
      f.file_name
      (Pp.print_list Pp.newline print_theory) f.file_theories

  let print_session_aux name fmt s =
    fprintf fmt "@[<hov><ul><a href='#'>%s</a>@,%a</ul>@]"
      name
      (Pp.print_iter2 PHstr.iter Pp.newline Pp.nothing Pp.nothing print_file)
      s.session_files


  let print_session name fmt s =
    fprintf fmt
      "<a href='#' onclick=\"$('#%s_session').jstree('open_all');\">
expand all
</a> <a href='#' onclick=\"$('#%s_session').jstree('close_all');\">
close all
</a>
<div id=\"%s_session\" class=\"session\">
%a
</div>
<script type=\"text/javascript\" class=\"source\">
$(function () {
  $(\"#%s_session\").jstree({
      \"types\" : {
	   \"types\" : {
	   \"file\" : {
		\"icon\" : { \"image\" : \"images/folder16.png\"},
		      },
	   \"theory\" : {
		\"icon\" : { \"image\" : \"images/folder16.png\"},
		      },
	   \"goal\" : {
		\"icon\" : { \"image\" : \"images/file16.png\"},
		      },
	   \"prover\" : {
		\"icon\" : { \"image\" : \"images/wizard16.png\"},
		      },
	   \"transf\" : {
		\"icon\" : { \"image\" : \"images/configure16.png\"},
		      },
                        }
                },
      \"plugins\" : [\"themes\",\"html_data\",\"types\"]
        });
});
</script>
"
  name name name (print_session_aux name) s name


  let context : context = "<!DOCTYPE html
PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"
\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">
<head>
    <meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\" />
    <title>Why3 session of %s</title>
    <link rel=\"stylesheet\" type=\"text/css\"
     href=\"javascript/session.css\" />
    <script type=\"text/javascript\" src=\"javascript/jquery.js\"></script>
    <script type=\"text/javascript\" src=\"javascript/jquery.jstree.js\">\
</script>
    <script type=\"text/javascript\" src=\"javascript/session.js\">\
</script>
</head>
<body>
%a
<iframe src=\"\"  id='edited'>
<p>Your browser does not support iframes.</p>
</iframe>
<script type=\"text/javascript\" class=\"source\">
$(function () {
  $('#edited').hide()
})
</script>
</body>
</html>
"

  let run_files config =
    if !opt_context then
      if not (Sys.file_exists edited_dst) then Unix.mkdir edited_dst 0o755;
    iter_files (run_file context print_session);
    if !opt_context then
      let data_dir = Whyconf.datadir (Whyconf.get_main config) in
      (** copy images *)
      let img_dir_src = Filename.concat data_dir "images" in
      let img_dir_dst = Filename.concat !output_dir "images" in
      if not (Sys.file_exists img_dir_dst) then Unix.mkdir img_dir_dst 0o755;
      List.iter (fun img_name ->
        let from = Filename.concat img_dir_src img_name in
        let to_  = Filename.concat img_dir_dst img_name in
        Sysutil.copy_file from to_)
        ["folder16.png";"file16.png";"wizard16.png";"configure16.png"];
      (** copy javascript *)
      let js_dir_src = Filename.concat data_dir "javascript" in
      let js_dir_dst = Filename.concat !output_dir "javascript" in
      Sysutil.copy_dir js_dir_src js_dir_dst

end



let run () =
  let _,config,should_exit1 = read_env_spec () in
  if should_exit1 then exit 1;
  match !opt_style with
    | Table -> iter_files Table.run_one
    | SimpleTree -> iter_files Simple.run_one
    | Jstree -> Jstree.run_files config


let cmd =
  { cmd_spec = spec;
    cmd_desc = "output session in HTML format.";
    cmd_name = "html";
    cmd_run  = run;
  }


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3session.byte"
End:
*)
