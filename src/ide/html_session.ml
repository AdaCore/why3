(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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

let includes = ref []
let files = Queue.create ()
let opt_version = ref false
let output_dir = ref ""
let allow_obsolete = ref true
let opt_config = ref None
let opt_context = ref false

type style =
  | Simple
  | Jstree

let opt_style = ref Jstree

let set_opt_style = function
  | "simple" -> opt_style := Simple
  | "jstree" -> opt_style := Jstree
  | _ -> assert false

let opt_pp = ref []

let set_opt_pp_in,set_opt_pp_cmd,set_opt_pp_out =
  let suf = ref "" in
  let cmd = ref "" in
  (fun s -> suf := s),
  (fun s -> cmd := s),
  (fun s -> opt_pp := (!suf,(!cmd,s))::!opt_pp)

let spec = Arg.align [
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> Add s to loadpath") ;
  ("-v",
   Arg.Set opt_version,
   " Print version information") ;
  ("-o",
   Arg.Set_string output_dir,
   " The directory to output the files ('-' for stdout)");
  ("--strict",
   Arg.Clear allow_obsolete,
   " Forbid obsolete session");
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " Same as -C";
  "--context", Arg.Set opt_context,
  " Add context around the generated code in order to allow direct \
    visualisation (header, css, ...). It also add in the directory \
    all the needed external file. It can't be set with stdout output";
  "--style", Arg.Symbol (["simple";"jstree"], set_opt_style),
  " Set the style to use. 'simple' use only 'ul' and 'il' tag. 'jstree' use \
    the 'jstree' plugin of the javascript library 'jquery'.";
  "--add_pp", Arg.Tuple
    [Arg.String set_opt_pp_in;
     Arg.String set_opt_pp_cmd;
     Arg.String set_opt_pp_out],
  "<suffix> <cmd> <out_suffix> \
Add for the given prefix the given pretty-printer, \
the new file as the given out_suffix. cmd must contain '%i' which will be \
replace by the input file and '%o' which will be replaced by the output file.";
    "--coqdoc",
  Arg.Unit (fun ()->
    opt_pp := (".v",("coqdoc --no-index --html -o %o %i",".html"))::!opt_pp),
  " same as '--add_pp .v \"coqdoc --no-index --html -o %o %i\" .html'";
    Debug.Opt.desc_debug_list;
    Debug.Opt.desc_debug_all;
    Debug.Opt.desc_debug;
]


let version_msg = sprintf
  "Why3 html session output, version %s (build date: %s)"
  Config.version Config.builddate

let usage_str = sprintf
  "Usage: %s [options] [<file.why>|<project directory>] ... "
  (Filename.basename Sys.argv.(0))

let set_file f = Queue.push f files

let () = Arg.parse spec set_file usage_str

let () =
  if !opt_version then begin
    printf "%s@." version_msg;
    exit 0
  end

(* let () = *)
(*   List.iter (fun (in_,(cmd,out)) -> *)
(*     printf "in : %s, cmd : %s, out : %s@." in_ cmd out) !opt_pp *)

let allow_obsolete = !allow_obsolete
let includes = List.rev !includes

open Session_ro

let env = read_config ~includes !opt_config

let () =
  Debug.Opt.set_flags_selected ();
  if  Debug.Opt.option_list () then exit 0

let output_dir =
  match !output_dir with
    | "" -> printf
      "Error: output_dir must be set@.";
      exit 1
    | "-" when !opt_context ->
      printf
        "Error: context and stdout output can't be set at the same time@.";
      exit 1
    | _ -> !output_dir

let edited_dst = Filename.concat output_dir "edited"

open Util

type context =
    (string ->
     (formatter -> Session_ro.session -> unit) -> Session_ro.session
     -> unit, formatter, unit) format

let run_file (context : context) print_session f =
  let session_path = get_project_dir f in
  let basename = Filename.basename session_path in
  let session = read_project_dir ~allow_obsolete ~env session_path in
  let cout = if output_dir = "-" then stdout else
      open_out (Filename.concat output_dir (basename^".html")) in
  let fmt = formatter_of_out_channel cout in
  if !opt_context
  then fprintf fmt context basename (print_session basename) session
  else print_session basename fmt session;
  pp_print_flush fmt ();
  if output_dir <> "-" then close_out cout


module Simple =
struct

  let print_prover fmt pd = fprintf fmt "%s" pd.prover_name

  let print_proof_status fmt = function
    | Undone -> fprintf fmt "Undone"
    | Done pr -> fprintf fmt "Done : %a" Call_provers.print_prover_result pr
    | InternalFailure exn ->
      fprintf fmt "Failure : %a"Exn_printer.exn_printer exn

  let print_proof_attempt fmt pa =
    fprintf fmt "<li>%a : %a</li>"
      print_prover pa.prover
      print_proof_status pa.proof_state

  let rec print_transf fmt tr =
    fprintf fmt "<li>%s : <ul>%a</ul></li>"
      tr.transf_name
      (Pp.print_list Pp.newline print_goal) tr.subgoals

  and print_goal fmt g =
    fprintf fmt "<li>%s : <ul>%a%a</ul></li>"
      g.goal_name
      (Pp.print_iter2 Mstr.iter Pp.newline Pp.nothing
         Pp.nothing print_proof_attempt)
      g.external_proofs
      (Pp.print_iter2 Mstr.iter Pp.newline Pp.nothing
         Pp.nothing print_transf)
      g.transformations

  let print_theory fmt th =
    fprintf fmt "<li>%s : <ul>%a</ul></li>"
      th.theory_name
      (Pp.print_list Pp.newline print_goal) th.goals

  let print_file fmt f =
    fprintf fmt "<li>%s : <ul>%a</ul></li>"
      f.file_name
      (Pp.print_list Pp.newline print_theory) f.theories

  let print_session _name fmt s =
    fprintf fmt "<ul>%a</ul>"
      (Pp.print_list Pp.newline print_file) s.files


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

  let run_files () =
  Queue.iter (run_file context print_session) files

end

module Jstree =
struct

  let print_verified fmt b =
    if b
    then fprintf fmt "class='verified'"
    else fprintf fmt "class='notverified'"

  let print_prover fmt pd = fprintf fmt "%s" pd.prover_name

  let print_proof_status fmt = function
    | Undone -> fprintf fmt "<span class='notverified'>Undone</span>"
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
    match pa.edited_as with
      | None ->
        fprintf fmt "@[<hov><li rel='prover' ><a href='#'>%a : %a</a></li>@]"
          print_prover pa.prover
          print_proof_status pa.proof_state
      | Some f ->
        let output = find_pp f in
        fprintf fmt "@[<hov><li rel='prover' ><a href='#' \
onclick=\"showedited('%s'); return false;\">%a : %a</a></li>@]"
          output
          print_prover pa.prover
          print_proof_status pa.proof_state

  let rec print_transf fmt tr =
    fprintf fmt
      "@[<hov><li rel='transf'><a href='#'>\
<span %a>%s</span></a>@,<ul>%a</ul></li>@]"
      print_verified tr.transf_verified
      tr.transf_name
      (Pp.print_list Pp.newline print_goal) tr.subgoals

  and print_goal fmt g =
    fprintf fmt
      "@[<hov><li rel='goal'><a href='#'>\
<span %a>%s</a></a>@,<ul>%a%a</ul></li>@]"
      print_verified g.goal_verified
      g.goal_name
      (Pp.print_iter2 Mstr.iter Pp.newline Pp.nothing
         Pp.nothing print_proof_attempt)
      g.external_proofs
      (Pp.print_iter2 Mstr.iter Pp.newline Pp.nothing
         Pp.nothing print_transf)
      g.transformations

  let print_theory fmt th =
    fprintf fmt
      "@[<hov><li rel='theory'><a href='#'>\
<span %a>%s</span></a>@,<ul>%a</ul></li>@]"
      print_verified th.theory_verified
      th.theory_name
      (Pp.print_list Pp.newline print_goal) th.goals

  let print_file fmt f =
    fprintf fmt
      "@[<hov><li rel='file'><a href='#'>\
<span %a>%s</span></a>@,<ul>%a</ul></li>@]"
      print_verified f.file_verified
      f.file_name
      (Pp.print_list Pp.newline print_theory) f.theories

  let print_session_aux name fmt s =
    fprintf fmt "@[<hov><ul><a href='#'>%s</a>@,%a</ul>@]"
      name
      (Pp.print_list Pp.newline print_file) s.files


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

  let run_files () =
    if !opt_context then
      if not (Sys.file_exists edited_dst) then Unix.mkdir edited_dst 0o755;
    Queue.iter (run_file context print_session) files;
    if !opt_context then
      let data_dir = Whyconf.datadir (Whyconf.get_main env.config) in
      (** copy images *)
      let img_dir_src = Filename.concat data_dir "images" in
      let img_dir_dst = Filename.concat output_dir "images" in
      if not (Sys.file_exists img_dir_dst) then Unix.mkdir img_dir_dst 0o755;
      List.iter (fun img_name ->
        let from = Filename.concat img_dir_src img_name in
        let to_  = Filename.concat img_dir_dst img_name in
        Sysutil.copy_file from to_)
        ["folder16.png";"file16.png";"wizard16.png";"configure16.png"];
      (** copy javascript *)
      let js_dir_src = Filename.concat data_dir "javascript" in
      let js_dir_dst = Filename.concat output_dir "javascript" in
      Sysutil.copy_dir js_dir_src js_dir_dst

end


let () =
  match !opt_style with
    | Simple -> Simple.run_files ()
    | Jstree -> Jstree.run_files ()
