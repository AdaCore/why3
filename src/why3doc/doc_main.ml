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

open Format
open Why3
open Stdlib
open Theory

let () = Debug.set_flag Glob.flag

(* command line parsing *)

let usage_msg = sprintf
  "Usage: %s [options...] [files...]"
  (Filename.basename Sys.argv.(0))

let opt_loadpath = ref []
let opt_output = ref None
let opt_index = ref None (* default behavior *)
let opt_title = ref None
let opt_body = ref false
let opt_queue = Queue.create ()

let option_list = Arg.align [
  "-L", Arg.String (fun s -> opt_loadpath := s :: !opt_loadpath),
      "<dir> Add <dir> to the library search path";
  "-o", Arg.String (fun s -> opt_output := Some s),
      "<dir> Print files in <dir>";
  "--output", Arg.String (fun s -> opt_output := Some s),
      " same as -o";
  "--stdlib-url", Arg.String Doc_def.set_stdlib_url,
      "<url> Add links to <url> for files found on loadpath";
  "--index", Arg.Unit (fun () -> opt_index := Some true),
    " generates an index file index.html";
  "--no-index", Arg.Unit (fun () -> opt_index := Some false),
    " do not generate an index file index.html";
  "--title", Arg.String (fun s -> opt_title := Some s),
    " <title> Set a title for the index page";
  "--body-only", Arg.Set opt_body,
    " Only produce the body of the HTML document";
]

let add_opt_file x = Queue.add x opt_queue

let () =
  Arg.parse option_list add_opt_file usage_msg;
  let config = Whyconf.read_config None in
  let main = Whyconf.get_main config in
  opt_loadpath := List.rev_append !opt_loadpath (Whyconf.loadpath main);
  Doc_def.set_loadpath !opt_loadpath;
  Doc_def.set_output_dir !opt_output

let index = match !opt_index with
  | Some b -> b
  | None -> Queue.length opt_queue > 1

let title = match !opt_title with
  | None -> "why3doc index"
  | Some s -> s

let css =
  let css_fname = "style.css" in
  let css_full_fname = match !opt_output with
    | None -> css_fname
    | Some dir -> Filename.concat dir css_fname
  in
  if not (Sys.file_exists css_full_fname)
  then Doc_html.style_css css_full_fname;
  css_fname

let do_file env fname =
  try
    let m = Env.read_file env fname in
    let add _s th =
      Doc_def.add_ident th.th_name;
      Ident.Sid.iter Doc_def.add_ident th.th_local in
    Mstr.iter add m
  with e ->
    eprintf "warning: could not read file '%s'@." fname;
    eprintf "(%a)@." Exn_printer.exn_printer e

let print_file fname =
  let fhtml = Doc_def.output_file fname in
  let c = open_out fhtml in
  let fmt = formatter_of_out_channel c in
  let f = Filename.basename fname in
  if not !opt_body then Doc_html.print_header fmt ~title:f ~css ();
  if index then
    fprintf fmt "<p>%s <a href=\"index.html\">index</a></p>@\n<hr>@\n" title;
  Doc_lexer.do_file fmt fname;
  if not !opt_body then Doc_html.print_footer fmt ();
  close_out c

let () =
  Queue.iter Doc_def.add_file opt_queue;
  try
    let env = Env.create_env !opt_loadpath in
    (* process files *)
    Queue.iter (do_file env) opt_queue;
    Queue.iter print_file opt_queue;
    (* then generate the index *)
    if index then begin
      let fhtml = Doc_def.output_file "index" in
      let c = open_out fhtml in
      let fmt = formatter_of_out_channel c in
      if not !opt_body then Doc_html.print_header fmt ~title ~css ();
      fprintf fmt "<h1>%s</h1>@\n" title;
      fprintf fmt "<ul>@\n";
      let add fn =
        let header = Doc_lexer.extract_header fn in
        let header = if header = "" then "" else ": " ^ header in
        let basename = Filename.basename fn in
        fprintf fmt "<li> <a href=\"%s.html\">%s</a> %s </li>@\n"
          basename basename header
      in
      Queue.iter add opt_queue;
      fprintf fmt "</ul>@\n";
      if not !opt_body then Doc_html.print_footer fmt ();
      close_out c
    end
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3doc.opt"
End:
*)

