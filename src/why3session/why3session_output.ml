(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2026 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(********************************************************************)

open Why3
open Why3session_lib
open Session_itp

let output_dir = ref ("." : string)

let spec =
  let open Getopt in
  [
    ( KLong "output-dir",
      Hnd1
        ( AString,
          fun dir -> output_dir := dir ),
      "<dir> output directory" );
  ]
  @ Why3session_lib.filter_spec

let filename_sanitizer =
  let no_slash_quote = function
    | '/' | '\\' |'"' | '\''-> "__"
    | c -> String.make 1 c
  in
  let ident_printer = Ident.create_ident_printer ~sanitizer:(Ident.sanitizer no_slash_quote no_slash_quote)
  [] in
  fun file->
    let file_ext = Filename.extension file in
    let file_no_ext = Filename.remove_extension file in
    let file = (Ident.string_unique ident_printer file_no_ext) ^ file_ext in
    file



let run () =
  let config, env = Whyconf.Args.complete_initialization () in
  iter_session_files (fun fname ->
    let controller,_,_ =
    Why3session_lib.read_update_session ~allow_obsolete:true env config fname in
    let session = controller.Controller_itp.controller_session in

  let f, e = Why3session_lib.read_filter_spec config in
  if e then exit 1;
  Why3session_lib.session_iter_proof_attempt_by_filter session f
   (fun _ pa_node ->
        match Session_itp.get_task session pa_node.parent,
        Whyconf.Hprover.find controller.Controller_itp.controller_provers pa_node.prover with
        | exception Not_found -> ()
        | (task,(_,driver)) ->
        let th = get_encapsulating_theory session (APn pa_node.parent) in
        let th_name = (Session_itp.theory_name th).Ident.id_string in
        let f = get_encapsulating_file session (ATh th) in
        let fn = Filename.chop_extension (Sysutil.basename (file_path f)) in
        let node_name = (Session_itp.get_proof_name session pa_node.parent).Ident.id_string in
        let file = Driver.get_filename driver ~input_file:fn ~theory_name:th_name ~goal_name:node_name
          ~sanitize:(fun x -> x) in
        let file = Sysutil.concat !output_dir (filename_sanitizer file) in
        Sysutil.write_file_fmt file (fun fmt -> Driver.print_task driver fmt task)
      )
)

let cmd =
  {
    cmd_spec = spec;
    cmd_desc = "output prover input file from the command line";
    cmd_usage = "<session>\nOutput prover input file from the command line.";
    cmd_name = "output";
    cmd_run = run;
  }
