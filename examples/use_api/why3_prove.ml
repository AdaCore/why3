(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*******************

This file builds some MLW modules, using parse trees instead of direct
API calls

******************)

(* BEGIN{buildenv} *)
open Why3
let config : Whyconf.config = Whyconf.read_config None
let main : Whyconf.main = Whyconf.get_main config
let env : Env.env = Env.create_env (Whyconf.loadpath main)
open Ptree
(* END{buildenv} *)

(* printing *)

let get_and_print_mods () =
  let fname = Sys.argv.(1) in
  let path = [] in
  let lb = Lexing.from_channel (open_in fname) in
  Loc.set_file fname lb;
  let mlw_file = Lexer.parse_mlw_file lb in
  let mods =
    try
      Typing.type_mlw_file env path fname mlw_file
    with
      e -> ignore (Typing.discard_file ()); raise e
  in
  if path = [] then begin
    let print_m _ m = Format.eprintf "%a@\n@." Pmodule.print_module m in
    let add_m _ m mods = Ident.Mid.add m.Pmodule.mod_theory.Theory.th_name m mods in
    Ident.Mid.iter print_m (Wstdlib.Mstr.fold add_m mods Ident.Mid.empty)
  end;
  mods

let mods =
  if Array.length Sys.argv >= 3 then
    (
      match Sys.argv.(2) with
      | "--type-only" -> Debug.set_flag Typing.debug_parse_only ; Printf.printf "TYPE ONLY !\n"
      | "--parse-only" -> Debug.set_flag Typing.debug_type_only ; Printf.printf "PARSE ONLY !\n"
      | "--type-parse-only" ->  Debug.set_flag Typing.debug_type_only ; Debug.set_flag Typing.debug_parse_only ; Printf.printf "TYPE AND PARSE ONLY !\n"
      | _ -> Printf.eprintf "error flag" ; exit 2
    );
  get_and_print_mods ()

(* BEGIN{checkingvcs} *)
let my_tasks : Task.task list =
  let mods =
    Wstdlib.Mstr.fold
      (fun _ m acc ->
       List.rev_append
         (Task.split_theory m.Pmodule.mod_theory None None) acc)
      mods []
  in List.rev mods

(*
open Format

let () =
  printf "Tasks are:@.";
  let _ =
    List.fold_left
      (fun i t -> printf "Task %d: %a@." i Pretty.print_task t; i+1)
      1 my_tasks
  in ()

let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

let alt_ergo : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
  (** all provers that have the name "Alt-Ergo" *)
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else
    snd (Whyconf.Mprover.max_binding provers)

let alt_ergo_driver : Driver.driver =
  try
    Whyconf.load_driver main env alt_ergo.Whyconf.driver []
  with e ->
    eprintf "Failed to load driver for alt-ergo: %a@."
      Exn_printer.exn_printer e;
    exit 1

let () =
  let _ =
    List.fold_left
      (fun i t ->
       let r =
         Call_provers.wait_on_call
           (Driver.prove_task ~limit:Call_provers.empty_limit
                              ~command:alt_ergo.Whyconf.command
                              alt_ergo_driver t)
       in
       printf "@[On task %d, alt-ergo answers %a@."
              i (Call_provers.print_prover_result ~json_model:false) r;
       i+1
      )
      1 my_tasks
  in ()
(* END{checkingvcs} *)
*)
