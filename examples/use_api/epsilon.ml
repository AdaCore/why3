(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*******************

This file is for testing the creation of epsilon-terms using the Ptree
   API and the S-expression parsing and printing

******************)

open Why3
let config : Whyconf.config = Whyconf.init_config None
let main : Whyconf.main = Whyconf.get_main config
let env : Env.env = Env.create_env (Whyconf.loadpath main)
open Ptree
open Ptree_helpers

(* declaration of
module M
  use int.Int
  goal g : (epsilon x. 0 <= x) + 1 > 0
end
 *)

let mlw_source_file = "../epsilon.mlw"
let sexp_file = "examples/use_api/epsilon.sexp"

let loc = Loc.user_position mlw_source_file 1 0 1 1

let mod_M =
  (* use int.Int *)
  let use_int_Int = use ~loc ~import:false (["int";"Int"]) in
  (* goal g  *)
  let g =
    let zero = tconst ~loc 0 in
    let le_int = qualid ["Int";Ident.op_infix "<="] in
    let id_x = ident ~loc "x" in
    let ty_int = PTtyapp(qualid ["int"],[]) in
    let zero_le_x = tapp ~loc le_int [zero;tvar ~loc (Qident id_x)] in
    let eps = term ~loc (Teps(id_x,ty_int,zero_le_x)) in
    let gt_int = qualid ["Int";Ident.op_infix ">"] in
    let one = tconst ~loc 1 in
    let add_int = qualid ["Int";Ident.op_infix "+"] in
    let goal_term = tapp ~loc gt_int  [tapp add_int [eps;one]; zero] in
    Dprop(Decl.Pgoal, ident ~loc "g", goal_term)
  in
  (ident ~loc "M",[use_int_Int ; g])


let mlw_file = Modules [mod_M]

open Format

(* Printing back the mlw file, in S-expression format *)

let sexp = Ptree.sexp_of_mlw_file mlw_file

let () = printf "@[%a@]@." Sexplib.Sexp.pp sexp

let () =
  let ch = open_out sexp_file in
  Sexplib.Sexp.output ch sexp;
  close_out ch

let mods =
  try
    Typing.type_mlw_file env [] sexp_file mlw_file
  with Loc.Located _ as e ->
    Format.eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(* Checking the VCs *)

let my_tasks : Task.task list =
  let mods =
    Wstdlib.Mstr.fold
      (fun _ m acc ->
       List.rev_append
         (Task.split_theory m.Pmodule.mod_theory None None) acc)
      mods []
  in List.rev mods



let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

let limits =
  Call_provers.{empty_limits with
                limit_time = Whyconf.timelimit main;
                limit_mem = Whyconf.memlimit main }

let alt_ergo : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 1
  end else
    snd (Whyconf.Mprover.max_binding provers)

let alt_ergo_driver : Driver.driver =
  try
    Driver.load_driver_for_prover main env alt_ergo
  with e ->
    eprintf "Failed to load driver for alt-ergo: %a@."
      Exn_printer.exn_printer e;
    exit 1

let () =
  List.iteri (fun i t ->
      let call =
        Driver.prove_task ~limits ~config:main
          ~command:alt_ergo.Whyconf.command alt_ergo_driver t in
      let r = Call_provers.wait_on_call call in
      printf "@[On task %d, Alt-ergo answers %a@]@." (succ i)
        (Call_provers.print_prover_result ~json:false) r)
    my_tasks

let () =
  printf "You can try the same example in the IDE using@\n";
  printf "  why3 ide %s@." sexp_file

(*
Local Variables:
compile-command: "make -C ../.. test-api-epsilon"
End:
*)
