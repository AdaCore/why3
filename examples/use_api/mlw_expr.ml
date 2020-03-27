(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
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
(* END{buildenv} *)

(*

declaration of
BEGIN{source2}
     let f2 () : int
        requires { true }
        ensures { result >= 0 }
      = let x = ref 42 in !x
END{source2}

*)

(* BEGIN{code2_import} *)
let int_module : Pmodule.pmodule =
  Pmodule.read_module env ["int"] "Int"

let ge_int : Term.lsymbol =
  Theory.ns_find_ls int_module.Pmodule.mod_theory.Theory.th_export
    [Ident.op_infix ">="]

let ref_module : Pmodule.pmodule =
  Pmodule.read_module env ["ref"] "Ref"

let ref_type : Ity.itysymbol =
  Pmodule.ns_find_its ref_module.Pmodule.mod_export ["ref"]

(* the "ref" function *)
let ref_fun : Expr.rsymbol =
  Pmodule.ns_find_rs ref_module.Pmodule.mod_export ["ref"]

(* the "!" function *)
let get_fun : Expr.rsymbol =
  Pmodule.ns_find_rs ref_module.Pmodule.mod_export [Ident.op_prefix "!"]

(* END{code2_import} *)


(* BEGIN{code2} *)
let d2 =
  let id = Ident.id_fresh "f" in
  let post =
    let result =
      Term.create_vsymbol (Ident.id_fresh "result") Ty.ty_int
    in
    let post = Term.ps_app ge_int [Term.t_var result; Term.t_nat_const 0] in
    Ity.create_post result post
  in
  let body =
    (* building expression "ref 42" *)
    let e =
      let c0 = Expr.e_const (Constant.int_const_of_int 42) Ity.ity_int in
      let refzero_type = Ity.ity_app ref_type [Ity.ity_int] [] in
      Expr.e_app ref_fun [c0] [] refzero_type
    in
    (* building the first part of the let x = ref 42 *)
    let id_x = Ident.id_fresh "x" in
    let letdef, var_x = Expr.let_var id_x e in
    (* building expression "!x" *)
    let bang_x = Expr.e_app get_fun [Expr.e_var var_x] [] Ity.ity_int in
    (* the complete body *)
    Expr.e_let letdef bang_x
  in
  let arg_unit =
    let unit = Ident.id_fresh "unit" in
    Ity.create_pvsymbol unit Ity.ity_unit
  in
  let def,_rs = Expr.let_sym id
      (Expr.c_fun [arg_unit] [] [post] Ity.Mxs.empty Ity.Mpv.empty body) in
  Pdecl.create_let_decl def

(* END{code2} *)

(* BEGIN{createmodule} *)
let mod2 =
  let uc : Pmodule.pmodule_uc =
    Pmodule.create_module env (Ident.id_fresh "MyModule")
  in
  let uc = Pmodule.use_export uc int_module in
  let uc = Pmodule.use_export uc ref_module in
  let uc = Pmodule.add_pdecl ~vc:true uc d2 in
  Pmodule.close_module uc
(* END{createmodule} *)

(* Checking the VCs *)

(* BEGIN{checkingvcs} *)
let my_tasks : Task.task list =
  Task.split_theory mod2.Pmodule.mod_theory None None

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
    exit 1
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

(*
Local Variables:
compile-command: "ocaml -I ../../lib/why3 unix.cma nums.cma str.cma dynlink.cma -I `ocamlfind query menhirLib` menhirLib.cmo -I `ocamlfind query camlzip` zip.cma ../../lib/why3/why3.cma mlw_tree.ml"
End:
*)
