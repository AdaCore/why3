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

(*******************

This file builds some MLW modules, using parse trees instead of direct
API calls

******************)

(* opening the Why3 library *)
open Why3

(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config None
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config


(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

let () = Typing.open_file env [] (* dummy pathname *)

open Ptree

let mk_ident ?(label=[]) ?(loc=Loc.dummy_position) s = {
  id_str = s; id_lab=label; id_loc = loc
}

(* start a module *)

let m = Typing.open_module (mk_ident "Program")


(* use int.Int *)

let mk_qid l =
  let rec aux l =
    match l with
      | [] -> assert false
      | [x] -> Qident(mk_ident x)
      | x::r -> Qdot(aux r,mk_ident x)
  in
  aux (List.rev l)

let eq_symb = mk_qid [Ident.infix "="]

let use_import (f, m) =
  let loc = Loc.dummy_position in
  let m = mk_ident ~loc m in
  Typing.open_scope loc m;
  Typing.add_decl loc (Ptree.Duse (Qdot (Qident (mk_ident ~loc f), m)));
  Typing.close_scope loc ~import:true

let use_int_Int = use_import ("int","Int")

let int_type = mk_qid ["int"]

let mul_int = mk_qid ["Int";Ident.infix "*"]

let mk_expr e = { expr_desc = e; expr_loc = Loc.dummy_position }

let mk_term t = { term_desc = t; term_loc = Loc.dummy_position }

let mk_pat p = { pat_desc = p; pat_loc = Loc.dummy_position }

let no_params ~loc = [loc, None, false, Some (PTtuple [])]

let param ~loc id ty = [loc, Some id, false, Some ty]

let mk_tconst s =
  mk_term
    (Tconst
       Number.(ConstInt { ic_negative = false ; ic_abs = int_literal_dec s }))

let mk_econst s =
  mk_expr
    (Econst
       Number.(ConstInt { ic_negative = false ; ic_abs = int_literal_dec s }))



(* declaration of
     let f (_dummy:unit) : unit
        requires { true }
        ensures { true }
      =
        assert { 6*7 = 42 }
 *)
let d : decl =
  let spec = {
    sp_pre = [];
    sp_post = [];
    sp_xpost = [];
    sp_reads = [];
    sp_writes = [];
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
  }
  in
  let body =
    let c6 = mk_tconst "6" in
    let c7 = mk_tconst "7" in
    let c42 = mk_tconst "42" in
    let c6p7 = mk_term (Tidapp(mul_int,[c6;c7])) in
    let p = mk_term (Tidapp(eq_symb,[c6p7;c42])) in
    mk_expr(Eassert(Expr.Assert,p))
  in
  let f = Efun(no_params Loc.dummy_position,None,Ity.MaskVisible,spec,body)
  in
  Dlet(mk_ident "f",false,Expr.RKnone, mk_expr f)

let () =
  try Typing.add_decl Loc.dummy_position d
  with e ->
    Format.printf "Exception raised during typing of d:@ %a@."
      Exn_printer.exn_printer e


(*

declaration of
     let f (_dummy:unit) : unit
        requires { true }
        ensures { result >= 0 }
      =
        let x = ref 42 in
        !x

*)

let ge_int = mk_qid ["Int";Ident.infix ">="]

let use_ref_Ref = use_import ("ref","Ref")

let mk_var id = mk_term (Tident (Qident id))

let pat_var id = mk_pat (Pvar (id,false))

let d2 =
  let result = mk_ident "result" in
  let post = mk_term(Tidapp(ge_int,[mk_var result;mk_tconst "0"])) in
  let spec = {
    sp_pre = [];
    sp_post = [Loc.dummy_position,[pat_var result,post]];
    sp_xpost = [];
    sp_reads = [];
    sp_writes = [];
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
  }
  in
  let body =
    let e1 = mk_expr(Eidapp(mk_qid ["Ref";"ref"],[mk_econst "42"])) in
    let id_x = mk_ident "x" in
    let e2 = mk_expr(Eidapp(mk_qid ["Ref";Ident.prefix "!"],
                            [mk_expr(Eident(Qident id_x))])) in
    mk_expr(Elet(id_x,false,Expr.RKlocal,e1,e2))
  in
  let f = Efun(no_params Loc.dummy_position,None,Ity.MaskVisible,spec,body)
  in
  Dlet(mk_ident "f2",false,Expr.RKnone, mk_expr f)

let () =
  try Typing.add_decl Loc.dummy_position d2
  with e ->
    Format.printf "Exception raised during typing of d2:@ %a@."
      Exn_printer.exn_printer e

(* let f (a:array int)
      requires { a.length >= 1 }
      ensures { a[0] = 42 }
    = a[0] <- 42
 *)

let array_module = use_import ("array","Array")

let ty_array = PTtyapp(mk_qid ["Array";"array"],[PTtyapp(int_type,[])])

let length = mk_qid ["Array";"length"]

let array_get = mk_qid ["Array";"mixfix []"]

let array_set = mk_qid ["Array";"mixfix []<-"]

let d3 =
  let id_a = mk_ident "a" in
  let pre = mk_term(Tidapp(ge_int,[mk_term(Tidapp(length,[mk_var id_a]));
                                   mk_tconst "1"])) in
  let result = mk_ident "result" in
  let post =
    mk_term(Tidapp(eq_symb,[mk_term(Tidapp(array_get,[mk_var id_a;mk_tconst "0"]));
                            mk_tconst "42"])) in
  let spec = {
    sp_pre = [pre];
    sp_post = [Loc.dummy_position,[pat_var result,post]];
    sp_xpost = [];
    sp_reads = [];
    sp_writes = [];
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
  }
  in
  let body =
    mk_expr(Eidapp(array_set,
                   [mk_expr(Eident(Qident id_a));
                    mk_econst "0";
                    mk_econst "42"]))
    in
  let f = Efun(param Loc.dummy_position id_a ty_array,
               None,Ity.MaskVisible,spec,body)
  in
  Dlet(mk_ident "f3",false,Expr.RKnone, mk_expr f)

let () =
  try Typing.add_decl Loc.dummy_position d3
  with e ->
    Format.printf "Exception raised during typing of d3:@ %a@."
      Exn_printer.exn_printer e



let () = Typing.close_module Loc.dummy_position

let mods = Typing.close_file ()

                             (* Checking the VCs *)

let my_tasks : Task.task list =
  let mods =
    Stdlib.Mstr.fold
      (fun _ m acc ->
       List.rev_append (Task.split_theory m.Pmodule.mod_theory None None) acc)
      mods []
  in List.rev mods




open Format

let () =
  printf "Tasks are:@.";
  let _ =
    List.fold_left
      (fun i t -> printf "Task %d: %a@." i Pretty.print_task t; i+1)
      1 my_tasks
  in ()

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
              i Call_provers.print_prover_result r;
       i+1
      )
      1 my_tasks
  in ()

(*
Local Variables:
compile-command: "ocaml -I ../../lib/why3 unix.cma nums.cma str.cma dynlink.cma -I `ocamlfind query menhirLib` menhirLib.cmo -I `ocamlfind query camlzip` zip.cma ../../lib/why3/why3.cma mlw_tree.ml"
End:
*)
