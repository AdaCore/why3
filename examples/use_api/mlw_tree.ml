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

(* BEGIN{buildenv} *)
open Why3
let config : Whyconf.config = Whyconf.read_config None
let main : Whyconf.main = Whyconf.get_main config
let env : Env.env = Env.create_env (Whyconf.loadpath main)
open Ptree
(* END{buildenv} *)

(* start a module *)
(* BEGIN{openmodule} *)
let () = Typing.open_file env [] (* empty pathname *)
let mk_ident s = { id_str = s; id_lab=[]; id_loc = Loc.dummy_position }
let m = Typing.open_module (mk_ident "Program")
(* END{openmodule} *)


(* use int.Int *)


(* BEGIN{useimport} *)
let mk_qid l =
  let rec aux l =
    match l with
      | [] -> assert false
      | [x] -> Qident(mk_ident x)
      | x::r -> Qdot(aux r,mk_ident x)
  in
  aux (List.rev l)

let use_import (f, m) =
  let m = mk_ident m in
  let loc = Loc.dummy_position in
  Typing.open_scope loc m;
  Typing.add_decl loc (Ptree.Duse (Qdot (Qident (mk_ident f), m)));
  Typing.close_scope loc ~import:true

let use_int_Int = use_import ("int","Int")
(* END{useimport} *)

(* BEGIN{helper1} *)
let mk_expr e = { expr_desc = e; expr_loc = Loc.dummy_position }

let mk_term t = { term_desc = t; term_loc = Loc.dummy_position }

let mk_pat p = { pat_desc = p; pat_loc = Loc.dummy_position }
let pat_var id = mk_pat (Pvar (id,false))

let mk_var id = mk_term (Tident (Qident id))

let param0 = [Loc.dummy_position, None, false, Some (PTtuple [])]
let param1 id ty = [Loc.dummy_position, Some id, false, Some ty]

let mk_tconst s =
  mk_term
    (Tconst
       Number.(ConstInt { ic_negative = false ; ic_abs = int_literal_dec s }))

let mk_econst s =
  mk_expr
    (Econst
       Number.(ConstInt { ic_negative = false ; ic_abs = int_literal_dec s }))

let mk_tapp f l = mk_term (Tidapp(f,l))

let mk_eapp f l = mk_expr (Eidapp(f,l))

let mk_evar x = mk_expr(Eident(Qident x))
(* END{helper1} *)

(* declaration of
  BEGIN{source1}
     let f1 (x:int) : unit
        requires { x=6 }
        ensures { result=42 }
      = x*7
  END{source1}
 *)

(* BEGIN{code1} *)
let eq_symb = mk_qid [Ident.infix "="]
let int_type_id = mk_qid ["int"]
let int_type = PTtyapp(int_type_id,[])
let mul_int = mk_qid ["Int";Ident.infix "*"]

let d1 : decl =
  let id_x = mk_ident "x" in
  let pre = mk_tapp eq_symb [mk_var id_x; mk_tconst "6"] in
  let result = mk_ident "result" in
  let post = mk_tapp eq_symb [mk_var result; mk_tconst "42"] in
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
  let body = mk_eapp mul_int [mk_evar id_x; mk_econst "7"] in
  let f1 = Efun(param1 id_x int_type, None, Ity.MaskVisible, spec, body) in
  Dlet(mk_ident "f1",false,Expr.RKnone, mk_expr f1)

let () =
  try Typing.add_decl Loc.dummy_position d1
  with e ->
    Format.printf "Exception raised during typing of d:@ %a@."
      Exn_printer.exn_printer e
(* END{code1} *)


(*

declaration of
BEGIN{source2}
     let f2 () : int
        requires { true }
        ensures { result >= 0 }
      = let x = ref 42 in !x
END{source2}

*)

(* BEGIN{code2} *)
let ge_int = mk_qid ["Int";Ident.infix ">="]

let use_ref_Ref = use_import ("ref","Ref")

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
    let e1 = mk_eapp (mk_qid ["Ref";"ref"]) [mk_econst "42"] in
    let id_x = mk_ident "x" in
    let e2 = mk_eapp (mk_qid ["Ref";Ident.prefix "!"]) [mk_evar id_x] in
    mk_expr(Elet(id_x,false,Expr.RKlocal,e1,e2))
  in
  let f = Efun(param0,None,Ity.MaskVisible,spec,body)
  in
  Dlet(mk_ident "f2",false,Expr.RKnone, mk_expr f)

let () =
  try Typing.add_decl Loc.dummy_position d2
  with e ->
    Format.printf "Exception raised during typing of d2:@ %a@."
      Exn_printer.exn_printer e
(* END{code2} *)

(*
BEGIN{source3}
let f (a:array int) : unit
      requires { a.length >= 1 }
      ensures { a[0] = 42 }
    = a[0] <- 42
END{source3}
*)

(* BEGIN{code3} *)
let () = use_import ("array","Array")

let array_int_type = PTtyapp(mk_qid ["Array";"array"],[int_type])

let length = mk_qid ["Array";"length"]

let array_get = mk_qid ["Array"; Ident.mixfix "[]"]

let array_set = mk_qid ["Array"; Ident.mixfix "[]<-"]

let d3 =
  let id_a = mk_ident "a" in
  let pre =
    mk_tapp ge_int [mk_tapp length [mk_var id_a]; mk_tconst "1"]
  in
  let post =
    mk_tapp eq_symb [mk_tapp array_get [mk_var id_a; mk_tconst "0"];
                     mk_tconst "42"]
  in
  let spec = {
    sp_pre = [pre];
    sp_post = [Loc.dummy_position,[mk_pat Pwild,post]];
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
    mk_eapp array_set [mk_evar id_a; mk_econst "0"; mk_econst "42"]
  in
  let f = Efun(param1 id_a array_int_type,
               None,Ity.MaskVisible,spec,body)
  in
  Dlet(mk_ident "f3", false, Expr.RKnone, mk_expr f)

let () =
  try Typing.add_decl Loc.dummy_position d3
  with e ->
    Format.printf "Exception raised during typing of d3:@ %a@."
      Exn_printer.exn_printer e
(* END{code3} *)

(* BEGIN{closemodule} *)
let () = Typing.close_module Loc.dummy_position
let mods : Pmodule.pmodule Stdlib.Mstr.t = Typing.close_file ()
(* END{closemodule} *)

(* Checking the VCs *)

(* BEGIN{checkingvcs} *)
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
              i Call_provers.print_prover_result r;
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
