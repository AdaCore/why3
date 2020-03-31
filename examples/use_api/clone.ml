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

This file builds some MLW modules using the API
In particular, it tests the clone feature
(Inspired from mlw_tree.ml)

******************)

open Why3

let () = Debug.set_flag Debug.stack_trace
let config : Whyconf.config =
  Whyconf.(load_default_config_if_needed (read_config None))
let main : Whyconf.main = Whyconf.get_main config
let env : Env.env = Env.create_env (Whyconf.loadpath main)
open Ptree

let () = Typing.open_file env [] (* empty pathname *)
let mk_ident s = { id_str = s; id_ats = []; id_loc = Loc.dummy_position }
let () = Typing.open_module (mk_ident "Test")


(* Auxiliary functions (same as mlw_tree.ml) *)
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
  Typing.add_decl loc (Ptree.Duseimport (loc,true, [Qdot (Qident (mk_ident f), m), None]))

let use_int_Int = use_import ("int","Int")

let mk_expr e = { expr_desc = e; expr_loc = Loc.dummy_position }

let mk_term t = { term_desc = t; term_loc = Loc.dummy_position }

let mk_pat p = { pat_desc = p; pat_loc = Loc.dummy_position }
let pat_var id = mk_pat (Pvar id)

let mk_var id = mk_term (Tident (Qident id))

let param0 = [Loc.dummy_position, None, false, Some (PTtuple [])]
let param1 id ty = [Loc.dummy_position, Some id, false, Some ty]

let mk_const i =
  Constant.(ConstInt Number.{ il_kind = ILitDec; il_int = BigInt.of_int i })

let mk_tconst i = mk_term (Tconst (mk_const i))

let mk_econst i = mk_expr (Econst (mk_const i))

let mk_tapp f l = mk_term (Tidapp(f,l))

let mk_eapp f l = mk_expr (Eidapp(f,l))

let mk_evar x = mk_expr(Eident(Qident x))

let eq_symb = mk_qid [Ident.op_infix "="]
let int_type_id = mk_qid ["int"]
let int_type = PTtyapp(int_type_id,[])

let a = mk_ident "a"

(* type a = < range 22 46 > *)
let type_a : Ptree.decl =
  let c22 = BigInt.of_int 22 in
  let c46 = BigInt.of_int 46 in
  Dtype [{
    td_loc = Loc.dummy_position;
    td_ident = a;
    td_params = [];
    td_vis = Public;
    td_mut = false;
    td_inv = [];
    td_wit = [];
    td_def = TDrange (c22, c46);
  }]

(*
  let f2 (b : 'a) =
     ensures {result = false}
     true
*)
let d2 : Ptree.decl =
  let id_b = mk_ident "_b" in
  let pre = mk_term Ttrue in
  let result = mk_ident "result" in
  let post = mk_tapp eq_symb [mk_var result; mk_term Tfalse] in
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
    sp_partial = false;
  }
  in
  let body: expr = mk_expr Etrue in
  let f1 =
    Efun(param1 id_b (PTtyvar a), None,  mk_pat Pwild,
         Ity.MaskVisible, spec, body)
  in
  Dlet(mk_ident "f2",false,Expr.RKnone, mk_expr f1)

(*
  let f3 (b : a) =
     ensures {a'int b  = 42}
     true
*)
let d3 : Ptree.decl =
  let id_b = mk_ident "b" in
  let pre = mk_term Ttrue in
  let a_int = mk_qid ["a'int"] in
  let result = mk_ident "_result" in
  let post = mk_tapp eq_symb [mk_tapp a_int [mk_var id_b];
                              mk_tconst 42] in
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
    sp_partial = false;
  }
  in
  let body: expr = mk_evar id_b in
  let f1 =
    Efun(param1 id_b (PTtyapp (Qident a, [])), None,  mk_pat Pwild,
         Ity.MaskVisible, spec, body)
  in
  Dlet(mk_ident "f3",false,Expr.RKnone, mk_expr f1)



(*
  let f1 (b : a) =
    requires {a'int b = 42}
    ensures {a'int result = a'int b}
    (42:a)
*)
let d1 : Ptree.decl =
  let id_b = mk_ident "b" in
  let a_int = mk_qid ["a'int"] in
  let pre = mk_tapp eq_symb [mk_tapp a_int [mk_var id_b];
                             mk_tconst 42] in
  let result = mk_ident "result" in
  let post = mk_tapp eq_symb [mk_tapp a_int [mk_var result];
                              mk_tapp a_int [mk_var id_b]] in
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
    sp_partial = false;
  }
  in
  let body: expr = mk_expr (Ecast (mk_econst 42, PTtyapp (Qident a, []))) in
  let f1 =
    Efun(param1 id_b (PTtyapp (Qident a, [])), None,  mk_pat Pwild,
         Ity.MaskVisible, spec, body)
  in
  Dlet(mk_ident "f1",false,Expr.RKnone, mk_expr f1)


(* Add those declarations *)
let () = Typing.add_decl Loc.dummy_position type_a
let () = Typing.add_decl Loc.dummy_position d2
let () = Typing.add_decl Loc.dummy_position d3
let () = Typing.add_decl Loc.dummy_position d1

let () = Typing.close_module Loc.dummy_position

(* New module is clone of this one *)
let () = Typing.open_module (mk_ident "Test1")

(*
module Test1
  clone Test as T
end
*)
let clone_decl : Ptree.decl =
  Dcloneimport (Loc.dummy_position, false, Qident (mk_ident "Test"), Some (mk_ident "T"),[])

let () = Typing.add_decl Loc.dummy_position clone_decl

let () = Typing.close_module Loc.dummy_position

(* End of file *)
let mods : Pmodule.pmodule Wstdlib.Mstr.t = Typing.close_file ()

open Format

let () =
  printf "Theory are:@.";
  Wstdlib.Mstr.iter
    (fun _ m ->
      printf "%a@." Pretty.print_theory m.Pmodule.mod_theory) mods

(* Only use of this is to test clone_export *)
let auto_clone task th =
  Task.clone_export task th Theory.empty_inst

let my_tasks : Task.task list =
  let mods =
    Wstdlib.Mstr.fold
      (fun _ m acc ->
        let th = m.Pmodule.mod_theory in
        (* Automatically clone all theories *)
        let task =
          auto_clone None th
        in
        List.rev_append
          (Task.split_theory m.Pmodule.mod_theory None task) acc)
      mods []
  in
  List.rev mods

let () =
  printf "Tasks are:@.";
  let _ =
    List.fold_left
      (fun i t -> printf "Task %d: %a@." i Pretty.print_task t; i+1)
      1 my_tasks
  in ()
