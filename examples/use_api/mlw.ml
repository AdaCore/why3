(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*******************

This file builds some MLW modules using the API

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

let int_theory : Theory.theory =
  Env.read_theory env ["int"] "Int"

let mul_int : Term.lsymbol =
  Theory.ns_find_ls int_theory.Theory.th_export ["infix *"]

let unit_type = Ty.ty_tuple []

(* start a module named "Program" *)
let m = Mlw_module.create_module env (Ident.id_fresh "Program")


(* declaration of
     let f (_dummy:unit) : unit
        requires { true }
        ensures { true }
      =
        assert { 6*7 = 42 }
 *)
let d =
  let args =
    [Mlw_ty.create_pvsymbol (Ident.id_fresh "_dummy") Mlw_ty.ity_unit]
  in
  let result = Term.create_vsymbol (Ident.id_fresh "result") unit_type in
  let spec = {
    Mlw_ty.c_pre = Term.t_true;
    c_post = Mlw_ty.create_post result Term.t_true;
    c_xpost = Mlw_ty.Mexn.empty;
    c_effect = Mlw_ty.eff_empty;
    c_variant = [];
    c_letrec  = 0;
  }
  in
  let body =
    let c6  = Term.t_nat_const 6 in
    let c7  = Term.t_nat_const 7 in
    let c42 = Term.t_nat_const 42 in
    let p =
      Term.t_equ (Term.t_app_infer mul_int [c6;c7]) c42
    in
    Mlw_expr.e_assert Mlw_expr.Aassert p
  in
  let lambda = {
    Mlw_expr.l_args = args;
    l_expr = body;
    l_spec = spec;
  }
  in
  let def = Mlw_expr.create_fun_defn (Ident.id_fresh "f") lambda in
  Mlw_decl.create_rec_decl [def]

(*

declaration of
     let f (_dummy:unit) : unit
        requires { true }
        ensures { result = 0 }
      =
        let x = ref 0 in
        !x

*)


(* import the ref.Ref module *)

let ref_module : Mlw_module.modul =
  Mlw_module.read_module env ["ref"] "Ref"

let ref_type : Mlw_ty.T.itysymbol =
  Mlw_module.ns_find_its ref_module.Mlw_module.mod_export ["ref"]

(* the "ref" function *)
let ref_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["ref"]

(* the "!" function *)
let get_fun : Mlw_expr.psymbol =
  Mlw_module.ns_find_ps ref_module.Mlw_module.mod_export ["prefix !"]

let d2 =
  let args =
    [Mlw_ty.create_pvsymbol (Ident.id_fresh "_dummy") Mlw_ty.ity_unit]
  in
  let result = Term.create_vsymbol (Ident.id_fresh "result") Ty.ty_int in
  let spec = {
    Mlw_ty.c_pre = Term.t_true;
    c_post = Mlw_ty.create_post result Term.t_true;
    c_xpost = Mlw_ty.Mexn.empty;
    c_effect = Mlw_ty.eff_empty;
    c_variant = [];
    c_letrec  = 0;
  }
  in
  let body =
    (* building expression "ref 0" *)
    let e =
      (* recall that "ref" has polymorphic type "(v:'a) -> ref 'a".
         We need to build an instance of it *)
      (* we build "ref int" with a *fresh* region *)
      let ity = Mlw_ty.ity_app_fresh ref_type [Mlw_ty.ity_int] in
      (* e1 : the appropriate instance of "ref" *)
      let e1 = Mlw_expr.e_arrow ref_fun [Mlw_ty.ity_int] ity in
      (* we apply it to 0 *)
      let c0 = Mlw_expr.e_const
        (Number.ConstInt (Number.int_const_dec "0")) Mlw_ty.ity_int in
      Mlw_expr.e_app e1 [c0]
    in
    (* building the first part of the let x = ref 0 *)
    let letdef, var_x = Mlw_expr.create_let_pv_defn (Ident.id_fresh "x") e in
    (* building expression "!x" *)
    let bang_x =
      (* recall that "!" as type "ref 'a -> 'a" *)
      let e1 = Mlw_expr.e_arrow get_fun [var_x.Mlw_ty.pv_ity] Mlw_ty.ity_int in
      Mlw_expr.e_app e1 [Mlw_expr.e_value var_x]
    in
    (* the complete body *)
    Mlw_expr.e_let letdef bang_x
  in
  let lambda = {
    Mlw_expr.l_args = args;
    l_expr = body;
    l_spec = spec;
  }
  in
  let def = Mlw_expr.create_fun_defn (Ident.id_fresh "f") lambda in
  Mlw_decl.create_rec_decl [def]






(* TODO: continue *)

(*
let () = Printexc.record_backtrace true

let () =
  try
    let _buggy : Mlw_module.module_uc = Mlw_module.add_pdecl ~wp:true m d in
    ()
  with Not_found ->
    Printexc.print_backtrace stderr;
    flush stderr
*)



(*
Local Variables:
compile-command: "ocaml -I ../../lib/why3 unix.cma nums.cma str.cma dynlink.cma ../../lib/why3/why3.cma mlw.ml"
End:
*)
