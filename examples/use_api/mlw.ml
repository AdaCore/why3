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
let m = Pmodule.create_module env (Ident.id_fresh "Program")


(* declaration of
     let f (_dummy:unit) : unit
        requires { true }
        ensures { true }
      =
        assert { 6*7 = 42 }
 *)
let d =
  let id = Ident.id_fresh "f" in
  let args =
    [None,false,Dexpr.dity_of_ity Ity.ity_unit]
  in
  let body denv =
    let spec_later _lvm _exn _old _ret_type =
      {
        Dexpr.ds_pre = [];
        Dexpr.ds_post = [];
        Dexpr.ds_xpost = Ity.Mxs.empty;
        Dexpr.ds_reads = [];
        Dexpr.ds_writes = [];
        Dexpr.ds_diverge = false;
        Dexpr.ds_checkrw = false;
      }
    in
    let variants _lvm _exn _old = [Term.t_nat_const 0,None] in
    let body =
      let c6 = Term.t_nat_const 6 in
      let c7 = Term.t_nat_const 7 in
      let c42 = Term.t_nat_const 42 in
      let p =
        Term.t_equ (Term.t_app_infer mul_int [c6;c7]) c42
      in
      Dexpr.dexpr (Dexpr.DEassert(Expr.Assert,(fun _lvm _exn _old -> p)))
    in
    (spec_later,variants,body)
  in
  let predef = (id, false (* function is not ghost *),
                Expr.RKnone (* function is not intended to be used in the specifications *),
                args,
                Dexpr.dity_of_ity Ity.ity_unit,
                Ity.MaskVisible,
                body)
  in
  let denv,def = Dexpr.drec_defn Dexpr.denv_empty [predef] in
  let def = Dexpr.rec_defn def in
  Format.eprintf "It works!@.";
  def


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

let d2 =
  let id = Ident.id_fresh "f" in
  let args =
    [None,false,Dexpr.dity_of_ity Ity.ity_unit]
  in
  let body denv =
    let spec_later _lvm _exn _old _ret_type =
      let result =
        Ity.create_pvsymbol (Ident.id_fresh "result") _ret_type (*Ty.ty_int*)
      in
      let post =
        Term.ps_app Term.ps_equ [Term.t_var result.Ity.pv_vs; Term.t_nat_const 0]
      in
      {
        Dexpr.ds_pre = [];
        Dexpr.ds_post = [result,post];
        Dexpr.ds_xpost = Ity.Mxs.empty;
        Dexpr.ds_reads = [];
        Dexpr.ds_writes = [];
        Dexpr.ds_diverge = false;
        Dexpr.ds_checkrw = false;
      }
    in
    let variants _lvm _exn _old = [Term.t_nat_const 0,None] in
    let int_type =  Dexpr.dity_of_ity Ity.ity_int in
    let body =
      (* building expression "ref 0" *)
      let e =
        let c0 =
          Dexpr.dexpr
            (Dexpr.DEconst(Number.const_of_int 0,int_type))
        in
        let f = Dexpr.dexpr(Dexpr.DEsym (Pmodule.RS ref_fun)) in
        Dexpr.dexpr (Dexpr.DEapp(f,c0))
      in
      (* building the first part of the let x = ref 0 *)
      let id_x = Ident.id_fresh "x" in
      let typ_x = Ity.ity_app ref_type [Ity.ity_int] [] in
      let var_x = Ity.create_pvsymbol id_x typ_x in
      let letdef = (id_x,false,Expr.RKlocal,e) in
      (* building expression "!x" *)
      let bang_x =
        let f = Dexpr.dexpr(Dexpr.DEsym (Pmodule.RS get_fun)) in
        Dexpr.dexpr
          (Dexpr.DEapp(f,Dexpr.dexpr(Dexpr.DEpv_pure var_x)))
      in
      (* the complete body *)
      Dexpr.dexpr(Dexpr.DElet(letdef,bang_x))
    in (spec_later,variants,body)
  in
    let predef = (id, false (* function is not ghost *),
                Expr.RKnone (* function is not intended to be used in the specifications *),
                args,
                Dexpr.dity_of_ity Ity.ity_int,
                Ity.MaskVisible,
                body)
  in
  let denv,def = Dexpr.drec_defn Dexpr.denv_empty [predef] in
  try
    let def = Dexpr.rec_defn def in
  Format.eprintf "It works!@.";
  def
  with exn -> Format.eprintf "error: %a@." Exn_printer.exn_printer exn;
              exit 1

let d2' =
  let id = Ident.id_fresh "f" in
  let post =
    let result =
      Term.create_vsymbol (Ident.id_fresh "result") Ty.ty_int
    in
    let post = Term.ps_app Term.ps_equ [Term.t_var result; Term.t_nat_const 0] in
    Ity.create_post result post
  in
  let body =
    (* building expression "ref 0" *)
    let e =
      let c0 = Expr.e_const (Number.int_const_of_int 0) Ity.ity_int in
      let refzero_type = Ity.ity_app ref_type [Ity.ity_int] [] in
      let f = Expr.e_app ref_fun [c0] [] refzero_type in
      Expr.e_func_app f c0
    in
    (* building the first part of the let x = ref 0 *)
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
  let def,rs = Expr.let_sym id
      (Expr.c_fun [arg_unit] [] [post] Ity.Mxs.empty Ity.Mpv.empty body) in
  try
    let def = Pdecl.create_let_decl def in
    Format.eprintf "It works!@.";
    def
  with exn -> Format.eprintf "error: %a@." Exn_printer.exn_printer exn;
    exit 1


(*
 (* let f (a:array int)
      requires { a.length >= 1 }
      ensures { a[0] = 42 }
    = a[0] <- 42
  *)


let array_module : Pmodule.modul =
  Pmodule.read_module env ["array"] "Array"

let array_theory : Theory.theory =
  array_module.Pmodule.mod_theory

let array_type : Pty.T.itysymbol =
  Pmodule.ns_find_its array_module.Pmodule.mod_export ["array"]

let ls_length : Term.lsymbol =
  Theory.ns_find_ls array_theory.Theory.th_export ["length"]

(* the "[]" logic symbol *)
let ls_select : Term.lsymbol =
  Theory.ns_find_ls array_theory.Theory.th_export ["mixfix []"]

(* the "[]<-" program symbol *)
let store_fun : Expr.psymbol =
  Pmodule.ns_find_ps array_module.Pmodule.mod_export ["mixfix []<-"]


let d3 =
  try
  let ity = Pty.ity_app_fresh array_type [Pty.ity_int] in
  let a = Pty.create_pvsymbol (Ident.id_fresh "a") ity in
  let result = Term.create_vsymbol (Ident.id_fresh "result") (Ty.ty_tuple []) in
  let pre =
    Term.ps_app ge_int
                [Term.t_app_infer ls_length [Term.t_var a.Pty.pv_vs];Term.t_nat_const 1]
  in
  let post =
    Term.ps_app Term.ps_equ
                [Term.t_app_infer ls_select [Term.t_var a.Pty.pv_vs;Term.t_nat_const 0 ] ;
                 Term.t_nat_const 42 ]
  in
  let spec = {
    Pty.c_pre = pre;
    c_post = Pty.create_post result post;
    c_xpost = Pty.Mexn.empty;
    c_effect = Pty.eff_empty;
    c_variant = [];
    c_letrec  = 0;
  }
  in
  (* building expression "a[0]<-42" *)
  let e1 = Expr.e_arrow store_fun [ity;Pty.ity_int;Pty.ity_int] Pty.ity_unit in
  let body =
    Expr.e_app e1
                   [Expr.e_value a;
                    Expr.e_const (Number.const_of_int 0) Pty.ity_int;
                    Expr.e_const (Number.const_of_int 42) Pty.ity_int]
  in
  let lambda = {
    Expr.l_args = [a];
    l_expr = body;
    l_spec = spec;
  }
  in
  let def = Expr.create_fun_defn (Ident.id_fresh "f") lambda in
    Pdecl.create_rec_decl [def]
  with e -> Format.eprintf "Error: %a@." Exn_printer.exn_printer e;
            exit 1

 *)



(* TODO: continue *)

(*
let () = Printexc.record_backtrace true

let () =
  try
    let _buggy : Pmodule.module_uc = Pmodule.add_pdecl ~wp:true m d in
    ()
  with Not_found ->
    Printexc.print_backtrace stderr;
    flush stderr
*)



(*
Local Variables:
compile-command: "ocaml -I ../../lib/why3 unix.cma nums.cma str.cma dynlink.cma -I `ocamlfind query menhirLib` menhirLib.cmo -I `ocamlfind query camlzip` zip.cma ../../lib/why3/why3.cma mlw.ml"
End:
*)
