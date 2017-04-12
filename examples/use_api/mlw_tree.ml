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

let int_theory : Theory.theory =
  Env.read_theory env ["int"] "Int"

let mul_int : Term.lsymbol =
  Theory.ns_find_ls int_theory.Theory.th_export ["infix *"]

let unit_type = Ty.ty_tuple []

(* start a parsing *)

let pathname = [] (* dummy pathname *)

let t : Ptree.incremental = Mlw_typing.open_file env pathname

open Ptree

(*
type incremental = {
  open_theory     : ident -> unit;
  close_theory    : unit -> unit;
  open_module     : ident -> unit;
  close_module    : unit -> unit;
  open_namespace  : string -> unit;
  close_namespace : loc -> bool (*import:*) -> unit;
  new_decl        : loc -> decl -> unit;
  new_pdecl       : loc -> pdecl -> unit;
  use_clone       : loc -> use_clone -> unit;
}
*)



(* start a module *)

let mk_ident ?(label=[]) ?(loc=Loc.dummy_position) s = {
  id_str = s; id_lab=label; id_loc = loc
}

let m = t.open_module (mk_ident "Program")


(* use int.Int *)

let mk_qid l =
  let rec aux l =
    match l with
      | [] -> assert false
      | [x] -> Qident(mk_ident x)
      | x::r -> Qdot(aux r,mk_ident x)
  in
  aux (List.rev l)

let use_int_Int =
  let qualid = mk_qid ["int" ; "Int"] in
  {
  use_theory = qualid;
  use_import = Some(true,"Int");
}

let () = t.use_clone Loc.dummy_position (use_int_Int,None)

let mul_int = mk_qid ["Int";"infix *"]

let mk_lexpr p = { term_loc = Loc.dummy_position;
                   term_desc = p }

let mk_const s =
  mk_lexpr (Tconst(Number.ConstInt(Number.int_const_dec s)))

let mk_expr e = { expr_desc = e; expr_loc = Loc.dummy_position }

(* declaration of
     let f (_dummy:unit) : unit
        requires { true }
        ensures { true }
      =
        assert { 6*7 = 42 }
 *)
let d : pdecl =
  let args =
    [Loc.dummy_position,Some(mk_ident "_dummy"),false,Some(PTtuple [])]
  in
  let spec = {
    sp_pre = [];
    sp_post = [];
    sp_xpost = [];
    sp_reads = [];
    sp_writes = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
  }
  in
  let body =
    let c6 = mk_const "6" in
    let c7 = mk_const "7" in
    let c42 = mk_const "42" in
    let c6p7 = mk_lexpr (Tidapp(mul_int,[c6;c7])) in
    let p = mk_lexpr (Tinfix(c6p7,mk_ident "infix =",c42)) in
    mk_expr(Eassert(Aassert,p))
  in
  Dfun(mk_ident "f",Gnone,(args,None,body,spec))

let () =
  try t.new_pdecl Loc.dummy_position d
  with e ->
    Format.printf "Exception raised during typing of d:@ %a@."
      Exn_printer.exn_printer e


(*

declaration of
     let f (_dummy:unit) : unit
        requires { true }
        ensures { result = 0 }
      =
        let x = ref 0 in
        !x

*)


(* TODO *)

(*
(* import the ref.Ref module *)

let ref_modules, ref_theories =
  Env.read_lib_file (Mlw_main.library_of_env env) ["ref"]

let ref_module : Mlw_module.modul = Stdlib.Mstr.find "Ref" ref_modules

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
      let c0 = Mlw_expr.e_const (Number.ConstInt (Number.int_const_dec "0")) in
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


*)




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
compile-command: "ocaml -I ../../lib/why3 unix.cma nums.cma str.cma dynlink.cma ../../lib/why3/why3.cma mlw_tree.ml"
End:
*)
