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

open Wstdlib
open Ident
open Ty
open Term
open Decl

let make_pont = Wty.memoize 3 (fun ty ->
  let t2tb =
    let t2tb_name = "t2tb" in
    let t2tb_id = Libencoding.id_unprotected t2tb_name in
    create_fsymbol t2tb_id [ty] ty in
  let tb2t =
    let tb2t_name = "tb2t" in
    let tb2t_id = Libencoding.id_unprotecting tb2t_name in
    create_fsymbol tb2t_id [ty] ty in
  let t2tb_def = create_param_decl t2tb in
  let tb2t_def = create_param_decl tb2t in
  let bridge_l =
    let x_vs = create_vsymbol (id_fresh "i") ty in
    let x_t = t_var x_vs in
    let t2tb_x = fs_app t2tb [x_t] ty in
    let tb2t_t2tb_x = fs_app tb2t [t2tb_x] ty in
    let eq = t_equ tb2t_t2tb_x x_t in
    let ax = t_forall_close [x_vs] [[t2tb_x]] eq in
    let pr = create_prsymbol (id_fresh "BridgeL") in
    create_prop_decl Paxiom pr ax in
  let bridge_r =
    let x_vs = create_vsymbol (Libencoding.id_unprotected "j") ty in
    let x_t = t_var x_vs in
    let tb2t_x = fs_app tb2t [x_t] ty in
    let t2tb_tb2t_x = fs_app t2tb [tb2t_x] ty in
    let eq = t_equ t2tb_tb2t_x x_t in
    let ax = t_forall_close [x_vs] [[t2tb_tb2t_x]] eq in
    let pr = create_prsymbol (id_fresh "BridgeR") in
    create_prop_decl Paxiom pr ax in
  t2tb, tb2t, [t2tb_def; tb2t_def; bridge_l; bridge_r])

let seen_h = Hty.create 7
let seen_q = Queue.create ()

let check_in ty =
  if not (Hty.mem seen_h ty) then begin
    Hty.add seen_h ty ();
    Queue.add ty seen_q
  end

let add_decls tenv decls =
  let add decls ty =
    let _,_,defs = Mty.find ty tenv in
    List.append defs decls in
  let decls = Queue.fold add decls seen_q in
  Queue.clear seen_q;
  Hty.clear seen_h;
  decls

let conv_arg tenv t aty =
  let tty = t_type t in
  if ty_equal tty aty then t else
  try
    let t2tb,tb2t,_ = Mty.find tty tenv in
    check_in tty;
    match t.t_node with
      | Tapp (fs,[t]) when ls_equal fs tb2t -> t
      | _ -> fs_app t2tb [t] tty
  with Not_found -> t

let conv_app tenv fs tl tty =
  let t = fs_app fs tl tty in
  let vty = Opt.get fs.ls_value in
  if ty_equal tty vty then t else
  try
    let _,tb2t,_ = Mty.find tty tenv in
    check_in tty;
    fs_app tb2t [t] tty
  with Not_found -> t

(* FIXME? in quantifiers we might generate triggers
   with unnecessary bridge functions over them *)
let rec rewrite tenv t = match t.t_node with
  | Tapp (ls,[t1;t2]) when ls_equal ls ps_equ ->
      t_attr_copy t (t_equ (rewrite tenv t1) (rewrite tenv t2))
  | Tapp (ls,tl) ->
      let tl = List.map (rewrite tenv) tl in
      let tl = List.map2 (conv_arg tenv) tl ls.ls_args in
      if t.t_ty = None then t_attr_copy t (ps_app ls tl)
      else t_attr_copy t (conv_app tenv ls tl (t_type t))
  | _ -> t_map (rewrite tenv) t

let decl tenv d = match d.d_node with
  | Dtype _ | Dparam _ -> [d]
  | Ddata _ -> Printer.unsupportedDecl d
      "Algebraic and recursively-defined types are \
            not supported, run eliminate_algebraic"
  | Dlogic [ls,ld] when not (Sid.mem ls.ls_name d.d_syms) ->
      let f = rewrite tenv (ls_defn_axiom ld) in
      Libencoding.defn_or_axiom ls f
  | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively defined symbols are not supported, run eliminate_recursion"
  | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
  | Dprop (k,pr,f) ->
      [create_prop_decl k pr (rewrite tenv f)]

let decl tenv d =
  let decls = decl tenv d in
  add_decls tenv decls

let t = Trans.on_tagged_ty Libencoding.meta_kept (fun s ->
  Trans.decl (decl (Mty.mapi (fun ty () -> make_pont ty) s)) None)

let () = Hstr.replace Encoding.ft_enco_kept "twin" (Util.const t)
