(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task

let meta_kept = register_meta "encoding_decorate : kept" [MTtysymbol]

(* From Encoding Polymorphism CADE07*)

type lconv = { u2t : lsymbol ; t2u : lsymbol }

type tenv = {
  kept : Sts.t option;
  declare_kept : tysymbol -> decl list;
  specials : lconv Hty.t;
  ty_uni : ty;
  trans_lsymbol : lsymbol Hls.t
}

let init_tenv kept =
  let ts_uni = create_tysymbol (id_fresh "uni") [] None in
  let task = use_export None builtin_theory in
  let task = add_ty_decl task [ts_uni, Tabstract] in
  let ty_uni = ty_app ts_uni [] in
  let specials = Hty.create 17 in
  let declare_kept ts =
    let ty = ty_app ts [] in
    let name = ts.ts_name.id_string in
    let u2t = create_fsymbol (id_fresh ("uni2" ^ name)) [ty_uni] ty in
    let t2u = create_fsymbol (id_fresh (name ^ "2uni")) [ty] ty_uni in
    let pr_u = create_prsymbol (id_fresh ("uni2" ^ name ^ "2uni")) in
    let pr_t = create_prsymbol (id_fresh (name ^ "2uni2" ^ name)) in
    let vu = create_vsymbol (id_fresh "vu") ty_uni in
    let vt = create_vsymbol (id_fresh "vt") ty in
    let tu = t_var vu in
    let tt = t_var vt in
    let u2t2u = t_app t2u [t_app u2t [tu] ty] ty_uni in
    let t2u2t = t_app u2t [t_app t2u [tt] ty_uni] ty in
    let u2t2u = f_forall [vu] [] (f_equ u2t2u tu) in
    let t2u2t = f_forall [vt] [] (f_equ t2u2t tt) in
    Hty.add specials ty { u2t = u2t ; t2u = t2u };
    [ create_ty_decl [ts, Tabstract];
      create_logic_decl [u2t, None];
      create_logic_decl [t2u, None];
      create_prop_decl Paxiom pr_u u2t2u;
      create_prop_decl Paxiom pr_t t2u2t ]
  in
  task,
  { kept          = kept;
    declare_kept  = Wts.memoize 7 declare_kept;
    specials      = specials;
    ty_uni        = ty_uni;
    trans_lsymbol = Hls.create 17 }

let is_kept tenv ts =
  ts_equal ts Explicit_polymorphism.ts_ty ||
  ts.ts_args = [] && match tenv.kept with
  | Some s -> Sts.mem ts s
  | None   -> true

(* Convert type *)
let conv_ty tenv ty =
  if Hty.mem tenv.specials ty then ty else tenv.ty_uni

(* Convert a variable *)
let conv_vs tenv vs =
  let ty = conv_ty tenv vs.vs_ty in
  if ty_equal ty vs.vs_ty then vs else
  create_vsymbol (id_dup vs.vs_name) ty

(* Convert a logic symbol to the encoded one *)
let conv_ls tenv ls =
  if ls_equal ls ps_equ || ls_equal ls ps_neq then ls
  else try Hls.find tenv.trans_lsymbol ls with Not_found ->
  let ty_res = Util.option_map (conv_ty tenv) ls.ls_value in
  let ty_arg = List.map (conv_ty tenv) ls.ls_args in
  let ls' =
    if Util.option_eq ty_equal ty_res ls.ls_value &&
       List.for_all2 ty_equal ty_arg ls.ls_args then ls
    else create_lsymbol (id_clone ls.ls_name) ty_arg ty_res
  in
  Hls.add tenv.trans_lsymbol ls ls';
  ls'

(* Convert the argument of a function *)
let conv_arg tenv ty_arg t =
  let ty_val = t.t_ty in
  if ty_equal ty_arg ty_val then t else
  (* ty_val is kept and ty_arg = ty_uni *)
  let lc = Hty.find tenv.specials ty_val in
  t_app lc.t2u [t] ty_arg

let rec rewrite_term tenv vm t =
  let fnT = rewrite_term tenv in
  let fnF = rewrite_fmla tenv in
  match t.t_node with
  | Tconst _ -> t
  | Tvar x ->
      Mvs.find x vm
  | Tapp (fs,tl) ->
      let fs = conv_ls tenv fs in
      let fn ty t = conv_arg tenv ty (fnT vm t) in
      let tl = List.map2 fn fs.ls_args tl in
      let nt = t_app fs tl (of_option fs.ls_value) in
      (* convert if nt.t_ty = ty_uni but t.t_ty is kept *)
      let ty = conv_ty tenv t.t_ty in
      if ty_equal nt.t_ty ty then nt else
      let lc = Hty.find tenv.specials ty in
      t_app lc.u2t [nt] ty
  | Tif (f, t1, t2) ->
      t_if (fnF vm f) (fnT vm t1) (fnT vm t2)
  | Tlet (t1, b) ->
      let u,t2 = t_open_bound b in
      let u' = conv_vs tenv u in
      let t1' = fnT vm t1 in
      let t2' = fnT (Mvs.add u (t_var u') vm) t2 in
      if vs_equal u u' && t_equal t1 t1' && t_equal t2 t2'
      then t else t_let u' t1' t2'
  | Tcase _ | Teps _ | Tbvar _ ->
      Printer.unsupportedTerm t "unsupported term"

and rewrite_fmla tenv vm f =
  let fnT = rewrite_term tenv in
  let fnF = rewrite_fmla tenv in
  match f.f_node with
  | Fapp (ps,tl) when ls_equal ps ps_equ || ls_equal ps ps_neq ->
      f_app ps (List.map (fnT vm) tl)
  | Fapp (ps,tl) ->
      let ps = conv_ls tenv ps in
      let fn ty t = conv_arg tenv ty (fnT vm t) in
      let tl = List.map2 fn ps.ls_args tl in
      f_app ps tl
  | Fquant (q,b) ->
      let vl, tl, f1 = f_open_quant b in
      let add m v = let v' = conv_vs tenv v in Mvs.add v (t_var v') m, v' in
      let vm', vl' = Util.map_fold_left add vm vl in
      let tl' = tr_map (fnT vm') (fnF vm') tl in
      let f1' = fnF vm' f1 in
      if List.for_all2 vs_equal vl vl' && tr_equal tl tl' && f_equal f1 f1'
      then f else f_quant q vl' tl' f1'
  | Flet (t1, b) ->
      let u,f1 = f_open_bound b in
      let u' = conv_vs tenv u in
      let t1' = fnT vm t1 in
      let f1' = fnF (Mvs.add u (t_var u') vm) f1 in
      if vs_equal u u' && t_equal t1 t1' && f_equal f1 f1'
      then f else f_let u' t1' f1'
  | Fcase _ ->
      Printer.unsupportedFmla f "unsupported formula"
  | _ -> f_map (fnT vm) (fnF vm) f

let decl tenv d =
  let fnT = rewrite_term tenv in
  let fnF = rewrite_fmla tenv in
  match d.d_node with
  | Dtype dl ->
      let add acc = function
        | ts, Tabstract when not (is_kept tenv ts) -> acc
        | ts, Tabstract -> List.rev_append (tenv.declare_kept ts) acc
        | _ -> Printer.unsupportedDecl d "use eliminate_algebraic"
      in
      List.rev (List.fold_left add [] dl)
  | Dlogic ll ->
      let conv = function
        | ls, None -> create_logic_decl [conv_ls tenv ls, None]
        | _ -> Printer.unsupportedDecl d "use eliminate_definition"
      in
      List.map conv ll
  | Dind _ ->
      Printer.unsupportedDecl d "use eliminate_inductive"
  | Dprop _ ->
      [decl_map (fnT Mvs.empty) (fnF Mvs.empty) d]

let t = Trans.on_meta meta_kept (fun tds ->
  let s = Sts.add ts_int (Sts.singleton ts_real) in
  let s = Task.find_tagged_ts meta_kept tds s in
  let task, tenv = init_tenv (Some s) in
  Trans.decl (decl tenv) task)

let () = Trans.register_transform "encoding_simple_kept" t

let t_all =
  let task, tenv = init_tenv None in
  Trans.decl (decl tenv) task

let () = Trans.register_transform "encoding_simple_all" t_all

let t_none =
  let s = Sts.add ts_int (Sts.singleton ts_real) in
  let task, tenv = init_tenv (Some s) in
  Trans.decl (decl tenv) task

let () = Trans.register_transform "encoding_simple" t_none

