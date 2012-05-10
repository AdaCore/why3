(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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
open Libencoding

(* polymorphic decoration function *)
let ls_poly_deco =
  let tyvar = ty_var (create_tvsymbol (id_fresh "a")) in
  create_fsymbol (id_fresh "sort") [ty_type;tyvar] tyvar

let decorate tvar t =
  let tty = term_of_ty tvar (t_type t) in
  t_app ls_poly_deco [tty;t] t.t_ty

let findL = Wls.memoize 63 (fun ls ->
  if ls_equal ls ps_equ then ls else
  let tys = ls_ty_freevars ls in
  if Stv.is_empty tys then ls else
  let args = Stv.fold (fun _ l -> ty_type::l) tys ls.ls_args in
  Term.create_lsymbol (id_clone ls.ls_name) args ls.ls_value)

let deco_term kept tvar =
  let rec deco t = match t.t_node with
    | Tvar v ->
        if is_protected_vs kept v
        then t else decorate tvar t
    | Tapp (ls,_) when ls.ls_value <> None && not (is_protected_ls kept ls) ->
        decorate tvar (expl t)
    | Tconst _ ->
        if Sty.mem (t_type t) kept
        then t else decorate tvar t
    | Teps tb ->
        let v,f,close = t_open_bound_cb tb in
        let t = t_eps (close v (deco f)) in
        if is_protected_vs kept v
        then t else decorate tvar t
    | _ -> expl t
  and expl t = match t.t_node with
    | Tlet (t1,tb) ->
        let v,e,close = t_open_bound_cb tb in
        t_let (expl t1) (close v (deco e))
    | Tapp (ls,tl) when not (ls_equal ls ps_equ) ->
        let inst = ls_app_inst ls tl t.t_ty in
        let add _ ty acc = term_of_ty tvar ty :: acc in
        let tl = Mtv.fold add inst (List.map deco tl) in
        t_app (findL ls) tl t.t_ty
    | _ -> t_map deco t
  in
  deco

let ls_inf_type = create_psymbol (id_fresh "infinite") [ty_type]

let deco_decl kept enum phmap d = match d.d_node with
  | Dtype { ts_def = Some _ } -> []
  | Dtype ts when not (Mts.mem ts enum) ->
      let ls = ls_of_ts ts in
      let vs_of_tv v = create_vsymbol (id_clone v.tv_name) ty_type in
      let vl = List.map vs_of_tv ts.ts_args in
      let t = fs_app ls (List.map t_var vl) ty_type in
      let inf_ts =
        let id = id_fresh ("Inf_ts_" ^ ts.ts_name.id_string) in
        let f = t_forall_close vl [] (ps_app ls_inf_type [t]) in
        create_prop_decl Paxiom (create_prsymbol id) f in
      let sort_id =
        let id = id_fresh ("Sort_id_" ^ ts.ts_name.id_string) in
        let ty_arg = ty_var (create_tvsymbol (id_fresh "a")) in
        let vs_arg = create_vsymbol (id_fresh "x") ty_arg in
        let t_arg = t_var vs_arg in
        let t = fs_app ls_poly_deco [t; t_arg] ty_arg in
        let f = t_forall_close (vs_arg::vl) [] (t_equ t t_arg) in
        create_prop_decl Paxiom (create_prsymbol id) f in
      [d; lsdecl_of_ts ts; inf_ts; sort_id]
  | Dtype ts ->
      let ls = ls_of_ts ts in
      let vs_of_tv v = create_vsymbol (id_clone v.tv_name) ty_type in
      let vl = List.map vs_of_tv ts.ts_args in
      let t = fs_app ls (List.map t_var vl) ty_type in
      let phl = try Mts.find ts phmap with Not_found ->
        List.map Util.ffalse ts.ts_args in
      let add ph v l = if ph then l else
        let id = id_fresh ("Inf_ts_" ^ ts.ts_name.id_string) in
        let f = ps_app ls_inf_type [t] in
        let h = ps_app ls_inf_type [t_var v] in
        let f = t_forall_close vl [] (t_implies h f) in
        create_prop_decl Paxiom (create_prsymbol id) f :: l in
      let inf_tss = List.fold_right2 add phl vl [] in
      [d; lsdecl_of_ts ts] @ inf_tss
  | Ddata _ -> Printer.unsupportedDecl d
      "Algebraic and recursively-defined types are \
            not supported, run eliminate_algebraic"
  | Dparam ls ->
      [create_param_decl (findL ls)]
  | Dlogic [ls,ld] when not (Sid.mem ls.ls_name d.d_syms) ->
      let f = t_type_close (deco_term kept) (ls_defn_axiom ld) in
      defn_or_axiom (findL ls) f
  | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively-defined symbols are not supported, run eliminate_recursion"
  | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
  | Dprop (k,pr,f) ->
      [create_prop_decl k pr (t_type_close (deco_term kept) f)]

let d_infinite =
  let pr = create_prsymbol (id_fresh "Infinite_type") in
  let ty_arg = ty_var (create_tvsymbol (id_fresh "a")) in
  let vs_ty = create_vsymbol (id_fresh "t") ty_type in
  let vs_arg = create_vsymbol (id_fresh "x") ty_arg in
  let t_ty = t_var vs_ty and t_arg = t_var vs_arg in
  let t = fs_app ls_poly_deco [t_ty; t_arg] ty_arg in
  let f = t_implies (ps_app ls_inf_type [t_ty]) (t_equ t t_arg) in
  create_prop_decl Paxiom pr (t_forall_close [vs_ty;vs_arg] [] f)

let deco_init =
  let init = Task.add_decl None d_ts_type in
  let init = Task.add_param_decl init ls_poly_deco in
  let init = Task.add_param_decl init ls_inf_type in
  let init = Task.add_param_decl init ps_equ in
  let init = Task.add_decl init d_infinite in
  init

let deco kept =
  Trans.on_tagged_ts Eliminate_algebraic.meta_enum (fun enum ->
  Trans.on_meta Eliminate_algebraic.meta_phantom (fun phlist ->
  let add_ph phmap = function
    | [Theory.MAts ts; Theory.MAint i] ->
        let phmap, pha = try phmap, Mts.find ts phmap with
          | Not_found ->
              let pha = Array.make (List.length ts.ts_args) false in
              Mts.add ts pha phmap, pha
        in
        Array.set pha i true;
        phmap
    | _ -> assert false
  in
  let phmap = List.fold_left add_ph Mts.empty phlist in
  let phmap = Mts.map Array.to_list phmap in
  Trans.decl (deco_decl kept enum phmap) deco_init))

(** Monomorphisation *)

let ls_deco = create_fsymbol (id_fresh "sort") [ty_type;ty_base] ty_base

(* monomorphise a logical symbol *)
let lsmap kept = Wls.memoize 63 (fun ls ->
  if ls_equal ls ls_poly_deco then ls_deco else
  let prot_arg = is_protecting_id ls.ls_name in
  let prot_val = is_protected_id ls.ls_name in
  let neg ty = if prot_arg && Sty.mem ty kept then ty else ty_base in
  let pos ty = if prot_val && Sty.mem ty kept then ty else ty_base in
  let tyl = List.map neg ls.ls_args in
  let tyr = Util.option_map pos ls.ls_value in
  if Util.option_eq ty_equal tyr ls.ls_value
     && List.for_all2 ty_equal tyl ls.ls_args then ls
  else create_lsymbol (id_clone ls.ls_name) tyl tyr)

let mono_init =
  let init = Task.add_ty_decl None ts_base in
  init

let mono kept =
  let kept = Sty.add ty_type kept in
  Trans.decl (d_monomorph kept (lsmap kept)) mono_init

let t = Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
  Trans.compose (deco kept) (mono kept))

let () = Hashtbl.replace Encoding.ft_enco_poly "decoexp" (const t)

