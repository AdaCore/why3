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

(** transformation from polymorphic logic to many-sorted logic *)

(** an implementation of "featherweight tags" encoding t?? from
    Blanchette et al., Encoding monomorphic and polymorphic types,
    TACAS 2013, LNCS 7795, pp. 493–507 *)

open Ident
open Ty
open Term
open Decl
open Libencoding

type info = {
  kept  : Sty.t;            (* ground types to preserve *)
  infts : Sts.t;            (* infinite type constructors *)
  margs : bool list Mts.t;  (* material type arguments *)
  varm  : term Mtv.t;       (* tyvar-to-variable mapping *)
  polar : bool;             (* polarity is known *)
}

let mk_info kept infts margs = {
  kept  = kept;
  infts = infts;
  margs = margs;
  varm  = Mtv.empty;
  polar = true;
}

let is_infinite_ty info ty =
  Eliminate_algebraic.is_infinite_ty info.infts info.margs ty

let fs_sort =
  let tv = ty_var (create_tvsymbol (id_fresh "a")) in
  create_fsymbol (id_fresh "sort") [tv] tv

(* detect if [t] may be equal to a variable in [svs] *)
let rec detect svs t = match t.t_node with
  | Tvar v -> Svs.mem v svs
  | Tapp _ | Tconst _ -> false
  | Tif (_,t1,t2) ->
      detect svs t1 || detect svs t2
  | Tlet (t1, b) ->
      let s = detect svs t1 in
      let u,t2 = t_open_bound b in
      let svs = if s then Svs.add u svs else svs in
      detect svs t2
  | _ -> assert false (* match and epsilon gone, the rest is prop *)

let rec expl_term info svs sign t = match t.t_node with
  | Tapp (ls,tl) when not (ls_equal ls ps_equ) ->
      let tv_to_ty = ls_app_inst ls tl t.t_ty in
      let tl = List.map (expl_term info svs sign) tl in
      let add _ ty tl = term_of_ty info.varm ty :: tl in
      let tl = Mtv.fold add tv_to_ty tl in
      t_attr_copy t (t_app (ls_extend ls) tl t.t_ty)
  | Tapp (ls,[t1;t2])
    when (not info.polar || sign) && ls_equal ls ps_equ ->
      let t1 = if detect svs t1 then t_app fs_sort [t1] t1.t_ty else t1 in
      let t2 = if detect svs t2 then t_app fs_sort [t2] t2.t_ty else t2 in
      let t1 = expl_term info svs sign t1 in
      let t2 = expl_term info svs sign t2 in
      t_attr_copy t (t_equ t1 t2)
  | Tlet (t1, b) ->
      let s = detect svs t1 in
      let u,t2,close = t_open_bound_cb b in
      let t1 = expl_term info svs sign t1 in
      let svs = if s then Svs.add u svs else svs in
      let t2 = expl_term info svs sign t2 in
      t_attr_copy t (t_let t1 (close u t2))
  | Tquant (q, b) ->
      let vl,tl,f1,close = t_open_quant_cb b in
      let add_vs v (f,svs) =
        if is_protected_vs info.kept v then
          f, svs
        else if info.polar && sign = (q = Tforall) then
          f, if is_infinite_ty info v.vs_ty then svs else Svs.add v svs
        else
          let g = t_equ (fs_app fs_sort [t_var v] v.vs_ty) (t_var v) in
          (if q = Tforall then t_implies else t_and) g f, svs
      in
      let f1, svs = List.fold_right add_vs vl (f1,svs) in
      let tl = tr_map (expl_term info svs sign) tl in
      let f1 = expl_term info svs sign f1 in
      t_attr_copy t (t_quant q (close vl tl f1))
  | Tif (f1,t1,t2) when t.t_ty <> None ->
      let f1 = expl_term { info with polar = false } svs sign f1 in
      let t1 = expl_term info svs sign t1 in
      let t2 = expl_term info svs sign t2 in
      t_attr_copy t (t_if f1 t1 t2)
  | _ ->
      t_map_sign (expl_term info svs) sign t

let expl_term info sign varM t =
  expl_term { info with varm = varM } Svs.empty sign t

(** {2 main part} *)

let ls_desc info ls =
  if ls.ls_value = None || is_protected_ls info.kept ls then [] else
  let vl = List.map (create_vsymbol (id_fresh "x")) ls.ls_args in
  let t = t_app ls (List.map t_var vl) ls.ls_value in
  let f = t_forall_close vl [] (t_equ (t_app fs_sort [t] t.t_ty) t) in
  let pr = create_prsymbol (id_fresh (ls.ls_name.id_string ^ "_sort")) in
  [create_prop_decl Paxiom pr (t_type_close (expl_term info true) f)]

let decl info d = match d.d_node with
  | Dtype { ts_def = Alias _ } -> []
  | Dtype ts -> [d; lsdecl_of_ts ts]
  | Ddata _ -> Printer.unsupportedDecl d
      "Algebraic types are not supported, run eliminate_algebraic"
  | Dparam ls ->
      [create_param_decl (ls_extend ls)] @ ls_desc info ls
  | Dlogic [ls,ld] when not (Sid.mem ls.ls_name d.d_syms) ->
      let f = t_type_close (expl_term info true) (ls_defn_axiom ld) in
      defn_or_axiom (ls_extend ls) f @ ls_desc info ls
  | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively-defined symbols are not supported, run eliminate_recursion"
  | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
  | Dprop (k,pr,f) ->
      let sign = (k <> Pgoal) in
      [create_prop_decl k pr (t_type_close (expl_term info sign) f)]

let d_witness =
  let tv = ty_var (create_tvsymbol (id_fresh "a")) in
  let fs_wit = create_fsymbol (id_fresh "witness") [] tv in
  let dummy_info = mk_info Sty.empty Sts.empty Mts.empty in
  decl dummy_info (create_param_decl fs_wit)

let expl_init =
  let init = Task.add_decl None d_ts_type in
  let init = Task.add_param_decl init ps_equ in
  let init = Task.add_param_decl init (ls_extend fs_sort) in
  let init = List.fold_left Task.add_decl init d_witness in
  init

let tags =
  Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
  Trans.on_tagged_ts Eliminate_algebraic.meta_infinite (fun infts ->
  Trans.on_meta Eliminate_algebraic.meta_material (fun matl ->
  let margs = Eliminate_algebraic.get_material_args matl in
  let info = mk_info kept infts margs in
  Trans.decl (decl info) expl_init)))

let () = Wstdlib.Hstr.replace Encoding.ft_enco_poly "tags" (fun _ ->
  Trans.compose tags monomorphise_task)
