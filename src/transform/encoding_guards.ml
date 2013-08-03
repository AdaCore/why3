(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** transformation from polymorphic logic to many-sorted logic *)

(** an implementation of "featherweight guards" encoding g?? from
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

let ps_sort =
  let tv = ty_var (create_tvsymbol (id_fresh "a")) in
  create_psymbol (id_fresh "sort") [tv]

(* add type args to the signature of polymorphic symbols *)
let findL = Wls.memoize 63 (fun ls ->
  if ls_equal ls ps_equ then ls else
  let tvs = ls_ty_freevars ls in
  if Stv.is_empty tvs then ls else
  let args = Stv.fold (fun _ l -> ty_type::l) tvs ls.ls_args in
  Term.create_lsymbol (id_clone ls.ls_name) args ls.ls_value)

(* add to [svs] each variable that [t] may be equal to *)
let rec collect svs t = match t.t_node with
  | Tvar v -> Svs.add v svs
  | Tapp _ | Tconst _ -> svs
  | Tif (_,t1,t2) ->
      collect (collect svs t1) t2
  | Tlet (t1, b) ->
      let s = collect Svs.empty t1 in
      let u,t2 = t_open_bound b in
      let svs = collect svs t2 in
      if Svs.mem u svs then Svs.union s (Svs.remove u svs) else svs
  | _ -> assert false (* match and epsilon gone, the rest is prop *)

let rec expl_term info svs sign t = match t.t_node with
  | Tapp (ls,tl) when not (ls_equal ls ps_equ) ->
      let tv_to_ty = ls_app_inst ls tl t.t_ty in
      let tl = List.map (expl_term info svs sign) tl in
      let add _ ty tl = term_of_ty info.varm ty :: tl in
      let tl = Mtv.fold add tv_to_ty tl in
      t_label_copy t (t_app (findL ls) tl t.t_ty)
  | Tapp (ls,[t1;t2])
    when (not info.polar || sign) && ls_equal ls ps_equ ->
      svs := collect (collect !svs t1) t2;
      let t1 = expl_term info svs sign t1 in
      let t2 = expl_term info svs sign t2 in
      t_label_copy t (t_equ t1 t2)
  | Tlet (t1, b) ->
      let s = collect Svs.empty t1 in
      let u,t2,close = t_open_bound_cb b in
      let t1 = expl_term info svs sign t1 in
      let t2 = expl_term info svs sign t2 in
      if Svs.mem u !svs then svs := Svs.union s (Svs.remove u !svs);
      t_label_copy t (t_let t1 (close u t2))
  | Tquant (q, b) ->
      let vl,tl,f1,close = t_open_quant_cb b in
      let tl = tr_map (expl_term info svs sign) tl in
      let f1 = expl_term info svs sign f1 in
      let guard v f =
        let skip = is_protected_vs info.kept v || is_infinite_ty info v.vs_ty
          || (info.polar && sign = (q = Tforall) && not (Svs.mem v !svs)) in
        svs := Svs.remove v !svs;
        if skip then f else
        let g = ps_app ps_sort [t_var v] in
        let g = expl_term info svs sign g in
        (if q = Tforall then t_implies else t_and) g f in
      let f1 = List.fold_right guard vl f1 in
      t_label_copy t (t_quant q (close vl tl f1))
  | Tif (f1,t1,t2) when t.t_ty <> None ->
      let f1 = expl_term { info with polar = false } svs sign f1 in
      let t1 = expl_term info svs sign t1 in
      let t2 = expl_term info svs sign t2 in
      t_label_copy t (t_if f1 t1 t2)
  | _ ->
      t_map_sign (expl_term info svs) sign t

let expl_term info sign varM t =
  expl_term { info with varm = varM } (ref Svs.empty) sign t

(** {2 main part} *)

let ps_inf_ty = create_psymbol (id_fresh "infinite") [ty_type]

let ts_desc info ts =
  if not (Sts.mem ts info.infts || Mts.mem ts info.margs) then [] else
  let vs_of_tv v = create_vsymbol (id_clone v.tv_name) ty_type in
  let vl = List.map vs_of_tv ts.ts_args in
  let id = id_fresh ("Inf_ts_" ^ ts.ts_name.id_string) in
  let add_axiom f = let f = t_forall_close vl [] f in
    create_prop_decl Paxiom (create_prsymbol id) f in
  let t = fs_app (ls_of_ts ts) (List.map t_var vl) ty_type in
  let f = ps_app ps_inf_ty [t] in
  if Sts.mem ts info.infts then [add_axiom f] else
  let add material v l = if not material then l else
    add_axiom (t_implies (ps_app ps_inf_ty [t_var v]) f) :: l in
  List.fold_right2 add (Mts.find ts info.margs) vl []

let ls_desc info ls =
  if ls.ls_value = None || is_protected_ls info.kept ls ||
      is_infinite_ty info (Opt.get ls.ls_value) then [] else
  let vl = List.map (create_vsymbol (id_fresh "x")) ls.ls_args in
  let t = t_app ls (List.map t_var vl) ls.ls_value in
  let f = t_forall_close vl [] (ps_app ps_sort [t]) in
  let pr = create_prsymbol (id_fresh (ls.ls_name.id_string ^ "_sort")) in
  [create_prop_decl Paxiom pr (t_type_close (expl_term info true) f)]

let decl info d = match d.d_node with
  | Dtype { ts_def = Some _ } -> []
  | Dtype ts ->
      [d; lsdecl_of_ts ts] @ ts_desc info ts
  | Ddata _ -> Printer.unsupportedDecl d
      "Algebraic types are not supported, run eliminate_algebraic"
  | Dparam ls ->
      [create_param_decl (findL ls)] @ ls_desc info ls
  | Dlogic [ls,ld] when not (Sid.mem ls.ls_name d.d_syms) ->
      let f = t_type_close (expl_term info true) (ls_defn_axiom ld) in
      defn_or_axiom (findL ls) f @ ls_desc info ls
  | Dlogic _ -> Printer.unsupportedDecl d
      "Recursively-defined symbols are not supported, run eliminate_recursion"
  | Dind _ -> Printer.unsupportedDecl d
      "Inductive predicates are not supported, run eliminate_inductive"
  | Dprop (k,pr,f) ->
      let sign = (k <> Pgoal) in
      [create_prop_decl k pr (t_type_close (expl_term info sign) f)]

let d_infinite =
  let pr = create_prsymbol (id_fresh "Infinite_type") in
  let ty_arg = ty_var (create_tvsymbol (id_fresh "a")) in
  let vs_ty = create_vsymbol (id_fresh "t") ty_type in
  let vs_arg = create_vsymbol (id_fresh "x") ty_arg in
  let t_ty = t_var vs_ty and t_arg = t_var vs_arg in
  let f = ps_app (findL ps_sort) [t_ty; t_arg] in
  let f = t_forall_close [vs_arg] [] f in
  let f = t_implies (ps_app ps_inf_ty [t_ty]) f in
  let f = t_forall_close [vs_ty] [] f in
  create_prop_decl Paxiom pr f

let d_witness =
  let tv = ty_var (create_tvsymbol (id_fresh "a")) in
  let fs_wit = create_fsymbol (id_fresh "witness") [] tv in
  let dummy_info = mk_info Sty.empty Sts.empty Mts.empty in
  decl dummy_info (create_param_decl fs_wit)

let expl_init =
  let init = Task.add_decl None d_ts_type in
  let init = Task.add_param_decl init ps_equ in
  let init = Task.add_param_decl init (findL ps_sort) in
  let init = Task.add_param_decl init ps_inf_ty in
  let init = Task.add_decl init d_infinite in
  let init = List.fold_left Task.add_decl init d_witness in
  init

let explicit info = Trans.decl (decl info) expl_init

(** {2 monomorphise task } *)

let lsmap kept = Wls.memoize 63 (fun ls ->
  let prot_arg = is_protecting_id ls.ls_name in
  let prot_val = is_protected_id ls.ls_name in
  let neg ty = if prot_arg && Sty.mem ty kept then ty else ty_base in
  let pos ty = if prot_val && Sty.mem ty kept then ty else ty_base in
  let ty_arg = List.map neg ls.ls_args in
  let ty_res = Opt.map pos ls.ls_value in
  if Opt.equal ty_equal ty_res ls.ls_value &&
     List.for_all2 ty_equal ty_arg ls.ls_args then ls
  else create_lsymbol (id_clone ls.ls_name) ty_arg ty_res)

let monomorph kept =
  let kept = Sty.add ty_type kept in
  let decl = d_monomorph kept (lsmap kept) in
  Trans.decl decl (Task.add_decl None d_ts_base)

let () = Stdlib.Hstr.replace Encoding.ft_enco_poly "guards" (fun _ ->
  Trans.on_tagged_ty Libencoding.meta_kept (fun kept ->
  Trans.on_tagged_ts Eliminate_algebraic.meta_infinite (fun infts ->
  Trans.on_meta Eliminate_algebraic.meta_material (fun matl ->
  let margs = Eliminate_algebraic.get_material_args matl in
  let info = mk_info kept infts margs in
  Trans.compose (explicit info) (monomorph kept)))))
