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

open Ident
open Ty
open Term
open Decl
open Theory

let debug = Debug.register_info_flag "encoding"
  ~desc:"Print@ debugging@ messages@ about@ polymorphism@ encoding."

(* meta to tag the protected types *)
let meta_kept = register_meta "encoding:kept" [MTty]
  ~desc:"Specify@ a@ type@ to@ keep@ during@ polymorphism@ encoding."

(* meta to tag the custom base type *)
let meta_base = register_meta_excl "encoding:base" [MTty]
  ~desc:"Specify@ the@ base@ type@ for@ monomorphic@ \
    polymorphism@ encoding@ (`int'@ or@ `real'@ only)."

(* sort symbol of the default base type *)
let ts_base = create_tysymbol (id_fresh "uni") [] NoDef

(* default base type *)
let ty_base = ty_app ts_base []

(* ts_base declaration *)
let d_ts_base = create_ty_decl ts_base

(* sort symbol of (polymorphic) types *)
let ts_type = create_tysymbol (id_fresh "ty") [] NoDef

(* sort of (polymorphic) types *)
let ty_type = ty_app ts_type []

(* ts_type declaration *)
let d_ts_type = create_ty_decl ts_type

(* add type args to the signature of a polymorphic lsymbol *)
let ls_extend = Wls.memoize 63 (fun ls ->
  if ls_equal ls ps_equ then ls else
  let tvs = ls_ty_freevars ls in
  if Stv.is_empty tvs then ls else
  let args = Stv.fold (fun _ l -> ty_type::l) tvs ls.ls_args in
  Term.create_lsymbol (id_clone ls.ls_name) args ls.ls_value)

(* function symbol mapping ty_type^n to ty_type *)
let ls_of_ts = Wts.memoize 63 (fun ts ->
  let args = List.map (Util.const ty_type) ts.ts_args in
  create_fsymbol (id_clone ts.ts_name) args ty_type)

(* convert a type to a term of type ty_type *)
let rec term_of_ty tvmap ty = match ty.ty_node with
  | Tyvar tv ->
      Mtv.find tv tvmap
  | Tyapp (ts,tl) ->
      fs_app (ls_of_ts ts) (List.map (term_of_ty tvmap) tl) ty_type

(* rewrite a closed formula modulo its free typevars *)
let type_close tvs fn f =
  let get_vs tv = create_vsymbol (id_clone tv.tv_name) ty_type in
  let tvm = Mtv.mapi (fun v () -> get_vs v) tvs in
  let vl = Mtv.values tvm in
  let tvm = Mtv.map t_var tvm in
  t_forall_close_simp vl [] (fn tvm f)

let t_type_close fn f =
  let tvs = t_ty_freevars Stv.empty f in
  type_close tvs fn f

(* convert a type declaration to a list of lsymbol declarations *)
let lsdecl_of_ts ts = create_param_decl (ls_of_ts ts)

let ls_of_const_format = Number.({
  long_int_support = true;
  extra_leading_zeros_support = false;
  negative_int_support = Number_unsupported;
  dec_int_support = Number_default;
  hex_int_support = Number_unsupported;
  oct_int_support = Number_unsupported;
  bin_int_support = Number_unsupported;
  def_int_support = Number_unsupported;
  negative_real_support = Number_unsupported;
  dec_real_support = Number_unsupported;
  hex_real_support = Number_unsupported;
  frac_real_support = Number_custom (PrintFracReal ("%s", "%sx%s", "%s_%s"));
  def_real_support = Number_unsupported;
})

(* convert a constant to a functional symbol of type ty_base *)
let ls_of_const =
  Hty.memo 3 (fun ty_base ->
    let cst = Wstdlib.Hstr.memo 63 (fun s ->
      let s = "const_" ^ s in
      create_fsymbol (id_fresh s) [] ty_base) in
    Hterm.memo 63 (fun t ->
      match t.t_node with
      | Tconst c ->
        cst (Pp.string_of_wnl (Number.print ls_of_const_format) c)
      | _ -> assert false))

(* unprotected and unprotecting idents *)

let unprotected_attr = Ident.create_attribute "encoding:unprotected"
let unprotecting_attr = Ident.create_attribute "encoding:unprotecting"

let id_unprotected n = id_fresh ~attrs:(Sattr.singleton unprotected_attr) n
let id_unprotecting n = id_fresh ~attrs:(Sattr.singleton unprotecting_attr) n

let is_protected_id id = not (Sattr.mem unprotected_attr id.id_attrs)
let is_protecting_id id = not (Sattr.mem unprotecting_attr id.id_attrs)

let is_protected_vs kept vs =
  is_protected_id vs.vs_name && Sty.mem vs.vs_ty kept

let is_protected_ls kept ls =
  is_protected_id ls.ls_name && Sty.mem (Opt.get ls.ls_value) kept

(* monomorphise modulo the set of kept types * and an lsymbol map *)

let vs_monomorph ty_base kept vs =
  if ty_equal vs.vs_ty ty_base || is_protected_vs kept vs
  then vs else create_vsymbol (id_clone vs.vs_name) ty_base

let t_monomorph ty_base kept lsmap consts vmap t =
  let rec t_mono vmap t = t_attr_copy t (match t.t_node with
    | Tvar v ->
        Mvs.find v vmap
    | Tconst _ when ty_equal (t_type t) ty_base ||
                    Sty.mem  (t_type t) kept ->
        t
    | Tconst _ ->
        let ls = ls_of_const ty_base t in
        consts := Sls.add ls !consts;
        fs_app ls [] ty_base
    | Tapp (ps,[t1;t2]) when ls_equal ps ps_equ ->
        t_equ (t_mono vmap t1) (t_mono vmap t2)
    | Tapp (ls,tl) ->
        let ls = lsmap ls in
        t_app ls (List.map (t_mono vmap) tl) ls.ls_value
    | Tif (f,t1,t2) ->
        t_if (t_mono vmap f) (t_mono vmap t1) (t_mono vmap t2)
    | Tlet (t1,b) ->
        let u,t2,close = t_open_bound_cb b in
        let v = vs_monomorph ty_base kept u in
        let t2 = t_mono (Mvs.add u (t_var v) vmap) t2 in
        t_let (t_mono vmap t1) (close v t2)
    | Tcase _ ->
        Printer.unsupportedTerm t "no match expressions at this point"
    | Teps b ->
        let u,f,close = t_open_bound_cb b in
        let v = vs_monomorph ty_base kept u in
        let f = t_mono (Mvs.add u (t_var v) vmap) f in
        t_eps (close v f)
    | Tquant (q,b) ->
        let ul,tl,f1,close = t_open_quant_cb b in
        let vl = List.map (vs_monomorph ty_base kept) ul in
        let add acc u v = Mvs.add u (t_var v) acc in
        let vmap = List.fold_left2 add vmap ul vl in
        let tl = tr_map (t_mono vmap) tl in
        t_quant q (close vl tl (t_mono vmap f1))
    | Tbinop (op,f1,f2) ->
        t_binary op (t_mono vmap f1) (t_mono vmap f2)
    | Tnot f1 ->
        t_not (t_mono vmap f1)
    | Ttrue | Tfalse -> t) in
  t_mono vmap t

let d_monomorph ty_base kept lsmap d =
  let consts = ref Sls.empty in
  let t_mono = t_monomorph ty_base kept lsmap consts in
  let dl = match d.d_node with
    | Dtype { ts_def = Alias _ } -> []
    | Dtype ts when not (Sty.exists (ty_s_any (ts_equal ts)) kept) -> []
    | Dtype ts ->
        [create_ty_decl ts]
    | Ddata _ ->
        Printer.unsupportedDecl d "no algebraic types at this point"
    | Dparam ls ->
        let ls = if ls_equal ls ps_equ then ls else lsmap ls in
        [create_param_decl ls]
    | Dlogic ldl ->
        let conv (ls,ld) =
          let ls = if ls_equal ls ps_equ then ls else lsmap ls in
          let ul,e,close = open_ls_defn_cb ld in
          let vl = List.map (vs_monomorph ty_base kept) ul in
          let add acc u v = Mvs.add u (t_var v) acc in
          let vmap = List.fold_left2 add Mvs.empty ul vl in
          close ls vl (t_mono vmap e)
        in
        [create_logic_decl (List.map conv ldl)]
    | Dind (s, idl) ->
        let iconv (pr,f) = pr, t_mono Mvs.empty f in
        let conv (ls,il) = lsmap ls, List.map iconv il in
        [create_ind_decl s (List.map conv idl)]
    | Dprop (k,pr,f) ->
        [create_prop_decl k pr (t_mono Mvs.empty f)]
  in
  let add ls acc = create_param_decl ls :: acc in
  Sls.fold add !consts dl

module OHTyl = Wstdlib.OrderedHashedList(struct
  type t = ty
  let tag = ty_hash
end)

module Mtyl = Extmap.Make(OHTyl)

let ls_inst =
  (* FIXME? Skolem type constants are short-living but
      will stay in lsmap as long as the lsymbol is alive *)
  let lsmap = Wls.memoize 63 (fun _ -> ref Mtyl.empty) in
  fun ls tyl tyv ->
    let m = lsmap ls in
    let l = oty_cons tyl tyv in
    match Mtyl.find_opt l !m with
    | Some ls -> ls
    | None ->
        let nls = create_lsymbol (id_clone ls.ls_name) tyl tyv in
        m := Mtyl.add l nls !m;
        nls

let lsmap ty_base kept = Hls.memo 63 (fun ls ->
  let prot_arg = is_protecting_id ls.ls_name in
  let prot_val = is_protected_id ls.ls_name in
  let neg ty = if prot_arg && Sty.mem ty kept then ty else ty_base in
  let pos ty = if prot_val && Sty.mem ty kept then ty else ty_base in
  let ty_arg = List.map neg ls.ls_args in
  let ty_res = Opt.map pos ls.ls_value in
  if Opt.equal ty_equal ty_res ls.ls_value &&
     List.for_all2 ty_equal ty_arg ls.ls_args then ls
  else ls_inst ls ty_arg ty_res)

(* replace all non-kept types with ty_base *)
let monomorphise_task =
  Trans.on_meta_excl meta_base (fun base ->
  let ty_base, d_ts_base = match base with
    | Some [MAty ({ty_node = Tyapp (ts,[])} as ty)]
      when ts_equal ts ts_int || ts_equal ts ts_real ->
        ty, create_ty_decl ts
    | Some [MAty _] -> Loc.errorm
        "the \"encoding:base\" meta can only apply to `int' or `real'"
    | Some _ -> assert false
    | None -> ty_base, d_ts_base in
  Trans.on_tagged_ty meta_kept (fun kept ->
    let kept = Sty.add ty_type kept in
    let lsmap = lsmap ty_base kept in
    let decl = d_monomorph ty_base kept lsmap in
    Trans.decl decl (Task.add_decl None d_ts_base)))

(* replace type variables in a goal with fresh type constants *)
let ts_of_tv = Htv.memo 63 (fun tv ->
  create_tysymbol (id_clone tv.tv_name) [] NoDef)

let monomorphise_goal = Trans.goal (fun pr f ->
  let stv = t_ty_freevars Stv.empty f in
  if Stv.is_empty stv then [create_prop_decl Pgoal pr f] else
  let mty,ltv = Stv.fold (fun tv (mty,ltv) ->
    let ts = ts_of_tv tv in
    Mtv.add tv (ty_app ts []) mty, ts::ltv) stv (Mtv.empty,[]) in
  let f = t_ty_subst mty Mvs.empty f in
  List.fold_left
    (fun acc ts -> create_ty_decl ts :: acc)
    [create_prop_decl Pgoal pr f] ltv)

(* close by subtype the set of types tagged by meta_kept *)
let close_kept =
  Trans.on_tagged_ty meta_kept (fun kept ->
    let rec add acc ty = ty_fold add (Sty.add ty acc) ty in
    let kept' = Sty.fold (Util.flip add) kept kept in
    if kept == kept' then Trans.identity
    else
      let kept' = Sty.diff kept' kept in
      let fold ty acc = create_meta meta_kept [MAty ty] :: acc in
      Trans.add_tdecls (Sty.fold fold kept' []))

(* reconstruct a definition of an lsymbol or make a defining axiom *)
let defn_or_axiom ls f =
  match Decl.ls_defn_of_axiom f with
    | Some ld -> [create_logic_decl [ld]]
    | None ->
        let nm = ls.ls_name.id_string ^ "_def" in
        let pr = create_prsymbol (id_derive nm ls.ls_name) in
        [create_param_decl ls; create_prop_decl Paxiom pr f]
