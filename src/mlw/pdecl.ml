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
open Ity
open Expr

(** {2 Type declarations} *)

type its_defn = {
  itd_its          : itysymbol;
  itd_fields       : rsymbol list;
  itd_constructors : rsymbol list;
  itd_invariant    : term list;
  itd_witness      : expr list;
}

let mk_itd s f c i w = {
  itd_its = s;
  itd_fields = f;
  itd_constructors = c;
  itd_invariant = i;
  itd_witness = w;
}

let create_alias_decl id args ity =
  mk_itd (create_alias_itysymbol id args ity) [] [] [] []

let create_range_decl id ir =
  mk_itd (create_range_itysymbol id ir) [] [] [] []

let create_float_decl id fp =
  mk_itd (create_float_itysymbol id fp) [] [] [] []

let check_field stv f =
  let loc = f.pv_vs.vs_name.id_loc in
  let ftv = ity_freevars Stv.empty f.pv_ity in
  if not (Stv.subset ftv stv) then Loc.error ?loc
    (UnboundTypeVar (Stv.choose (Stv.diff ftv stv)));
  if not f.pv_ity.ity_pure then Loc.errorm ?loc
    "This field has non-pure type, it cannot be used \
     in a recursive type definition"

let its_recursive s =
  not s.its_nonfree && not s.its_private &&
  not s.its_mutable && not s.its_fragile &&
  s.its_mfields = [] && s.its_regions = [] &&
  s.its_reg_flg = [] && s.its_def = NoDef &&
  List.for_all (fun x -> x.its_frozen &&
    x.its_exposed && not x.its_liable &&
    x.its_fixed && x.its_visible) s.its_arg_flg

let create_semi_constructor id s fdl pjl invl =
  let tvl = List.map ity_var s.its_ts.ts_args in
  let rgl = List.map ity_reg s.its_regions in
  let ity = ity_app s tvl rgl in
  let res = create_vsymbol (id_fresh "result") (ty_of_ity ity) in
  let t = t_var res in
  let mk_q {pv_vs = v} p = t_equ (fs_app (ls_of_rs p) [t] v.vs_ty) (t_var v) in
  let q = create_post res (t_and_simp_l (List.map2 mk_q fdl pjl)) in
  let eff = match ity.ity_node with
    | Ityreg r -> eff_reset eff_empty (Sreg.singleton r)
    | _ -> eff_empty in
  let c = create_cty fdl invl [q] Mxs.empty Mpv.empty eff ity in
  create_rsymbol id c

let create_plain_record_decl ~priv ~mut id args fdl invl witn =
  let exn = Invalid_argument "Pdecl.create_plain_record_decl" in
  let cid = id_fresh ?loc:id.pre_loc ("mk " ^ id.pre_name) in
  let add_fd fds (mut, fd) = Mpv.add_new exn fd mut fds in
  let fds = List.fold_left add_fd Mpv.empty fdl in
  let fdl = List.map snd fdl in
  let s = create_plain_record_itysymbol ~priv ~mut id args fds invl in
  let pjl = List.map (create_projection s) fdl in
  let csl = if priv then [] else if invl <> [] then
    [create_semi_constructor cid s fdl pjl invl] else
    [create_constructor ~constr:1 cid s fdl] in
  if witn <> [] then begin
    List.iter2 (fun fd ({e_loc = loc} as e) ->
      if diverges e.e_effect.eff_oneway then Loc.errorm ?loc
        "This expression may not terminate, it cannot be a witness";
      if partial e.e_effect.eff_oneway then Loc.errorm ?loc
        "This expression may fail, it cannot be a witness";
      if not (eff_pure e.e_effect) then Loc.errorm ?loc
        "This expression has side effects, it cannot be a witness";
      let ety = ty_of_ity e.e_ity and fty = fd.pv_vs.vs_ty in
      Loc.try2 ?loc ty_equal_check ety fty) fdl witn
  end;
  mk_itd s pjl csl invl witn

let create_rec_record_decl s fdl =
  let exn = Invalid_argument "Pdecl.create_rec_record_decl" in
  if not (its_recursive s) then raise exn;
  let id = s.its_ts.ts_name in
  let cid = id_fresh ?loc:id.id_loc ("mk " ^ id.id_string) in
  List.iter (check_field (Stv.of_list s.its_ts.ts_args)) fdl;
  let cs = create_constructor ~constr:1 cid s fdl in
  let pjl = List.map (create_projection s) fdl in
  mk_itd s pjl [cs] [] []

let create_variant_decl exn get_its csl =
  (* named projections are the same in each constructor *)
  let fdl, rest = match csl with
    | (_,fdl)::csl -> fdl, csl | [] -> raise exn in
  let add_pj pjs (p, fd) = if p then Spv.add fd pjs else pjs in
  let get_pjs fdl = List.fold_left add_pj Spv.empty fdl in
  let pjs = get_pjs fdl in
  List.iter (fun (_, fdl) -> let s = get_pjs fdl in
    if not (Spv.equal s pjs) then raise exn) rest;
  (* therefore, we take them from the first constructor *)
  let add_pj (p, fd) pjl = if p then fd::pjl else pjl in
  let pjl = List.fold_right add_pj fdl [] in
  (* we must also check each field of each constructor *)
  let add_fd fds (_, fd) = Spv.add_new exn fd fds in
  let get_fds (_, fdl) = List.fold_left add_fd Spv.empty fdl in
  (* and now we can create the type symbol and the constructors *)
  let s = get_its (List.map get_fds csl) and constr = List.length csl in
  let mk_cs (id, fdl) = create_constructor ~constr id s (List.map snd fdl) in
  mk_itd s (List.map (create_projection s) pjl) (List.map mk_cs csl) [] []

let create_plain_variant_decl id args csl =
  let exn = Invalid_argument "Pdecl.create_plain_variant_decl" in
  create_variant_decl exn (create_plain_variant_itysymbol id args) csl

let create_rec_variant_decl s csl =
  let exn = Invalid_argument "Pdecl.create_rec_variant_decl" in
  if not (its_recursive s) then raise exn;
  let stv = Stv.of_list s.its_ts.ts_args in
  let get_its fdl = List.iter (Spv.iter (check_field stv)) fdl; s in
  create_variant_decl exn get_its csl

(** {2 Module declarations} *)

type pdecl = {
  pd_node : pdecl_node;
  pd_pure : Decl.decl list;
  pd_meta : meta_decl list;
  pd_syms : Sid.t;
  pd_news : Sid.t;
  pd_tag  : int;
}

and pdecl_node =
  | PDtype of its_defn list
  | PDlet  of let_defn
  | PDexn  of xsymbol
  | PDpure

and meta_decl = Theory.meta * Theory.meta_arg list

let pd_equal : pdecl -> pdecl -> bool = (==)

let get_news node pure =
  let news_id news id = Sid.add_new (ClashIdent id) id news in
  let news_rs news s = news_id news s.rs_name in
  let news = match node with
    | PDtype dl ->
        let news_itd news d =
          let news = news_id news d.itd_its.its_ts.ts_name in
          let news = List.fold_left news_rs news d.itd_fields in
          List.fold_left news_rs news d.itd_constructors in
        List.fold_left news_itd Sid.empty dl
    | PDlet (LDvar (v,_)) -> news_id Sid.empty v.pv_vs.vs_name
    | PDlet (LDsym (s,_)) -> news_id Sid.empty s.rs_name
    | PDlet (LDrec rdl) ->
        let news_rd news d = news_id news d.rec_sym.rs_name in
        List.fold_left news_rd Sid.empty rdl
    | PDexn xs -> news_id Sid.empty xs.xs_name
    | PDpure -> Sid.empty in
  let news_pure news d = Sid.union news d.d_news in
  List.fold_left news_pure news pure

let get_syms node pure =
  let syms_ts syms s = Sid.add s.ts_name syms in
  let syms_ls syms s = Sid.add s.ls_name syms in
  let syms_ty syms ty = ty_s_fold syms_ts syms ty in
  let syms_term syms t = t_s_fold syms_ty syms_ls syms t in
  let syms_tl syms tl = List.fold_left syms_term syms tl in
  let syms_pure syms d = Sid.union syms d.d_syms in
  let syms_vari syms (t,r) = Opt.fold syms_ls (syms_term syms t) r in
  let syms_varl syms varl = List.fold_left syms_vari syms varl in
  let syms = List.fold_left syms_pure Sid.empty pure in
  let syms_its syms s = Sid.add s.its_ts.ts_name syms in
  let syms_ity syms ity = ity_s_fold syms_its syms ity in
  let syms_xs xs syms = Sid.add xs.xs_name syms in
  let syms_pv syms v = syms_ity syms v.pv_ity in
  let syms_pvl syms vl = List.fold_left syms_pv syms vl in
  let rec syms_pat syms p = match p.pat_node with
    | Pwild | Pvar _ -> syms
    | Papp (s,pl) ->
        let syms = List.fold_left syms_ty syms s.ls_args in
        List.fold_left syms_pat syms pl
    | Por (p,q) -> syms_pat (syms_pat syms p) q
    | Pas (p,_) -> syms_pat syms p in
  let syms_cty syms c =
    let add_tl syms tl = syms_tl syms tl in
    let add_xq xs ql syms = syms_xs xs (add_tl syms ql) in
    let syms = add_tl (add_tl syms c.cty_pre) c.cty_post in
    let syms = Mxs.fold add_xq c.cty_xpost syms in
    Sxs.fold syms_xs c.cty_effect.eff_raises syms in
  let rec syms_expr syms e = match e.e_node with
    | Evar _ | Econst _ | Eabsurd -> syms
    | Eassert (_,t) | Epure t -> syms_term syms t
    | Eghost e -> syms_expr syms e
    | Eexec (c,_) when c.c_cty.cty_args = [] -> syms_cexp syms c
    | Eexec (c,cty) -> syms_cty (syms_cexp syms c) cty
    | Eassign al ->
        let syms_as syms (v,s,u) =
          syms_pv (syms_pv (Sid.add s.rs_name syms) u) v in
        List.fold_left syms_as syms al
    | Elet (ld,e) ->
        let esms = syms_expr Sid.empty e in
        let esms = match ld with
          | LDvar _ -> esms
          | LDsym (s,_) -> Sid.remove s.rs_name esms
          | LDrec rdl ->
              let del_rd syms rd = Sid.remove rd.rec_sym.rs_name syms in
              List.fold_left del_rd esms rdl in
        syms_let_defn (Sid.union syms esms) ld
    | Eexn (xs, e) ->
        let esms = syms_expr Sid.empty e in
        Sid.union syms (Sid.remove xs.xs_name esms)
    | Efor (v,_,i,invl,e) ->
        syms_pv (syms_pv (syms_tl (syms_expr syms e) invl) i) v
    | Ewhile (d,invl,varl,e) ->
        let syms = syms_varl (syms_expr syms e) varl in
        syms_tl (syms_eity syms d) invl
    | Eif (c,d,e) ->
        syms_expr (syms_expr (syms_eity syms c) d) e
    | Ematch (d,bl,xl) ->
        (* Dexpr handles this, but not Expr, so we set a failsafe *)
        let exhaustive = bl = [] ||
          let v = create_vsymbol (id_fresh "x") (ty_of_ity d.e_ity) in
          let pl = List.map (fun (p,_) -> [p.pp_pat]) bl in
          Pattern.is_exhaustive [t_var v] pl in
        if not exhaustive then
          Loc.errorm ?loc:e.e_loc "Non-exhaustive pattern matching";
        let add_rbranch syms (p,e) =
          syms_pat (syms_expr syms e) p.pp_pat in
        let add_xbranch xs (vl,e) syms =
          syms_xs xs (syms_pvl (syms_expr syms e) vl) in
        Mxs.fold add_xbranch xl
          (List.fold_left add_rbranch (syms_eity syms d) bl)
    | Eraise (xs,e) ->
        syms_xs xs (syms_eity syms e)
  and syms_eity syms e =
    syms_expr (syms_ity syms e.e_ity) e
  and syms_city syms c =
    let syms = syms_cexp syms c in
    let syms = syms_pvl syms c.c_cty.cty_args in
    syms_ity syms c.c_cty.cty_result
  and syms_cexp syms c = match c.c_node with
    | Capp (s,vl) ->
        let syms = syms_cty syms s.rs_cty in
        syms_pvl (Sid.add s.rs_name syms) vl
    | Cpur (s,vl) ->
        syms_pvl (Sid.add s.ls_name syms) vl
    | Cfun e -> syms_cty (syms_expr syms e) c.c_cty
    | Cany -> syms_cty syms c.c_cty
  and syms_let_defn syms = function
    | LDvar (_,e) -> syms_eity syms e
    | LDsym (s,c) ->
        let syms = match s.rs_logic with
          | RLpv _ -> syms_ls (syms_ts syms ts_func) fs_func_app
          | _ -> syms in
        syms_city syms c
    | LDrec rdl ->
        let add_rd syms rd =
          let syms = syms_varl syms rd.rec_varl in
          let syms = match rd.rec_sym.rs_logic with
            | RLpv _ -> syms_ls (syms_ts syms ts_func) fs_func_app
            | _ -> syms in
          syms_city syms rd.rec_fun in
        let dsms = List.fold_left add_rd Sid.empty rdl in
        let add_inner acc rd =
          let acc = Sid.add rd.rec_rsym.rs_name acc in
          match ls_decr_of_rec_defn rd with
          | Some ls -> Sid.add ls.ls_name acc | None -> acc in
        let inners = List.fold_left add_inner Sid.empty rdl in
        Sid.union syms (Sid.diff dsms inners)
  in
  match node with
  | PDtype dl ->
      let syms_itd syms d =
        (* the syms of the invariants are already in [pure] *)
        let syms = type_def_fold syms_ity syms d.itd_its.its_def in
        let add_fd syms s = syms_ity syms s.rs_cty.cty_result in
        let add_cs syms s = syms_pvl syms s.rs_cty.cty_args in
        let syms = List.fold_left add_fd syms d.itd_fields in
        let syms = List.fold_left syms_expr syms d.itd_witness in
        List.fold_left add_cs syms d.itd_constructors in
      List.fold_left syms_itd syms dl
  | PDlet ld ->
      let syms = syms_let_defn syms ld in
      let vars = match ld with
        | LDvar (_,e) -> e.e_effect.eff_reads
        | LDsym (_,c) -> cty_reads c.c_cty
        | LDrec rdl -> List.fold_left (fun s rd ->
            Spv.union s (cty_reads rd.rec_fun.c_cty)) Spv.empty rdl in
      Spv.fold (fun v s -> Sid.add v.pv_vs.vs_name s) vars syms
  | PDexn xs -> syms_ity syms xs.xs_ity
  | PDpure -> syms

let mk_decl_meta = let r = ref 0 in fun meta node pure ->
  { pd_node = node;
    pd_pure = pure;
    pd_meta = meta;
    pd_syms = get_syms node pure;
    pd_news = get_news node pure;
    pd_tag  = (incr r; !r) }

let mk_decl = mk_decl_meta []

let axiom_of_invariant itd =
  let ts = itd.itd_its.its_ts in
  let inv = t_and_simp_l itd.itd_invariant in
  let ty = ty_app ts (List.map ty_var ts.ts_args) in
  let u = create_vsymbol (id_fresh "self") ty in
  let tl = [t_var u] in
  let add_fd sbs s = let pj = ls_of_rs s in
    Mvs.add (fd_of_rs s).pv_vs (t_app pj tl pj.ls_value) sbs in
  let sbs = List.fold_left add_fd Mvs.empty itd.itd_fields in
  let sbs = Mvs.set_inter sbs (t_freevars Mvs.empty inv) in
  let trl = Mvs.fold (fun _ t trl -> [t] :: trl) sbs [] in
  t_forall_close [u] trl (t_subst sbs inv)

let create_type_decl dl =
  if dl = [] then invalid_arg "Pdecl.create_type_decl";
  let conv_itd ({itd_its = s} as itd) =
    let {its_ts = {ts_name = {id_string = nm} as id} as ts} = s in
    match itd.itd_fields, itd.itd_constructors, s.its_def with
    | _, _, Alias _ ->
        mk_decl (PDtype [itd]) [create_ty_decl ts]
    | _, _, Range ir ->
        let pj_id = id_derive (nm ^ "'int") id in
        let pj_ls = create_fsymbol pj_id [ty_app ts []] ty_int in
        let pj_decl = create_param_decl pj_ls in
        (* Create the projection meta for pj_decl *)
        let meta_proj_pj = (Theory.meta_projection, [Theory.MAls pj_ls]) in
        (* create max attribute *)
        let max_id = id_derive (nm ^ "'maxInt") id in
        let max_ls = create_fsymbol max_id [] ty_int  in
        let max_defn = t_const Number.(const_of_big_int ir.ir_upper) ty_int in
        let max_decl = create_logic_decl [make_ls_defn max_ls [] max_defn] in
        (* create min attribute *)
        let min_id = id_derive (nm ^ "'minInt") id in
        let min_ls = create_fsymbol min_id [] ty_int  in
        let min_defn = t_const Number.(const_of_big_int ir.ir_lower) ty_int in
        let min_decl = create_logic_decl [make_ls_defn min_ls [] min_defn] in
        let pure = [create_ty_decl ts; pj_decl; max_decl; min_decl] in
        let meta = Theory.(meta_range, [MAts ts; MAls pj_ls]) in
        mk_decl_meta [meta; meta_proj_pj] (PDtype [itd]) pure
    | _, _, Float ff ->
        let pj_id = id_derive (nm ^ "'real") id in
        let pj_ls = create_fsymbol pj_id [ty_app ts []] ty_real in
        let pj_decl = create_param_decl pj_ls in
        (* Create the projection meta for pj_decl *)
        let meta_proj_pj = (Theory.meta_projection, [Theory.MAls pj_ls]) in
        (* create finiteness predicate *)
        let iF_id = id_derive (nm ^ "'isFinite") id in
        let iF_ls = create_psymbol iF_id [ty_app ts []] in
        let iF_decl = create_param_decl iF_ls in
        (* create exponent digits attribute *)
        let eb_id = id_derive (nm ^ "'eb") id in
        let eb_ls = create_fsymbol eb_id [] ty_int in
        let eb_defn = t_nat_const ff.Number.fp_exponent_digits in
        let eb_decl = create_logic_decl [make_ls_defn eb_ls [] eb_defn] in
        (* create significand digits attribute *)
        let sb_id = id_derive (nm ^ "'sb") id in
        let sb_ls = create_fsymbol sb_id [] ty_int  in
        let sb_defn = t_nat_const ff.Number.fp_significand_digits in
        let sb_decl = create_logic_decl [make_ls_defn sb_ls [] sb_defn] in
        let pure = [create_ty_decl ts; pj_decl; iF_decl; eb_decl; sb_decl] in
        let meta = Theory.(meta_float, [MAts ts; MAls pj_ls; MAls iF_ls]) in
        mk_decl_meta [meta; meta_proj_pj] (PDtype [itd]) pure
    | fl, _, NoDef when itd.itd_invariant <> [] ->
        let inv = axiom_of_invariant itd in
        let pr = create_prsymbol (id_derive (nm ^ "'invariant") id) in
        let ax = create_prop_decl Paxiom pr inv in
        let add_fd s dl = create_param_decl (ls_of_rs s) :: dl in
        let pure = create_ty_decl ts :: List.fold_right add_fd fl [ax] in
        mk_decl (PDtype [itd]) pure
    | fl, [], NoDef ->
        let add_fd s dl = create_param_decl (ls_of_rs s) :: dl in
        let pure = create_ty_decl ts :: List.fold_right add_fd fl [] in
        mk_decl (PDtype [itd]) pure
    | _, _, NoDef ->
        (* we create here a temporary invalid declaration, just
           to have pd_syms for the topological sorting later *)
        mk_decl (PDtype [itd]) []
  in
  let hpd = Hid.create 3 in
  let dl = List.map (fun itd ->
    let id = itd.itd_its.its_ts.ts_name in
    let d = conv_itd itd in
    Hid.add hpd id d;
    id, itd, d) dl in
  let lvl = Hid.create 3 in
  let rec count id = match Hid.find lvl id with
    | n -> n | exception Not_found ->
    begin match Hid.find hpd id with
    | d -> Hid.add lvl id 0;
        let n = Sid.fold (fun id n -> max (count id) n) d.pd_syms 0 in
        let n = n - (n mod 2) + match d.pd_node with
          | PDtype [{itd_constructors = _::_; itd_invariant = []}] -> 1
          | _ -> 2 in
        Hid.replace lvl id n; n
    | exception Not_found -> 0 end in
  let dl = List.map (fun (id,_,_ as d) -> d, count id) dl in
  let rec insert dl d0 = match dl with
    | d::dl when snd d0 < snd d -> d :: insert dl d0
    | dl -> d0::dl in
  let dl = List.fold_left insert [] dl in
  let mk_data pdl ddl ldl = if ddl = [] then pdl else
    mk_decl (PDtype ddl) [create_data_decl ldl] :: pdl in
  let rec mount pdl ddl ldl = function
    | ((_,_,d),l) :: dl when l mod 2 = 0 ->
        mount (d :: mk_data pdl ddl ldl) [] [] dl
    | ((_,d,_),_) :: dl ->
        let add s f = Mpv.add (fd_of_rs f) f s in
        let mf = List.fold_left add Mpv.empty d.itd_fields in
        let get_pj v = Opt.map ls_of_rs (Mpv.find_opt v mf) in
        let get_cs s = ls_of_rs s, List.map get_pj s.rs_cty.cty_args in
        let ld = d.itd_its.its_ts, List.map get_cs d.itd_constructors in
        mount pdl (d :: ddl) (ld :: ldl) dl
    | [] -> mk_data pdl ddl ldl in
  mount [] [] [] dl

(* TODO: share with Eliminate_definition *)
let rec t_insert hd t = match t.t_node with
  | Tif (f1,t2,t3) ->
      t_if f1 (t_insert hd t2) (t_insert hd t3)
  | Tlet (t1,bt) ->
      let v,t2 = t_open_bound bt in
      t_let_close v t1 (t_insert hd t2)
  | Tcase (tl,bl) ->
      t_case tl (List.map (fun b ->
        let pl,t1 = t_open_branch b in
        t_close_branch pl (t_insert hd t1)) bl)
  | _ when hd.t_ty = None -> t_iff_simp hd t
  | _ -> t_equ_simp hd t

let rec t_subst_fmla v t f = t_attr_copy f (match f.t_node with
  | Tapp (ps, [{t_node = Tvar u}; t1])
    when ls_equal ps ps_equ && vs_equal v u && t_v_occurs v t1 = 0 ->
      t_iff_simp t (t_equ_simp t1 t_bool_true)
  | Tvar u when vs_equal u v -> t_if t t_bool_true t_bool_false
  | _ -> t_map (t_subst_fmla v t) f)

let sattr_w_nce_no = Sattr.singleton Theory.attr_w_non_conservative_extension_no

let create_let_decl ld =
  let conv_post t ql =
    let conv q = match t.t_ty with
      | Some _ -> open_post_with t q
      | None -> let v,f = open_post q in
                t_subst_fmla v t f in
    List.map conv ql in
  let attrs = sattr_w_nce_no in
  let cty_axiom id cty f axms =
    if t_equal f t_true then axms else
    (* we do not care about aliases for pure symbols *)
    let add_old o v m = Mvs.add o.pv_vs (t_var v.pv_vs) m in
    let sbs = Mpv.fold add_old cty.cty_oldies Mvs.empty in
    let f = List.fold_right t_implies cty.cty_pre (t_subst sbs f) in
    let args = List.map (fun v -> v.pv_vs) cty.cty_args in
    let f = t_forall_close_simp args [] f in
    let f = t_forall_close (Mvs.keys (t_vars f)) [] f in
    create_prop_decl Paxiom (create_prsymbol id) f :: axms in
  let add_rs sm s ({c_cty = cty} as c) (abst,defn,axms) =
    match s.rs_logic with
    | RLpv _ -> invalid_arg "Pdecl.create_let_decl"
    | RLnone -> abst, defn, axms
    | RLlemma ->
        let f = if ity_equal cty.cty_result ity_unit then
          t_and_simp_l (conv_post t_void cty.cty_post)
        else match cty.cty_post with
          | q::ql ->
              let v, f = open_post q in
              let fl = f :: conv_post (t_var v) ql in
              t_exists_close [v] [] (t_and_simp_l fl)
          | [] -> t_true in
        abst, defn, cty_axiom (id_clone ~attrs s.rs_name) cty f axms
    | RLls ({ls_name = id} as ls) ->
        let vl = List.map (fun v -> v.pv_vs) cty.cty_args in
        let hd = t_app ls (List.map t_var vl) ls.ls_value in
        let f = t_and_simp_l (conv_post hd cty.cty_post) in
        let nm = id.id_string ^ "_spec" in
        let axms = cty_axiom (id_derive ~attrs nm id) cty f axms in
        let c = if Mrs.is_empty sm then c else c_rs_subst sm c in
        begin match c.c_node with
        | Cany | Capp _ | Cpur _ ->
            (* the full spec of c is inherited by the rsymbol and
               so appears in the "_spec" axiom above. Even if this
               spec contains "result = ...", we do not try to extract
               a definition from it. We only produce definitions via
               term_of_expr from a Cfun, and the user must eta-expand
               to obtain one. *)
            create_param_decl ls :: abst, defn, axms
        | Cfun e ->
            begin match term_of_expr ~prop:(ls.ls_value = None) e with
            | Some f when cty.cty_pre = [] ->
                abst, (ls, vl, f) :: defn, axms
            | Some f ->
                let f = t_insert hd f and nm = id.id_string ^ "_def" in
                let axms = cty_axiom (id_derive ~attrs nm id) cty f axms in
                create_param_decl ls :: abst, defn, axms
            | None when cty.cty_post = [] ->
                let axms = match post_of_expr hd e with
                  | Some f ->
                      let nm = id.id_string ^ "_def" in
                      cty_axiom (id_derive ~attrs nm id) cty f axms
                  | None -> axms in
                create_param_decl ls :: abst, defn, axms
            | None ->
                create_param_decl ls :: abst, defn, axms
            end
        end in
  let abst, defn, axms = match ld with
    | LDvar ({pv_vs = {vs_name = {id_loc = loc}}},e) ->
        if not (ity_closed e.e_ity) then
          Loc.errorm ?loc "Top-level variables must have monomorphic type";
        [], [], []
    | LDrec rdl ->
        let add_rd sm d = Mrs.add d.rec_rsym d.rec_sym sm in
        let sm = List.fold_left add_rd Mrs.empty rdl in
        let add_rd d dl = add_rs sm d.rec_sym d.rec_fun dl in
        List.fold_right add_rd rdl ([],[],[])
    | LDsym (s,c) ->
        add_rs Mrs.empty s c ([],[],[]) in
  let defn = if defn = [] then [] else
    let dl = List.map (fun (s,vl,t) -> make_ls_defn s vl t) defn in
    try [create_logic_decl dl] with Decl.NoTerminationProof _ ->
    let abst = List.map (fun (s,_) -> create_param_decl s) dl in
    let mk_ax ({ls_name = id} as s, vl, t) =
      let nm = id.id_string ^ "_def" in
      let pr = create_prsymbol (id_derive ~attrs nm id) in
      let hd = t_app s (List.map t_var vl) t.t_ty in
      let ax = t_forall_close vl [] (t_insert hd t) in
      create_prop_decl Paxiom pr ax in
    abst @ List.map mk_ax defn in
  mk_decl (PDlet ld) (abst @ defn @ axms)

let create_exn_decl xs =
  if not (ity_closed xs.xs_ity) then Loc.errorm ?loc:xs.xs_name.id_loc
    "Top-level exception %a has a polymorphic type" print_xs xs;
  if not xs.xs_ity.ity_pure then Loc.errorm ?loc:xs.xs_name.id_loc
    "The type of top-level exception %a has mutable components" print_xs xs;
  mk_decl (PDexn xs) []

let create_pure_decl d = match d.d_node with
  | Dtype _ | Ddata _ -> invalid_arg "Pdecl.create_pure_decl"
  | Dparam _ | Dlogic _ | Dind _ | Dprop _ -> mk_decl PDpure [d]

(** {2 Built-in decls} *)

open Theory

(* We must keep the builtin modules in sync with the builtin theories.
   Therefore we match the exact contents of th_decls, and crash if it
   is not what we expect. *)

let pd_int, pd_real, pd_equ = match builtin_theory.th_decls with
  | [{td_node = Decl di}; {td_node = Decl dr}; {td_node = Decl de}] ->
      mk_decl (PDtype [mk_itd its_int  [] [] [] []]) [di],
      mk_decl (PDtype [mk_itd its_real [] [] [] []]) [dr],
      mk_decl PDpure [de]
  | _ -> assert false

let pd_func, pd_func_app = match highord_theory.th_decls with
  | [{td_node = Decl df}; {td_node = Decl da}] ->
      mk_decl (PDtype [mk_itd its_func [] [] [] []]) [df],
      mk_decl (PDlet ld_func_app) [da]
  | _ -> assert false

let pd_bool = match bool_theory.th_decls with
  | [{td_node = Decl db}] ->
      mk_decl (PDtype [mk_itd its_bool [] [rs_true; rs_false] [] []]) [db]
  | _ -> assert false

let pd_tuple = Wstdlib.Hint.memo 17 (fun n ->
  match (tuple_theory n).th_decls with
  | [{td_node = Decl dt}] ->
      mk_decl (PDtype [mk_itd (its_tuple n) [] [rs_tuple n] [] []]) [dt]
  | _ -> assert false)

(** {2 Known identifiers} *)

type known_map = pdecl Mid.t

let known_id kn id =
  if not (Mid.mem id kn) then raise (UnknownIdent id)

let merge_known kn1 kn2 =
  let check_known id decl1 decl2 =
    if pd_equal decl1 decl2 then Some decl1
    else raise (RedeclaredIdent id) in
  Mid.union check_known kn1 kn2

let known_add_decl kn0 d =
  let kn = Mid.map (Util.const d) d.pd_news in
  let check id decl0 _ =
    if pd_equal decl0 d
    then raise (KnownIdent id)
    else raise (RedeclaredIdent id) in
  let kn = Mid.union check kn0 kn in
  let unk = Mid.set_diff d.pd_syms kn in
  if Sid.is_empty unk then kn else
    raise (UnknownIdent (Sid.choose unk))

(** {2 Records/algebraics handling} *)

let find_its_defn kn s =
  match (Mid.find s.its_ts.ts_name kn).pd_node with
  | PDtype dl ->
      let rec search = function
        | d::_ when its_equal s d.itd_its -> d
        | _::dl -> search dl
        | [] -> assert false in
      search dl
  | _ -> assert false

(** {2 Pretty-printing} *)

open Format

let print_its_defn fst fmt itd =
  let s = itd.itd_its in
  let print_args pr fmt tl = if tl <> [] then
    fprintf fmt "@ %a" (Pp.print_list Pp.space pr) tl in
  let print_regs pr fmt rl = if rl <> [] then
    fprintf fmt "@ <%a>" (Pp.print_list Pp.comma pr) rl in
  let print_field fmt f = fprintf fmt "%s%s%a%a : %a"
    (if List.exists (pv_equal (fd_of_rs f)) s.its_mfields
      then "mutable " else "") (if rs_ghost f then "ghost " else "")
    print_rs f Pretty.print_id_attrs f.rs_name
    print_ity f.rs_cty.cty_result in
  let is_big ity = match ity.ity_node with
    | Ityreg {reg_args = []; reg_regs = []}
    | Ityapp (_,[],[]) | Ityvar _ -> false
    | Ityapp (s,_,[]) when is_ts_tuple s.its_ts -> false
    | _ -> true in
  let print_proj mf fmt f = match Mpv.find_opt f mf with
    | Some f -> fprintf fmt "@ (%a)" print_field f
    | _ when f.pv_ghost -> fprintf fmt "@ (ghost %a)" print_ity f.pv_ity
    | _ when is_big f.pv_ity -> fprintf fmt "@ (%a)" print_ity f.pv_ity
    | _ -> fprintf fmt "@ %a" print_ity f.pv_ity in
  let print_constr mf fmt c = fprintf fmt "@\n@[<hov 4>| %a%a%a@]"
    print_rs c Pretty.print_id_attrs c.rs_name
    (Pp.print_list Pp.nothing (print_proj mf)) c.rs_cty.cty_args in
  let print_defn fmt () =
    match s.its_def, itd.itd_fields, itd.itd_constructors with
    | Alias ity, _, _ -> fprintf fmt " = %a" print_ity ity
    | Range _ir, _, _ -> fprintf fmt " = <range ...>" (* TODO *)
    | Float _ff, _, _ -> fprintf fmt " = <float ...>" (* TODO *)
    | NoDef, [], [] when not s.its_mutable -> ()
    | NoDef, fl, [] -> fprintf fmt " = private%s { %a }"
        (if s.its_mutable && s.its_mfields = [] then " mutable" else "")
        (Pp.print_list Pp.semi print_field) fl
    | NoDef, fl, [{rs_name = {id_string = n}}]
      when n = "mk " ^ s.its_ts.ts_name.id_string -> fprintf fmt " =%s { %a }"
        (if s.its_mutable && s.its_mfields = [] then " mutable" else "")
        (Pp.print_list Pp.semi print_field) fl
    | NoDef, fl, cl ->
        let add s f = Mpv.add (fd_of_rs f) f s in
        let mf = List.fold_left add Mpv.empty fl in
        fprintf fmt " =%a" (Pp.print_list Pp.nothing (print_constr mf)) cl
  in
  let print_inv fmt f = fprintf fmt
    "@\n@  invariant { %a }" Pretty.print_term f in
  fprintf fmt "@[<hov 2>%s %a%a%a%a%a%a@]"
    (if fst then "type" else "with")
    print_its s
    Pretty.print_id_attrs s.its_ts.ts_name
    (print_args Pretty.print_tv) s.its_ts.ts_args
    (print_regs print_reg) s.its_regions
    print_defn ()
    (Pp.print_list Pp.nothing print_inv) itd.itd_invariant

let print_pdecl fmt d = match d.pd_node with
  | PDtype dl -> Pp.print_list_next Pp.newline print_its_defn fmt dl
  | PDlet ld -> print_let_defn fmt ld
  | PDexn xs -> fprintf fmt
      "@[<hov 2>exception %a%a of@ %a@]"
        print_xs xs Pretty.print_id_attrs xs.xs_name print_ity xs.xs_ity
  | PDpure -> Pp.print_list Pp.newline2 Pretty.print_decl fmt d.pd_pure
