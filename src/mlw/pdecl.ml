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
open Ity
open Expr

(** {2 Type declarations} *)

type its_defn = {
  itd_its          : itysymbol;
  itd_fields       : rsymbol list;
  itd_constructors : rsymbol list;
  itd_invariant    : term list;
}

let mk_itd s f c i = {
  itd_its = s;
  itd_fields = f;
  itd_constructors = c;
  itd_invariant = i;
}

let create_alias_decl id args ity =
  mk_itd (create_itysymbol_alias id args ity) [] [] []

let check_field stv f =
  let loc = f.pv_vs.vs_name.id_loc in
  let ftv = ity_freevars Stv.empty f.pv_ity in
  if not (Stv.subset ftv stv) then Loc.error ?loc
    (Ty.UnboundTypeVar (Stv.choose (Stv.diff ftv stv)));
  if not f.pv_ity.ity_pure then Loc.error ?loc
    (Ity.ImpureField f.pv_ity)

let check_invariant stv svs p =
  let ptv = t_ty_freevars Stv.empty p in
  let pvs = t_freevars Mvs.empty p in
  if not (Stv.subset ptv stv) then Loc.error ?loc:p.t_loc
    (Ty.UnboundTypeVar (Stv.choose (Stv.diff ptv stv)));
  if not (Mvs.set_submap pvs svs) then Loc.error ?loc:p.t_loc
    (Decl.UnboundVar (fst (Mvs.choose (Mvs.set_diff pvs svs))))

let check_pure_its s = not s.its_privmut &&
  s.its_mfields = [] && s.its_regions = [] &&
  List.for_all (fun x -> x) s.its_arg_imm &&
  List.for_all (fun x -> x) s.its_arg_exp &&
  List.for_all (fun x -> x) s.its_arg_vis &&
  List.for_all (fun x -> x) s.its_arg_frz &&
  s.its_reg_vis = [] && s.its_reg_frz = [] &&
  s.its_def = NoDef

let create_semi_constructor id s fl pjl invl =
  let ity = ity_app s (List.map ity_var s.its_ts.ts_args) s.its_regions in
  let res = create_vsymbol (id_fresh "result") (ty_of_ity ity) in
  let t = t_var res in
  let get_pj p = match p.rs_logic with RLls s -> s | _ -> assert false in
  let mk_q {pv_vs = v} p = t_equ (fs_app (get_pj p) [t] v.vs_ty) (t_var v) in
  let q = create_post res (t_and_simp_l (List.map2 mk_q fl pjl)) in
  let c = create_cty fl invl [q] Mexn.empty Mpv.empty eff_empty ity in
  create_rsymbol id c

let create_flat_record_decl id args priv mut fldl invl =
  let exn = Invalid_argument "Mdecl.create_flat_record_decl" in
  let cid = id_fresh ?loc:id.pre_loc ("mk " ^ id.pre_name) in
  let add_fd fs (fm,fd) = Mpv.add_new exn fd fm fs in
  let flds = List.fold_left add_fd Mpv.empty fldl in
  let fmut = List.exists fst fldl in
  let fldl = List.map snd fldl in
  let mut = mut || fmut in
  if not priv && fldl = [] then raise exn;
  if not priv && mut && not fmut then raise exn;
  let stv = Stv.of_list args in
  let svs = List.fold_left (fun s v -> Svs.add v.pv_vs s) Svs.empty fldl in
  List.iter (check_invariant stv svs) invl;
  let s = if not mut && (priv || invl <> []) then begin
    (* a type with an invariant must be declared as mutable in order
       to accept mutable subvalues (we need a head region to track the
       values that must be rechecked if a change is made to a subvalue).
       If we have an immutable type with an invariant, then we create
       an opaque type symbol for it, and forbid subregions. *)
    List.iter (check_field stv) fldl;
    create_itysymbol_pure id args
  end else
    create_itysymbol_rich id args (priv && mut) flds in
  let pjl = List.map (create_projection s) fldl in
  let cl = if priv then [] else if invl <> [] then
    [create_semi_constructor cid s fldl pjl invl] else
    [create_constructor ~constr:1 cid s fldl] in
  mk_itd s pjl cl invl

let create_abstract_type_decl id args mut =
  (* = create_flat_record_decl id args true mut [] [] *)
  let s = if mut
    then create_itysymbol_rich id args true Mpv.empty
    else create_itysymbol_pure id args in
  mk_itd s [] [] []

let create_rec_record_decl s fldl =
  if not (check_pure_its s) || fldl = [] then
    invalid_arg "Mdecl.create_rec_record_decl";
  let id = s.its_ts.ts_name in
  let cid = id_fresh ?loc:id.id_loc ("mk " ^ id.id_string) in
  List.iter (check_field (Stv.of_list s.its_ts.ts_args)) fldl;
  let pjl = List.map (create_projection s) fldl in
  let cs = create_constructor ~constr:1 cid s fldl in
  mk_itd s pjl [cs] []

let create_variant_decl get_its cl =
  let exn = Invalid_argument "Mdecl.create_variant_decl" in
  let pjl, fds = match cl with
    | cs::cl ->
        let add_fd (pjs,fds) (pj,f) =
          (if pj then Spv.add f pjs else pjs), Mpv.add_new exn f false fds in
        let get_cs (_,fl) = List.fold_left add_fd (Spv.empty,Mpv.empty) fl in
        let pjs, fds = get_cs cs in
        let add_cs fds cs = let npjs, nfds = get_cs cs in
          if Spv.equal pjs npjs then Mpv.set_union fds nfds else raise exn in
        Spv.elements pjs, List.fold_left add_cs fds cl
    | [] -> raise exn in
  let s = get_its fds and constr = List.length cl in
  let mk_cs (cid,fl) = create_constructor ~constr cid s (List.map snd fl) in
  mk_itd s (List.map (create_projection s) pjl) (List.map mk_cs cl) []

let create_flat_variant_decl id args cl =
  create_variant_decl (fun fds -> create_itysymbol_rich id args false fds) cl

let create_rec_variant_decl s cl =
  if not (check_pure_its s) then invalid_arg "Mdecl.create_rec_variant_decl";
  let stv = Stv.of_list s.its_ts.ts_args in
  let check_field fd _ = check_field stv fd in
  create_variant_decl (fun fds -> Mpv.iter check_field fds; s) cl

(** {2 Module declarations} *)

type pdecl = {
  pd_node : pdecl_node;
  pd_pure : Decl.decl list;
  pd_syms : Sid.t;
  pd_news : Sid.t;
  pd_tag  : int;
}

and pdecl_node =
  | PDtype of its_defn list
  | PDlet  of let_defn
  | PDexn  of xsymbol
  | PDpure

let pd_equal : pdecl -> pdecl -> bool = (==)

let get_news node pure =
  let news_id news id = Sid.add_new (Decl.ClashIdent id) id news in
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
  let news_pure news d = Sid.union news d.Decl.d_news in
  List.fold_left news_pure news pure

let get_syms node pure =
  let syms_ts s ts = Sid.add ts.ts_name s in
  let syms_ls s ls = Sid.add ls.ls_name s in
  let syms_ty s ty = ty_s_fold syms_ts s ty in
  let syms_term s t = t_s_fold syms_ty syms_ls s t in
  let syms_pure syms d = Sid.union syms d.Decl.d_syms in
  let syms_vari syms (t,r) = Opt.fold syms_ls (syms_term syms t) r in
  let syms = List.fold_left syms_pure Sid.empty pure in
  let syms_its syms s = Sid.add s.its_ts.ts_name syms in
  let syms_ity syms ity = ity_s_fold syms_its syms ity in
  let syms_xs xs syms = Sid.add xs.xs_name syms in
  let syms_pv syms v = syms_ity syms v.pv_ity in
  let rec syms_pat syms p = match p.pat_node with
    | Pwild | Pvar _ -> syms
    | Papp (s,pl) ->
        let syms = List.fold_left syms_ty syms s.ls_args in
        List.fold_left syms_pat syms pl
    | Por (p,q) -> syms_pat (syms_pat syms p) q
    | Pas (p,_) -> syms_pat syms p in
  let syms_cty syms c =
    let add_tl syms tl = List.fold_left syms_term syms tl in
    let add_xq xs ql syms = syms_xs xs (add_tl syms ql) in
    let syms = add_tl (add_tl syms c.cty_pre) c.cty_post in
    let syms = Mexn.fold add_xq c.cty_xpost syms in
    Sexn.fold syms_xs c.cty_effect.eff_raises syms in
  let rec syms_expr syms e = match e.e_node with
    | Evar _ | Econst _ | Eabsurd -> syms
    | Eassert (_,t) | Epure t -> syms_term syms t
    | Eexec c -> syms_cexp syms c
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
    | Efor (i,_,invl,e) ->
        syms_pv (List.fold_left syms_term (syms_expr syms e) invl) i
    | Ewhile (d,invl,varl,e) ->
        let syms = List.fold_left syms_vari (syms_expr syms e) varl in
        List.fold_left syms_term (syms_eity syms d) invl
    | Eif (c,d,e) ->
        syms_expr (syms_expr (syms_eity syms c) d) e
    | Ecase (d,bl) ->
        let add_branch syms (p,e) =
          syms_pat (syms_expr syms e) p.pp_pat in
        List.fold_left add_branch (syms_eity syms d) bl
    | Etry (d,xl) ->
        let add_branch syms (xs,v,e) =
          syms_xs xs (syms_pv (syms_expr syms e) v) in
        List.fold_left add_branch (syms_expr syms d) xl
    | Eraise (xs,e) ->
        syms_xs xs (syms_eity syms e)
  and syms_eity syms e =
    syms_expr (syms_ity syms e.e_ity) e
  and syms_city syms c =
    let syms = syms_ity (syms_cexp syms c) c.c_cty.cty_result in
    List.fold_left syms_pv syms c.c_cty.cty_args
  and syms_cexp syms c = match c.c_node with
    | Capp (s,vl) ->
        let syms = List.fold_left syms_pv syms vl in
        syms_cty (Sid.add s.rs_name syms) s.rs_cty
    | Cfun e -> syms_cty (syms_expr syms e) c.c_cty
    | Cany -> syms_cty syms c.c_cty
  and syms_let_defn syms = function
    | LDvar (_,e) -> syms_eity syms e
    | LDsym (s,c) ->
        let syms = match s.rs_logic with
          | RLpv _ -> syms_ls (syms_ts syms ts_func) fs_func_app
          | _ -> syms in
        syms_city syms c
    | LDrec rdl as ld ->
        let add_rd syms rd =
          let syms = List.fold_left syms_vari syms rd.rec_varl in
          let syms = match rd.rec_sym.rs_logic with
            | RLpv _ -> syms_ls (syms_ts syms ts_func) fs_func_app
            | _ -> syms in
          syms_city syms rd.rec_fun in
        let dsms = List.fold_left add_rd Sid.empty rdl in
        let dsms = match ls_decr_of_let_defn ld with
          | Some ls -> Sid.remove ls.ls_name dsms | None -> dsms in
        let del_rd syms rd = Sid.remove rd.rec_rsym.rs_name syms in
        Sid.union syms (List.fold_left del_rd dsms rdl)
  in
  match node with
  | PDtype dl ->
      let syms_itd syms d =
        (* the syms of the invariants are already in [pure] *)
        let syms = type_def_fold syms_ity syms d.itd_its.its_def in
        let add_fd syms s = syms_ity syms s.rs_cty.cty_result in
        let add_cs syms s = List.fold_left syms_pv syms s.rs_cty.cty_args in
        let syms = List.fold_left add_fd syms d.itd_fields in
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

let mk_decl = let r = ref 0 in fun node pure ->
  { pd_node = node; pd_pure = pure;
    pd_syms = get_syms node pure;
    pd_news = get_news node pure;
    pd_tag  = (incr r; !r) }

let create_type_decl dl =
  let ldl = assert false (* TODO *) in
  mk_decl (PDtype dl) ldl

let create_let_decl ld = let _ = PDlet ld in assert false (* TODO *)

let create_exn_decl xs =
  if not (ity_closed xs.xs_ity) then Loc.errorm ?loc:xs.xs_name.id_loc
    "Top-level exception %a has a polymorphic type" print_xs xs;
  if not xs.xs_ity.ity_pure then Loc.errorm ?loc:xs.xs_name.id_loc
    "The type of top-level exception %a has mutable components" print_xs xs;
  mk_decl (PDexn xs) []

let create_pure_decl d = mk_decl PDpure [d]

(** {2 Built-in decls} *)

open Theory

(* We must keep the builtin modules in sync with the builtin theories.
   Therefore we match the exact contents of th_decls, and crash if it
   is not what we expect. *)

let pd_int, pd_real, pd_equ = match builtin_theory.th_decls with
  | [{td_node = Decl di}; {td_node = Decl dr}; {td_node = Decl de}] ->
      mk_decl (PDtype [mk_itd its_int  [] [] []]) [di],
      mk_decl (PDtype [mk_itd its_real [] [] []]) [dr],
      mk_decl PDpure [de]
  | _ -> assert false

let pd_unit = match unit_theory.th_decls with
  | [{td_node = Use _t0}; {td_node = Decl du}] ->
      mk_decl (PDtype [mk_itd its_unit [] [] []]) [du]
  | _ -> assert false

let pd_func, pd_pred, pd_func_app = match highord_theory.th_decls with
  | [{td_node = Use _bo};
     {td_node = Decl df}; {td_node = Decl dp}; {td_node = Decl da}] ->
      mk_decl (PDtype [mk_itd its_func [] [] []]) [df],
      mk_decl (PDtype [mk_itd its_pred [] [] []]) [dp],
      mk_decl (PDlet ld_func_app) [da]
  | _ -> assert false

let pd_bool = match bool_theory.th_decls with
  | [{td_node = Decl db}] ->
      mk_decl (PDtype [mk_itd its_bool [] [rs_true; rs_false] []]) [db]
  | _ -> assert false

let pd_tuple _n = assert false (*TODO*)

(** {2 Known identifiers} *)

type known_map = pdecl Mid.t

let known_id kn id =
  if not (Mid.mem id kn) then raise (Decl.UnknownIdent id)

let merge_known kn1 kn2 =
  let check_known id decl1 decl2 =
    if pd_equal decl1 decl2 then Some decl1
    else raise (Decl.RedeclaredIdent id) in
  Mid.union check_known kn1 kn2

let known_add_decl kn0 d =
  let kn = Mid.map (Util.const d) d.pd_news in
  let check id decl0 _ =
    if pd_equal decl0 d
    then raise (Decl.KnownIdent id)
    else raise (Decl.RedeclaredIdent id) in
  let kn = Mid.union check kn0 kn in
  let unk = Mid.set_diff d.pd_syms kn in
  if Sid.is_empty unk then kn else
    raise (Decl.UnknownIdent (Sid.choose unk))
