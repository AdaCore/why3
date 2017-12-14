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

(*
  - "use (im|ex)port" -> "open"
    but OCaml's open is not transitive, so requires some extra work
    to figure out all the opens

  - if a WhyML module M is extracted to something that is a signature,
    then extract "module type B_sig = ..." (as well as "module B = ...")
*)

(** Abstract syntax of ML *)

open Ident
open Ity
open Ty
open Term

let clean_name fname =
  (* TODO: replace with Filename.remove_extension
   * after migration to OCaml 4.04+ *)
  let remove_extension s =
    try Filename.chop_extension s with Invalid_argument _ -> s in
  let f = Filename.basename fname in (remove_extension f)

let module_name ?fname path t =
  let fname = match fname, path with
    | None, "why3"::_ -> "why3"
    | None, _   -> String.concat "__" path
    | Some f, _ -> clean_name f in
  fname ^ "__" ^ t

module ML = struct
  open Expr
  open Mltree

  let rec get_decl_name = function
    | Dtype itdefl -> List.map (fun {its_name = id} -> id) itdefl
    | Dlet (Lrec rdef) -> List.map (fun {rec_sym = rs} -> rs.rs_name) rdef
    | Dlet (Lvar ({pv_vs={vs_name=id}}, _))
    | Dlet (Lsym ({rs_name=id}, _, _, _))
    | Dlet (Lany ({rs_name=id}, _, _))
    | Dexn ({xs_name=id}, _) -> [id]
    | Dmodule (_, dl) -> List.concat (List.map get_decl_name dl)

  let rec add_known_decl decl k_map id =
    match decl with
    | Dmodule (_, dl) ->
        let add_decl k_map d =
          let idl = get_decl_name d in
          List.fold_left (add_known_decl d) k_map idl in
        List.fold_left add_decl k_map dl
    | _ -> Mid.add id decl k_map

  let rec iter_deps_ty f = function
    | Tvar _ -> ()
    | Tapp (id, ty_l) -> f id; List.iter (iter_deps_ty f) ty_l
    | Ttuple ty_l -> List.iter (iter_deps_ty f) ty_l

  let iter_deps_typedef f = function
    | Ddata constrl ->
        List.iter (fun (_, tyl) -> List.iter (iter_deps_ty f) tyl) constrl
    | Drecord pjl -> List.iter (fun (_, _, ty) -> iter_deps_ty f ty) pjl
    | Dalias ty -> iter_deps_ty f ty

  let iter_deps_its_defn f its_d =
    Opt.iter (iter_deps_typedef f) its_d.its_def

  let iter_deps_args f =
    List.iter (fun (_, ty_arg, _) -> iter_deps_ty f ty_arg)

  let rec iter_deps_xbranch f (xs, _, e) =
    f xs.xs_name;
    iter_deps_expr f e

  and iter_deps_pat_list f patl =
    List.iter (iter_deps_pat f) patl

  and iter_deps_pat f = function
    | Pwild | Pident _ -> ()
    | Papp (ls, patl) ->
        f ls.ls_name;
        iter_deps_pat_list f patl
    | Ptuple patl -> iter_deps_pat_list f patl
    | Por (p1, p2) ->
        iter_deps_pat f p1;
        iter_deps_pat f p2
    | Pas (p, _) -> iter_deps_pat f p

  and iter_deps_expr f e = match e.e_node with
    | Econst _ | Evar _ | Eabsurd | Ehole -> ()
    | Eapp (rs, exprl) ->
        f rs.rs_name; List.iter (iter_deps_expr f) exprl
    | Efun (args, e) ->
        List.iter (fun (_, ty_arg, _) -> iter_deps_ty f ty_arg) args;
        iter_deps_expr f e
    | Elet (Lvar (_, e1), e2) ->
        iter_deps_expr f e1;
        iter_deps_expr f e2
    | Elet (Lsym (_, ty_result, args, e1), e2) ->
        iter_deps_ty f ty_result;
        List.iter (fun (_, ty_arg, _) -> iter_deps_ty f ty_arg) args;
        iter_deps_expr f e1;
        iter_deps_expr f e2
    | Elet (Lany (_, ty_result, args), e2) ->
        iter_deps_ty f ty_result;
        List.iter (fun (_, ty_arg, _) -> iter_deps_ty f ty_arg) args;
        iter_deps_expr f e2
    | Elet ((Lrec rdef), e) ->
        List.iter
          (fun {rec_sym = rs; rec_args = args; rec_exp = e; rec_res = res} ->
             f rs.rs_name; iter_deps_args f args;
             iter_deps_expr f e; iter_deps_ty f res) rdef;
        iter_deps_expr f e
    | Ematch (e, branchl) ->
        iter_deps_expr f e;
        List.iter (fun (p, e) -> iter_deps_pat f p; iter_deps_expr f e) branchl
    | Eif (e1, e2, e3) ->
        iter_deps_expr f e1;
        iter_deps_expr f e2;
        iter_deps_expr f e3
    | Eblock exprl ->
        List.iter (iter_deps_expr f) exprl
    | Ewhile (e1, e2) ->
        iter_deps_expr f e1;
        iter_deps_expr f e2
    | Efor (_, _, _, _, e) ->
        iter_deps_expr f e
    | Eraise (xs, None) ->
        f xs.xs_name
    | Eraise (xs, Some e) ->
        f xs.xs_name;
        iter_deps_expr f e
    | Eexn (_xs, None, e) -> (* FIXME? How come we never do binding here? *)
        iter_deps_expr f e
    | Eexn (_xs, Some ty, e) -> (* FIXME? How come we never do binding here? *)
        iter_deps_ty f ty;
        iter_deps_expr f e
    | Etry (e, xbranchl) ->
        iter_deps_expr f e;
        List.iter (iter_deps_xbranch f) xbranchl
    | Eassign assingl ->
        List.iter (fun (_, rs, _) -> f rs.rs_name) assingl
    | Eignore e -> iter_deps_expr f e

  let rec iter_deps f = function
    | Dtype its_dl ->
        List.iter (iter_deps_its_defn f) its_dl
    | Dlet (Lsym (_rs, ty_result, args, e)) ->
        iter_deps_ty f ty_result;
        iter_deps_args f args;
        iter_deps_expr f e
    | Dlet (Lany (_rs, ty_result, args)) ->
        iter_deps_ty f ty_result;
        iter_deps_args f args
    | Dlet (Lrec rdef) ->
        List.iter
          (fun {rec_sym = rs; rec_args = args; rec_exp = e; rec_res = res} ->
             f rs.rs_name; iter_deps_args f args;
             iter_deps_expr f e; iter_deps_ty f res) rdef
    | Dlet (Lvar (_, e)) -> iter_deps_expr f e
    | Dexn (_, None) -> ()
    | Dexn (_, Some ty) -> iter_deps_ty f ty
    | Dmodule (_, dl) -> List.iter (iter_deps f) dl

  let mk_expr e_node e_ity e_effect e_label =
    { e_node = e_node; e_ity = e_ity; e_effect = e_effect; e_label = e_label; }

  let tunit = Ttuple []

  let ity_unit = I Ity.ity_unit

  let is_unit = function
    | I i -> ity_equal i Ity.ity_unit
    | _ -> false

  let enope = Eblock []

  let mk_hole =
    mk_expr Ehole (I Ity.ity_unit) Ity.eff_empty Slab.empty

  let mk_var id ty ghost = (id, ty, ghost)

  let mk_var_unit () = id_register (id_fresh "_"), tunit, true

  let mk_its_defn id args private_ def =
    { its_name    = id      ; its_args = args;
      its_private = private_; its_def  = def; }

  (* smart constructors *)
  let e_unit =
    mk_expr enope (I Ity.ity_unit) Ity.eff_empty Slab.empty

  let var_defn pv e =
    Lvar (pv, e)

  let sym_defn f ty_res args e =
    Lsym (f, ty_res, args, e)

  let e_let ld e = mk_expr (Elet (ld, e))

  let e_app rs pvl =
    mk_expr (Mltree.Eapp (rs, pvl))

  let e_fun args e = mk_expr (Efun (args, e))

  let e_ignore e =
    if is_unit e.e_ity then e
    else mk_expr (Eignore e) ity_unit e.e_effect e.e_label

  let e_if e1 e2 e3 =
    mk_expr (Mltree.Eif (e1, e2, e3)) e2.e_ity

  let e_while e1 e2 =
    mk_expr (Mltree.Ewhile (e1, e2)) ity_unit

  let e_for pv1 pv2 dir pv3 e1 =
    mk_expr (Mltree.Efor (pv1, pv2, dir, pv3, e1)) ity_unit

  let e_match e bl =
    mk_expr (Mltree.Ematch (e, bl))

  let e_assign al ity eff lbl =
    let rm_ghost (_, rs, _) = not (rs_ghost rs) in
    let al = List.filter rm_ghost al in
    if al = [] then e_unit else mk_expr (Mltree.Eassign al) ity eff lbl

  let e_absurd =
    mk_expr Eabsurd

  let e_seq e1 e2 =
    let e = match e1.e_node, e2.e_node with
      | (Eblock [] | Ehole), e | e, (Eblock [] | Ehole) -> e
      | Eblock e1, Eblock e2 -> Eblock (e1 @ e2)
      | _, Eblock e2 -> Eblock (e1 :: e2)
      | Eblock e1, _ -> Eblock (e1 @ [e2])
      | _ -> Eblock [e1; e2] in
    mk_expr e

end

(** Translation from Mlw to ML *)

module Translate = struct

  open Expr
  open Pmodule
  open Pdecl

  (* useful predicates and transformations *)
  let pv_not_ghost e = not e.pv_ghost

  (* remove ghost components from tuple, using mask *)
  let visible_of_mask m sl = match m with
    | MaskGhost    -> assert false (* FIXME ? *)
    | MaskVisible  -> sl
    | MaskTuple ml ->
        let add_ity acc m ity = if mask_ghost m then acc else ity :: acc in
        if List.length sl < List.length ml then sl (* FIXME ? much likely... *)
        else List.fold_left2 add_ity [] ml sl

  (* types *)
  let rec type_ ty =
    match ty.ty_node with
    | Tyvar tvs ->
        Mltree.Tvar tvs
    | Tyapp (ts, tyl) when is_ts_tuple ts ->
        Mltree.Ttuple (List.map type_ tyl)
    | Tyapp (ts, tyl) ->
        Mltree.Tapp (ts.ts_name, List.map type_ tyl)

  let vsty vs =
    vs.vs_name, type_ vs.vs_ty

  let rec filter_ghost_params p def = function
    | [] -> []
    | pv :: l ->
        if p pv then def pv :: (filter_ghost_params p def l)
        else filter_ghost_params p def l

  let rec filter_out_ghost_rdef = function
    | [] -> []
    | { rec_sym = rs; rec_rsym = rrs } :: l when rs_ghost rs || rs_ghost rrs ->
        filter_out_ghost_rdef l
    | rdef :: l ->
        rdef :: filter_out_ghost_rdef l

  let rec pat m p = match p.pat_node with
    | Pwild ->
        Mltree.Pwild
    | Pvar vs when (restore_pv vs).pv_ghost ->
        Mltree.Pwild
    | Pvar vs ->
        Mltree.Pident vs.vs_name
    | Por (p1, p2) ->
        Mltree.Por (pat m p1, pat m p2)
    | Pas (p, vs) when (restore_pv vs).pv_ghost ->
        pat m p
    | Pas (p, vs) ->
        Mltree.Pas (pat m p, vs.vs_name)
    | Papp (ls, pl) when is_fs_tuple ls ->
        let pl = visible_of_mask m pl in
        begin match pl with
          | [] -> Mltree.Pwild
          | [p] -> pat m p
          | _ -> Mltree.Ptuple (List.map (pat m) pl) end
    | Papp (ls, pl) ->
        let rs = restore_rs ls in
        let args = rs.rs_cty.cty_args in
        let mk acc pv pp = if not pv.pv_ghost then pat m pp :: acc else acc in
        let pat_pl = List.fold_left2 mk [] args pl in
        Mltree.Papp (ls, List.rev pat_pl)

  (** programs *)

  let pv_name pv = pv.pv_vs.vs_name

  (* individual types *)
  let mlty_of_ity mask t =
    let rec loop t = match t.ity_node with
      | _ when mask_equal mask MaskGhost -> ML.tunit
      | Ityvar tvs ->
          Mltree.Tvar tvs
      | Ityapp ({its_ts = ts}, itl, _) when is_ts_tuple ts ->
          let itl = visible_of_mask mask itl in
          Mltree.Ttuple (List.map loop itl)
      | Ityapp ({its_ts = ts}, itl, _) ->
          Mltree.Tapp (ts.ts_name, List.map loop itl)
      | Ityreg {reg_its = its; reg_args = args} ->
          let args = List.map loop args in
          Mltree.Tapp (its.its_ts.ts_name, args) in
    loop t

  let ty_int = mlty_of_ity MaskVisible ity_int

  let pvty pv =
    if pv.pv_ghost then ML.mk_var (pv_name pv) ML.tunit true
    else let (vs, vs_ty) = vsty pv.pv_vs in
      ML.mk_var vs vs_ty false

  let for_direction = function
    | To -> Mltree.To
    | DownTo -> Mltree.DownTo

  let isconstructor info rs =
    match Mid.find_opt rs.rs_name info.Mltree.from_km with
    | Some {pd_node = PDtype its} ->
        let is_constructor its =
          List.exists (rs_equal rs) its.itd_constructors in
        List.exists is_constructor its
    | _ -> false

  let is_singleton_imutable itd =
    let not_g e = not (rs_ghost e) in
    let pjl = itd.itd_fields in
    let mfields = itd.itd_its.its_mfields in
    let pv_equal_field rs = pv_equal (fd_of_rs rs) in
    let get_mutable rs = List.exists (pv_equal_field rs) mfields in
    match filter_ghost_params not_g get_mutable pjl with
    | [is_mutable] -> not is_mutable
    | _ -> false

  let get_record_itd info rs =
    match Mid.find_opt rs.rs_name info.Mltree.from_km with
    | Some {pd_node = PDtype itdl} ->
        let f pjl_constr = List.exists (rs_equal rs) pjl_constr in
        let itd = match rs.rs_field with
          | Some _ -> List.find (fun itd -> f itd.itd_fields) itdl
          | None -> List.find (fun itd -> f itd.itd_constructors) itdl in
        if itd.itd_fields = [] then None else Some itd
    | _ -> None

  let is_optimizable_record_itd itd =
    not itd.itd_its.its_private && is_singleton_imutable itd

  let is_optimizable_record_rs info rs =
    Opt.fold (fun _ -> is_optimizable_record_itd) false (get_record_itd info rs)

  let is_empty_record_itd itd =
    let is_ghost rs = rs_ghost rs in
    List.for_all is_ghost itd.itd_fields

  let is_empty_record info rs =
    Opt.fold (fun _ -> is_empty_record_itd) false (get_record_itd info rs)

  let mk_eta_expansion rs pvl ({cty_args = ca; cty_effect = ce} as c) =
    (* FIXME : effects and types of the expression in this situation *)
    let args_f =
      let def pv =
        (pv_name pv, mlty_of_ity (mask_of_pv pv) pv.pv_ity, pv.pv_ghost) in
      filter_ghost_params pv_not_ghost def ca in
    let args =
      let def pv =
        ML.mk_expr (Mltree.Evar pv) (Mltree.I pv.pv_ity) eff_empty Slab.empty in
      let args = filter_ghost_params pv_not_ghost def pvl in
      let extra_args = List.map def ca in args @ extra_args in
    let eapp = ML.mk_expr (Mltree.Eapp (rs, args)) (Mltree.C c) ce Slab.empty in
    ML.mk_expr (Mltree.Efun (args_f, eapp)) (Mltree.C c) ce Slab.empty

  (* function arguments *)
  let filter_params args =
    let args = List.map pvty args in
    let p (_, _, is_ghost) = not is_ghost in
    List.filter p args

  let params = function
    | []   -> []
    | args -> let args = filter_params args in
        if args = [] then [ML.mk_var_unit ()] else args

  let filter_params_cty p def pvl cty_args =
    let rec loop = function
      | [], _ -> []
      | pv :: l1, arg :: l2 ->
          if p pv && p arg then def pv :: loop (l1, l2) else loop (l1, l2)
      | _ -> assert false
    in loop (pvl, cty_args)

  let app pvl cty_args =
    let def pv =
      ML.mk_expr (Mltree.Evar pv) (Mltree.I pv.pv_ity) eff_empty Slab.empty in
    filter_params_cty pv_not_ghost def pvl cty_args

  (* build the set of type variables from functions arguments *)
  let rec add_tvar acc = function
    | Mltree.Tvar tv -> Stv.add tv acc
    | Mltree.Tapp (_, tyl) | Mltree.Ttuple tyl ->
        List.fold_left add_tvar acc tyl

  let exp_of_mask e = function
    | MaskGhost   -> e_void
    | MaskVisible -> e
    (* | MaskTuple l -> match e with *)
    (*   | Capp (rs, pvl) -> assert (is_rs_tuple rs); *)
    (*       let rec add_exp acc pv = begin function *)
    (*         | MaskGhost   -> acc *)
    (*         | MaskVisible -> pv *)
    (*         | MaskTuple l ->  *)
    (*       end *)
      | _ -> assert false

  (* expressions *)
  let rec expr info svar ({e_effect = eff; e_label = lbl} as e) =
    assert (not (e_ghost e));
    match e.e_node with
    | Econst c ->
        let c = match c with Number.ConstInt c -> c | _ -> assert false in
        ML.mk_expr (Mltree.Econst c) (Mltree.I e.e_ity) eff lbl
    | Evar pv -> ML.mk_expr (Mltree.Evar pv) (Mltree.I e.e_ity) eff lbl
    | Elet (LDvar (_, e1), e2) when e_ghost e1 -> expr info svar e2
    | Elet (LDvar (_, e1), e2) when e_ghost e2 ->
        (* sequences are transformed into [let o = e1 in e2] by A-normal form *)
        (* FIXME? this is only the case when [e1] is effectful ? *)
        assert (ity_equal ity_unit e1.e_ity);
        expr info svar e1
    | Elet (LDvar (pv, e1), e2)
      when pv.pv_ghost || not (Mpv.mem pv e2.e_effect.eff_reads) ->
        if eff_pure e1.e_effect then expr info svar e2
        else let e1 = ML.e_ignore (expr info svar e1) in
          ML.e_seq e1 (expr info svar e2) (Mltree.I e.e_ity) eff lbl
    | Elet (LDvar (pv, e1), e2) ->
        let ld = ML.var_defn pv (expr info svar e1) in
        ML.e_let ld (expr info svar e2) (Mltree.I e.e_ity) eff lbl
    | Elet (LDsym (rs, _), ein) when rs_ghost rs -> expr info svar ein
    | Elet (LDsym (rs, {c_node = Cfun ef; c_cty = cty}), ein) ->
        let args = params cty.cty_args in
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        let ld = ML.sym_defn rs res args (expr info svar ef) in
        ML.e_let ld (expr info svar ein) (Mltree.I e.e_ity) eff lbl
    | Elet (LDsym (rs, {c_node = Capp (rs_app, pvl); c_cty = cty}), ein)
      when isconstructor info rs_app -> (* partial application of constructor *)
        let eta_app = mk_eta_expansion rs_app pvl cty in
        let mk_func pv f = ity_func pv.pv_ity f in
        let func = List.fold_right mk_func cty.cty_args cty.cty_result in
        let res = mlty_of_ity cty.cty_mask func in
        let ld = ML.sym_defn rs res [] eta_app in
        ML.e_let ld (expr info svar ein) (Mltree.I e.e_ity) e.e_effect lbl
    | Elet (LDsym (rsf, {c_node = Capp (rs_app, pvl); c_cty = cty}), ein) ->
        (* partial application *)
        let pvl = app pvl rs_app.rs_cty.cty_args in
        let eff = cty.cty_effect in
        let eapp = ML.e_app rs_app pvl (Mltree.C cty) eff Slab.empty in
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        let ld = ML.sym_defn rsf res (params cty.cty_args) eapp in
        ML.e_let ld (expr info svar ein) (Mltree.I e.e_ity) e.e_effect lbl
    | Elet (LDrec rdefl, ein) ->
        let rdefl = filter_out_ghost_rdef rdefl in
        let def = function
          | { rec_sym = rs1; rec_rsym = rs2;
              rec_fun = {c_node = Cfun ef; c_cty = cty} } ->
              let res = mlty_of_ity rs1.rs_cty.cty_mask rs1.rs_cty.cty_result in
              let args = params cty.cty_args in
              let new_svar =
                let args' = List.map (fun (_, ty, _) -> ty) args in
                let svar  = List.fold_left add_tvar Stv.empty args' in
                add_tvar svar res in
              let new_svar = Stv.diff svar new_svar in
              let ef = expr info (Stv.union svar new_svar) ef in
              { Mltree.rec_sym  = rs1;  Mltree.rec_rsym = rs2;
                Mltree.rec_args = args; Mltree.rec_exp  = ef;
                Mltree.rec_res  = res;  Mltree.rec_svar = new_svar; }
          | _ -> assert false in
        let rdefl = List.map def rdefl in
        if rdefl <> [] then
          let ml_letrec = Mltree.Elet (Mltree.Lrec rdefl, expr info svar ein) in
          ML.mk_expr ml_letrec (Mltree.I e.e_ity) e.e_effect lbl
        else expr info svar ein
    | Eexec ({c_node = Capp (rs, [])}, _) when is_rs_tuple rs -> ML.e_unit
    | Eexec ({c_node = Capp (rs, _)}, _)
      when is_empty_record info rs || rs_ghost rs -> ML.e_unit
    | Eexec ({c_node = Capp (rs, pvl); c_cty = cty}, _)
      when isconstructor info rs && cty.cty_args <> [] ->
        (* partial application of constructors *)
        mk_eta_expansion rs pvl cty
    | Eexec ({c_node = Capp (rs, pvl); _}, _) ->
        let pvl = app pvl rs.rs_cty.cty_args in
        begin match pvl with
          | [pv_expr] when is_optimizable_record_rs info rs -> pv_expr
          | _ -> ML.e_app rs pvl (Mltree.I e.e_ity) eff lbl end
    | Eexec ({c_node = Cfun e; c_cty = {cty_args = []}}, _) ->
        (* abstract block *)
        expr info svar e
    | Eexec ({c_node = Cfun e; c_cty = cty}, _) ->
        ML.e_fun (params cty.cty_args) (expr info svar e)
                 (Mltree.I e.e_ity) eff lbl
    | Eexec ({c_node = Cany}, _) -> (* raise ExtractionAny *)
        ML.mk_hole
    | Eabsurd -> ML.e_absurd (Mltree.I e.e_ity) eff lbl
    | Ecase (e1, bl) when e_ghost e1 ->
        (* if [e1] is ghost but the entire [match-with] expression doesn't,
           it must be the case the first branch is irrefutable *)
        (match bl with [] -> assert false | (_, e) :: _ -> expr info svar e)
    | Ecase (e1, pl) ->
        let pl = List.map (ebranch info svar) pl in
        ML.e_match (expr info svar e1) pl (Mltree.I e.e_ity) eff lbl
    | Eassert _ -> ML.e_unit
    | Eif (e1, e2, e3) when e_ghost e1 ->
        (* if [e1] is ghost but the entire [if-then-else] expression doesn't,
           it must be the case one of the branches is [Eabsurd] *)
        if e2.e_node = Eabsurd then expr info svar e3 else expr info svar e2
    | Eif (e1, e2, e3) when e_ghost e3 ->
        ML.e_if (expr info svar e1) (expr info svar e2) ML.e_unit eff lbl
    | Eif (e1, e2, e3) when e_ghost e2 ->
        ML.e_if (expr info svar e1) ML.e_unit (expr info svar e3) eff lbl
    | Eif (e1, e2, e3) ->
        let e1 = expr info svar e1 in
        let e2 = expr info svar e2 in
        let e3 = expr info svar e3 in
        ML.e_if e1 e2 e3 eff lbl
    | Ewhile (e1, _, _, e2) ->
        ML.e_while (expr info svar e1) (expr info svar e2) eff lbl
    | Efor (pv1, (pv2, dir, pv3), _, _, efor) ->
        let dir = for_direction dir in
        let efor = expr info svar efor in
        ML.e_for pv1 pv2 dir pv3 efor eff lbl
    | Eghost _ -> assert false
    | Eassign al ->
        ML.e_assign al (Mltree.I e.e_ity) eff lbl
    | Epure _ -> assert false
    | Etry (etry, case, pvl_e_map) ->
        assert (not case); (* TODO *)
        let etry = expr info svar etry in
        let bl   =
          let bl_map = Mxs.bindings pvl_e_map in
          List.map (fun (xs, (pvl, e)) -> xs, pvl, expr info svar e) bl_map in
        ML.mk_expr (Mltree.Etry (etry, bl)) (Mltree.I e.e_ity) eff lbl
    | Eraise (xs, ex) ->
        let ex = exp_of_mask ex xs.xs_mask in
        let ex = match expr info svar ex with
          | {Mltree.e_node = Mltree.Eblock []} -> None
          | e -> Some e in
        ML.mk_expr (Mltree.Eraise (xs, ex)) (Mltree.I e.e_ity) eff lbl
    | Eexn (xs, e1) ->
        if mask_ghost e1.e_mask then ML.mk_expr
            (Mltree.Eexn (xs, None, ML.e_unit)) (Mltree.I e.e_ity) eff lbl
        else let e1 = expr info svar e1 in
          let ty = if ity_equal xs.xs_ity ity_unit then None else
              Some (mlty_of_ity xs.xs_mask xs.xs_ity) in
        ML.mk_expr (Mltree.Eexn (xs, ty, e1)) (Mltree.I e.e_ity) eff lbl
    | Elet (LDsym (_, {c_node=(Cany|Cpur (_, _)); _ }), _)
    | Eexec ({c_node=Cpur (_, _); _ }, _) -> ML.mk_hole

  and ebranch info svar ({pp_pat = p; pp_mask = m}, e) =
    (* if the [case] expression is not ghost but there is (at least) one ghost
       branch, then it must be the case that all the branches return [unit]
       and at least one of the non-ghost branches is effectful *)
    if e.e_effect.eff_ghost then (pat m p, ML.e_unit)
    else (pat m p, expr info svar e)

  (* type declarations/definitions *)
  let tdef itd =
    let s = itd.itd_its in
    let ddata_constructs = (* point-free *)
      List.map (fun ({rs_cty = cty} as rs) ->
          rs.rs_name,
          let args = List.filter pv_not_ghost cty.cty_args in
          List.map (fun {pv_vs = vs} -> type_ vs.vs_ty) args)
    in
    let drecord_fields ({rs_cty = cty} as rs) =
      (List.exists (pv_equal (fd_of_rs rs)) s.its_mfields),
      rs.rs_name,
      mlty_of_ity cty.cty_mask cty.cty_result
    in
    let id = s.its_ts.ts_name in
    let is_private = s.its_private in
    let args = s.its_ts.ts_args in
    begin match s.its_def, itd.itd_constructors, itd.itd_fields with
      | NoDef, [], [] ->
          ML.mk_its_defn id args is_private None
      | NoDef, cl, [] ->
          let cl = ddata_constructs cl in
          ML.mk_its_defn id args is_private (Some (Mltree.Ddata cl))
      | NoDef, _, pjl ->
          let p e = not (rs_ghost e) in
          let pjl = filter_ghost_params p drecord_fields pjl in
          begin match pjl with
            | [] -> ML.mk_its_defn id args is_private
                      (Some (Mltree.Dalias ML.tunit))
            | [_, _, ty_pj] when is_optimizable_record_itd itd ->
                ML.mk_its_defn id args is_private (Some (Mltree.Dalias ty_pj))
            | pjl ->
                ML.mk_its_defn id args is_private (Some (Mltree.Drecord pjl))
          end
      | Alias t, _, _ ->
          ML.mk_its_defn id args is_private (* FIXME ? is this a good mask ? *)
            (Some (Mltree.Dalias (mlty_of_ity MaskVisible t)))
      | Range _, [], [] ->
          assert (args = []); (* a range type is not polymorphic *)
          ML.mk_its_defn id [] is_private (Some (Mltree.Dalias ty_int))
      | Range _, _, _ -> assert false (* a range type has no field/constr. *)
      | Float _, _, _ -> assert false (* TODO *)
    end

  (* exception ExtractionVal of rsymbol *)

  let is_val = function
    | Eexec ({c_node = Cany}, _) -> true
    | _ -> false

  let rec fun_expr_of_mask mask e =
    let open Mltree in
    let mk_e e_node = { e with e_node = e_node } in
    (* assert (mask <> MaskGhost); *)
    match e.e_node with
    | Econst _ | Evar _   | Efun _ | Eassign _ | Ewhile _
    | Efor   _ | Eraise _ | Eexn _ | Eabsurd   | Ehole    -> e
    | Eapp (rs, el) when is_rs_tuple rs ->
        begin match visible_of_mask mask el with
          | [] -> ML.e_unit
          | [e] -> e
          | el -> mk_e (Eapp (rs, el)) end
    | Eapp _ -> e
    | Elet (let_def, ein) -> let ein = fun_expr_of_mask mask ein in
        mk_e (Elet (let_def, ein))
    | Eif (e1, e2, e3) ->
        let e2 = fun_expr_of_mask mask e2 in
        let e3 = fun_expr_of_mask mask e3 in
        mk_e (Eif (e1, e2, e3))
    | Ematch (e1, pel) ->
        let mk_pel (p, ee) = (p, fun_expr_of_mask mask ee) in
        mk_e (Ematch (e1, List.map mk_pel pel))
    | Eblock [] -> e
    | Eblock el -> let (e_block, e_last) = Lists.chop_last el in
        let e_last = fun_expr_of_mask mask e_last in
        mk_e (Eblock (e_block @ [e_last]))
    | Etry (e1, xspvel) ->
        let mk_xspvel (xs, pvl, ee) = (xs, pvl, fun_expr_of_mask mask ee) in
        mk_e (Etry (e1, List.map mk_xspvel xspvel))
    | Eignore ee ->
        let ee = fun_expr_of_mask mask ee in
        mk_e (Eignore ee)

  (* pids: identifiers from cloned modules without definitions *)
  let pdecl _pids info pd =
    match pd.pd_node with
    | PDlet (LDsym (rs, _)) when rs_ghost rs ->
        []
    | PDlet (LDsym ({rs_cty = cty} as rs, {c_node = Cany})) ->
        let args = params cty.cty_args in
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        [Mltree.Dlet (Mltree.Lany (rs, res, args))]
    | PDlet (LDsym ({rs_cty = cty} as rs, {c_node = Cfun e}))
      when is_val e.e_node -> (* zero argument functions *)
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        [Mltree.Dlet (Mltree.Lany (rs, res, []))]
    | PDlet (LDsym ({rs_cty = cty} as rs, {c_node = Cfun e})) ->
        let args = params cty.cty_args in
        let res = mlty_of_ity cty.cty_mask cty.cty_result in
        let svar =
          let args' = List.map (fun (_, ty, _) -> ty) args in
          let svar  = List.fold_left add_tvar Stv.empty args' in
          add_tvar svar res in
        let e = expr info svar e in
        let e = fun_expr_of_mask cty.cty_mask e in
        [Mltree.Dlet (Mltree.Lsym (rs, res, args, e))]
    | PDlet (LDrec rl) ->
        let rl = filter_out_ghost_rdef rl in
        let def {rec_fun = e; rec_sym = rs1; rec_rsym = rs2} =
          let e = match e.c_node with Cfun e -> e | _ -> assert false in
          let args = params rs1.rs_cty.cty_args in
          let res  = mlty_of_ity rs1.rs_cty.cty_mask rs1.rs_cty.cty_result in
          let svar =
            let args' = List.map (fun (_, ty, _) -> ty) args in
            let svar  = List.fold_left add_tvar Stv.empty args' in
            add_tvar svar res in
          let e = fun_expr_of_mask rs1.rs_cty.cty_mask (expr info svar e) in
          { Mltree.rec_sym  = rs1;  Mltree.rec_rsym = rs2;
            Mltree.rec_args = args; Mltree.rec_exp  = e;
            Mltree.rec_res  = res;  Mltree.rec_svar = svar; } in
        if rl = [] then [] else [Mltree.Dlet (Mltree.Lrec (List.map def rl))]
    | PDlet (LDsym _) | PDpure | PDlet (LDvar _) ->
        []
    | PDtype itl ->
        let itsd = List.map tdef itl in
        [Mltree.Dtype itsd]
    | PDexn xs ->
        if ity_equal xs.xs_ity ity_unit || xs.xs_mask = MaskGhost then
          [Mltree.Dexn (xs, None)]
        else [Mltree.Dexn (xs, Some (mlty_of_ity xs.xs_mask xs.xs_ity))]

  let pdecl_m m pd =
    let info = { Mltree.from_mod = Some m; Mltree.from_km = m.mod_known; } in
    pdecl Sid.empty info pd

  let abstract_or_alias_type itd =
    itd.itd_fields = [] && itd.itd_constructors = []

  let empty_pdecl pd  = match pd.pd_node with
    | PDlet (LDsym (_, {c_node = Cfun _})) | PDlet (LDrec _) -> false
    | PDexn _ -> false (* FIXME? *)
    | PDtype itl -> List.for_all abstract_or_alias_type itl
    | _ -> true
  let rec empty_munit = function
    | Udecl pd -> empty_pdecl pd
    | Uclone mi -> List.for_all empty_munit mi.mi_mod.mod_units
    | Uscope (_, l) -> List.for_all empty_munit l
    | Uuse _ | Umeta _ -> true

  let is_empty_clone mi =
    Mts.is_empty mi.mi_ty &&
    Mts.is_empty mi.mi_ts &&
    Mls.is_empty mi.mi_ls &&
    Decl.Mpr.is_empty mi.mi_pr &&
    Decl.Mpr.is_empty mi.mi_pk &&
    Mvs.is_empty mi.mi_pv &&
    Mrs.is_empty mi.mi_rs &&
    Mxs.is_empty mi.mi_xs &&
    List.for_all empty_munit mi.mi_mod.mod_units

  let find_params dl =
    let add params = function
      | Uclone mi when is_empty_clone mi -> mi :: params
      | _ -> params in
    List.fold_left add [] dl

  (* unit module declarations *)
  let rec mdecl pids info = function
    | Udecl pd -> pdecl pids info pd
    | Uscope (_, ([Uuse _] | [Uclone _])) -> []
    | Uscope (s, dl) ->
        let dl = List.concat (List.map (mdecl pids info) dl) in
        [Mltree.Dmodule (s, dl)]
    | Uuse _ | Uclone _ | Umeta _ -> []

  let ids_of_params pids mi =
    Mid.fold (fun id _ pids -> Sid.add id pids) mi.mi_mod.mod_known pids

  (* modules *)
  let module_ m =
    let from = { Mltree.from_mod = Some m; Mltree.from_km = m.mod_known; } in
    let params = find_params m.mod_units in
    let pids = List.fold_left ids_of_params Sid.empty params in
    let mod_decl = List.concat (List.map (mdecl pids from) m.mod_units) in
    let add_decl known_map decl = let idl = ML.get_decl_name decl in
      List.fold_left (ML.add_known_decl decl) known_map idl in
    let mod_known = List.fold_left add_decl Mid.empty mod_decl in {
      Mltree.mod_from = from;
      Mltree.mod_decl = mod_decl;
      Mltree.mod_known = mod_known;
    }

end

(** Some transformations *)

module Transform = struct

  open Mltree

  let no_reads_writes_conflict spv spv_mreg =
    let is_not_write {pv_ity = ity} = match ity.ity_node with
      | Ityreg rho -> not (Mreg.mem rho spv_mreg)
      | _ -> true in
    Spv.for_all is_not_write spv

  (* type subst = expr Mpv.t *)

  let mk_list_eb ebl f =
    let mk_acc e (e_acc, s_acc) =
      let e, s = f e in e::e_acc, Spv.union s s_acc in
    List.fold_right mk_acc ebl ([], Spv.empty)

  let rec expr info subst e =
    let mk e_node = { e with e_node = e_node } in
    let add_subst pv e1 e2 = expr info (Mpv.add pv e1 subst) e2 in
    match e.e_node with
    | Evar pv -> begin try Mpv.find pv subst, Spv.singleton pv
        with Not_found -> e, Spv.empty end
    | Elet (Lvar (pv, ({e_effect = eff1} as e1)), ({e_effect = eff2} as e2))
      when Slab.mem Expr.proxy_label pv.pv_vs.vs_name.id_label &&
           eff_pure eff1 &&
           no_reads_writes_conflict eff1.eff_reads eff2.eff_writes ->
        let e1, s1 = expr info subst e1 in
        let e2, s2 = add_subst pv e1 e2 in
        let s_union = Spv.union s1 s2 in
        if Spv.mem pv s2 then e2, s_union (* [pv] was substituted in [e2] *)
        else (* [pv] was not substituted in [e2], e.g [e2] is an [Efun] *)
          mk (Elet (Lvar (pv, e1), e2)), s_union
    | Elet (ld, e) ->
        let e, spv = expr info subst e in
        let e_let, spv_let = let_def info subst ld in
        mk (Elet (e_let, e)), Spv.union spv spv_let
    | Eapp (rs, el) ->
        let e_app, spv = mk_list_eb el (expr info subst) in
        mk (Eapp (rs, e_app)), spv
    | Efun (vl, e) ->
        (* For now, we accept to inline constants and constructors
           with zero arguments inside a [Efun]. *)
        let p _k e = match e.e_node with
          | Econst _ -> true
          | Eapp (rs, []) when Translate.isconstructor info rs -> true
          | _ -> false in
        let restrict_subst = Mpv.filter p subst in
        (* We begin the inlining of proxy variables in an [Efun] with a
           restricted substitution. This keeps some proxy lets, preventing
           undiserable captures inside the [Efun] expression. *)
        let e, spv = expr info restrict_subst e in
        mk (Efun (vl, e)), spv
    | Eif (e1, e2, e3) ->
        let e1, s1 = expr info subst e1 in
        let e2, s2 = expr info subst e2 in
        let e3, s3 = expr info subst e3 in
        mk (Eif (e1, e2, e3)), Spv.union (Spv.union s1 s2) s3
    | Eexn (xs, ty, e1) ->
        let e1, s1 = expr info subst e1 in
        mk (Eexn (xs, ty, e1)), s1
    | Ematch (e, bl) ->
        let e, spv = expr info subst e in
        let e_bl, spv_bl = mk_list_eb bl (branch info subst) in
        mk (Ematch (e, e_bl)), Spv.union spv spv_bl
    | Eblock el ->
        let e_app, spv = mk_list_eb el (expr info subst) in
        mk (Eblock e_app), spv
    | Ewhile (e1, e2) ->
        let e1, s1 = expr info subst e1 in
        let e2, s2 = expr info subst e2 in
        mk (Ewhile (e1, e2)), Spv.union s1 s2
    | Efor (x, pv1, dir, pv2, e) ->
        let e, spv = expr info subst e in
        mk (Efor (x, pv1, dir, pv2, e)), spv
    | Eraise (exn, None) -> mk (Eraise (exn, None)), Spv.empty
    | Eraise (exn, Some e) ->
        let e, spv = expr info subst e in
        mk (Eraise (exn, Some e)), spv
    | Etry (e, bl) ->
        let e, spv = expr info subst e in
        let e_bl, spv_bl = mk_list_eb bl (xbranch info subst) in
        mk (Etry (e, e_bl)), Spv.union spv spv_bl
    | Eassign _al -> (* FIXME : produced superfolous let *)
        (* let assign e (_, _, pv) = mk_let subst pv e in *)
        e, (* List.fold_left assign e al, *) Spv.empty
    | Econst _ | Eabsurd | Ehole -> e, Spv.empty
    | Eignore e ->
        let e, spv = expr info subst e in
        mk (Eignore e), spv

  (* and mk_let subst pv e = *)
  (*   try let e1 = Mpv.find pv subst in *)
  (*     { e with e_node = Elet (Lvar (pv, e1), e) } *)
  (*   with Not_found -> e *)

  and branch info subst (pat, e) =
    let e, spv = expr info subst e in (pat, e), spv
  and xbranch info subst (exn, pvl, e) =
    let e, spv = expr info subst e in (exn, pvl, e), spv

  and let_def info subst = function
    | Lvar (pv, e) ->
        assert (not (Mpv.mem pv subst)); (* no capture *)
        let e, spv = expr info subst e in
        Lvar (pv, e), spv
    | Lsym (rs, res, args, e) ->
        let e, spv = expr info subst e in
        Lsym (rs, res, args, e), spv
    | Lany _ as lany -> lany, Mpv.empty
    | Lrec rl ->
        let rdef, spv = mk_list_eb rl (rdef info subst) in
        Lrec rdef, spv

  and rdef info subst r =
    let rec_exp, spv = expr info subst r.rec_exp in
    { r with rec_exp = rec_exp }, spv

  let rec pdecl info = function
    | Dtype _ | Dexn _ as d -> d
    | Dmodule (id, dl) ->
        let dl = List.map (pdecl info) dl in Dmodule (id, dl)
    | Dlet def ->
        (* for top-level symbols we can forget the set of inlined variables *)
        let e, _ = let_def info Mpv.empty def in Dlet e

  let module_ m =
    let mod_decl = List.map (pdecl m.mod_from) m.mod_decl in
    let add known_map decl =
      let idl = ML.get_decl_name decl in
      List.fold_left (ML.add_known_decl decl) known_map idl in
    let mod_known = List.fold_left add Mid.empty mod_decl in
    { m with mod_decl = mod_decl; mod_known = mod_known }

end
