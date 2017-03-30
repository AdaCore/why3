(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*
  - suggest a command line to compile the extracted code
    (for instance in a comment)

  - extract file f.mlw into OCaml file f.ml, with sub-modules

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

  type ty =
    | Tvar    of tvsymbol
    | Tapp    of ident * ty list
    | Ttuple  of ty list

  type is_ghost = bool

  type var = ident * ty * is_ghost

  type for_direction = To | DownTo

  type pat =
    | Pwild
    | Pident  of ident
    | Papp    of lsymbol * pat list
    | Ptuple  of pat list
    | Por     of pat * pat
    | Pas     of pat * ident

  type is_rec = bool

  type binop = Band | Bor | Beq

  type ity = I of Ity.ity | C of Ity.cty (* TODO: keep it like this? *)

  type expr = {
    e_node   : expr_node;
    e_ity    : ity;
    e_effect : effect;
    (* TODO: add the set of free variables? *)
  }

  and expr_node =
    | Econst  of Number.integer_constant
    | Evar    of pvsymbol
    | Eapp    of rsymbol * expr list
    | Efun    of var list * expr
    | Elet    of let_def * expr
    | Eif     of expr * expr * expr
    (* | Ecast   of expr * ty *)
    | Eassign of (pvsymbol * rsymbol * pvsymbol) list
    | Ematch  of expr * (pat * expr) list
    | Eblock  of expr list
    | Ewhile  of expr * expr
    (* For loop for Why3's type int *)
    | Efor    of pvsymbol * pvsymbol * for_direction * pvsymbol * expr
    | Eraise  of xsymbol * expr option
    | Etry    of expr * (xsymbol * pvsymbol list * expr) list
    | Eignore of expr
    | Eabsurd
    | Ehole
    (* | Eany *)

  and let_def =
    | Lvar of pvsymbol * expr
    | Lsym of rsymbol * ty * var list * expr
    | Lrec of rdef list

  and rdef = {
    rec_sym  : rsymbol; (* exported *)
    rec_rsym : rsymbol; (* internal *)
    rec_args : var list;
    rec_exp  : expr;
    rec_res  : ty;
  }

  type is_mutable = bool

  type typedef =
    | Ddata     of (ident * ty list) list
    | Drecord   of (is_mutable * ident * ty) list
    | Dalias    of ty

  type its_defn = {
    its_name    : ident;
    its_args    : tvsymbol list;
    its_private : bool;
    its_def     : typedef option;
  }

  type decl =
    | Dtype   of its_defn list
    | Dlet    of let_def
    | Dexn    of xsymbol * ty option
    | Dclone  of ident * decl list
(*
    | Dfunctor of ident * (ident * decl list) list * decl list
*)

  type known_map = decl Mid.t

  type from_module = {
    from_mod: Pmodule.pmodule option;
    from_km : Pdecl.known_map;
  }

  type pmodule = {
    mod_from  : from_module;
    mod_decl  : decl list;
    mod_known : known_map;
  }

  let get_decl_name = function
    | Dtype itdefl -> List.map (fun {its_name = id} -> id) itdefl
    | Dlet (Lrec rdef) -> List.map (fun {rec_sym = rs} -> rs.rs_name) rdef
    | Dlet (Lvar ({pv_vs={vs_name=id}}, _))
    | Dlet (Lsym ({rs_name=id}, _, _, _))
    | Dexn ({xs_name=id}, _) -> [id]
    | Dclone _ -> [] (* FIXME? *)

  let add_known_decl decl k_map id =
    Mid.add id decl k_map

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
    | Dlet (Lrec rdef) ->
      List.iter
        (fun {rec_sym = rs; rec_args = args; rec_exp = e; rec_res = res} ->
           f rs.rs_name; iter_deps_args f args;
           iter_deps_expr f e; iter_deps_ty f res) rdef
    | Dlet (Lvar (_, e)) -> iter_deps_expr f e
    | Dexn (_, None) -> ()
    | Dexn (_, Some ty) -> iter_deps_ty f ty
    | Dclone (_, dl) -> List.iter (iter_deps f) dl

  let mk_expr e_node e_ity e_effect =
    { e_node = e_node; e_ity = e_ity; e_effect = e_effect }

  (* smart constructors *)
  let mk_let_var pv e1 e2 =
    Elet (Lvar (pv, e1), e2)

  let tunit = Ttuple []

  let ity_int  = I Ity.ity_int
  let ity_unit = I Ity.ity_unit

  let is_unit = function
    | I i -> ity_equal i Ity.ity_unit
    | _ -> false

  let enope = Eblock []

  let mk_unit =
    mk_expr enope (I Ity.ity_unit) Ity.eff_empty

  let mk_hole =
    mk_expr Ehole (I Ity.ity_unit) Ity.eff_empty

  let mk_var id ty ghost = (id, ty, ghost)

  let mk_var_unit () = id_register (id_fresh "_"), tunit, true

  let mk_its_defn id args private_ def =
    { its_name    = id      ; its_args = args;
      its_private = private_; its_def  = def; }

  let mk_ignore e =
    if is_unit e.e_ity then e
    else { e_node = Eignore e; e_effect = e.e_effect; e_ity = ity_unit }

  let eseq e1 e2 =
    match e1.e_node, e2.e_node with
    | (Eblock [] | Ehole), e | e, (Eblock [] | Ehole) -> e
    | Eblock e1, Eblock e2 -> Eblock (e1 @ e2)
    | _, Eblock e2 -> Eblock (e1 :: e2)
    | Eblock e1, _ -> Eblock (e1 @ [e2])
    | _ -> Eblock [e1; e2]

end

(** Translation from Mlw to ML *)

module Translate = struct

  open Expr
  open Pmodule
  open Pdecl

  (* useful predicates and transformations *)
  let pv_not_ghost e = not e.pv_ghost

  (* types *)
  let rec type_ ty =
    match ty.ty_node with
    | Tyvar tvs ->
       ML.Tvar tvs
    | Tyapp (ts, tyl) when is_ts_tuple ts ->
       ML.Ttuple (List.map type_ tyl)
    | Tyapp (ts, tyl) ->
       ML.Tapp (ts.ts_name, List.map type_ tyl)

  let vsty vs =
    vs.vs_name, type_ vs.vs_ty

  let type_args = (* point-free *)
    List.map (fun x -> x.tv_name)

  let rec filter_ghost_params p def = function
    | [] -> []
    | pv :: l ->
      if p pv then def pv :: (filter_ghost_params p def l)
      else filter_ghost_params p def l

  let filter2_ghost_params p def al l =
    let rec filter2_ghost_params_cps l k =
      match l with
      | []  -> k []
      | [e] -> k (if p e then [def e] else [al e])
      | e :: r ->
        filter2_ghost_params_cps r
          (fun fr -> k (if p e then (def e) :: fr else fr))
    in
    filter2_ghost_params_cps l (fun x -> x)

  let rec filter_ghost_rdef def = function
    | [] -> []
    | { rec_sym = rs; rec_rsym = rrs } :: l
      when rs_ghost rs || rs_ghost rrs -> filter_ghost_rdef def l
    | rdef :: l -> def rdef :: filter_ghost_rdef def l

  let rec pat p =
    match p.pat_node with
    | Pwild ->
      ML.Pwild
    | Pvar vs when (restore_pv vs).pv_ghost ->
      ML.Pwild
    | Pvar vs ->
      ML.Pident vs.vs_name
    | Por (p1, p2) ->
      ML.Por (pat p1, pat p2)
    | Pas (p, vs) when (restore_pv vs).pv_ghost ->
      pat p
    | Pas (p, vs) ->
      ML.Pas (pat p, vs.vs_name)
    | Papp (ls, pl) when is_fs_tuple ls ->
      ML.Ptuple (List.map pat pl)
    | Papp (ls, pl) ->
      let rs = restore_rs ls in
      let args = rs.rs_cty.cty_args in
      let mk acc pv pp = if not pv.pv_ghost then pat pp :: acc else acc in
      let pat_pl = List.fold_left2 mk [] args pl in
      ML.Papp (ls, List.rev pat_pl)

  (** programs *)

  let pv_name pv = pv.pv_vs.vs_name

  (* individual types *)
  let rec ity t =
    match t.ity_node with
    | Ityvar (tvs, _) ->
      ML.Tvar tvs
    | Ityapp ({its_ts = ts}, itl, _) when is_ts_tuple ts ->
      ML.Ttuple (List.map ity itl)
    | Ityapp ({its_ts = ts}, itl, _) ->
      ML.Tapp (ts.ts_name, List.map ity itl)
    | Ityreg {reg_its = its; reg_args = args} ->
      let args = List.map ity args in
      ML.Tapp (its.its_ts.ts_name, args)

  let pvty pv =
    if pv.pv_ghost then
      ML.mk_var (pv_name pv) ML.tunit true
    else
      let (vs, vs_ty) = vsty pv.pv_vs in
      ML.mk_var vs vs_ty false

  let for_direction = function
    | To -> ML.To
    | DownTo -> ML.DownTo

  let isconstructor info rs =
    match Mid.find_opt rs.rs_name info.ML.from_km with
    | Some {pd_node = PDtype its} ->
      let is_constructor its =
        List.exists (rs_equal rs) its.itd_constructors in
      List.exists is_constructor its
    | _ -> false

  let is_singleton_imutable itd =
    let not_g e = not (rs_ghost e) in
    let pjl = itd.itd_fields in
    let mfields = itd.itd_its.its_mfields in
    let pv_equal_field rs = pv_equal (Opt.get rs.rs_field) in
    let get_mutable rs = List.exists (pv_equal_field rs) mfields in
    match filter_ghost_params not_g get_mutable pjl with
    | [is_mutable] -> not is_mutable
    | _ -> false

  let get_record_itd info rs =
    match Mid.find_opt rs.rs_name info.ML.from_km with
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

  let mk_eta_expansion rsc pvl cty_app =
    (* FIXME : effects and types of the expression in this situation *)
    let args_f =
      let def pv = pv_name pv, ity pv.pv_ity, pv.pv_ghost in
      filter_ghost_params pv_not_ghost def cty_app.cty_args in
    let args =
      let def pv = ML.mk_expr (ML.Evar pv) (ML.I pv.pv_ity) eff_empty in
      let args = filter_ghost_params pv_not_ghost def pvl in
      let extra_args =
        (* FIXME : ghost status in this extra arguments *)
        List.map def cty_app.cty_args in
      args @ extra_args in
    let eapp =
      ML.mk_expr (ML.Eapp (rsc, args)) (ML.C cty_app) cty_app.cty_effect in
    ML.mk_expr (ML.Efun (args_f, eapp)) (ML.C cty_app) cty_app.cty_effect

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
        if p pv && p arg then def pv :: loop (l1, l2)
        else loop (l1, l2)
      | _ -> assert false
    in loop (pvl, cty_args)

  let app pvl cty_args =
    let def pv = ML.mk_expr (ML.Evar pv) (ML.I pv.pv_ity) eff_empty in
    filter_params_cty pv_not_ghost def pvl cty_args

  let mk_for op_b_rs op_a_rs i_pv from_pv to_pv body_expr eff =
    let i_expr, from_expr, to_expr =
      let int_ity = ML.ity_int in let eff_e = eff_empty in
      ML.mk_expr (ML.Evar i_pv)     int_ity eff_e,
      ML.mk_expr (ML.Evar from_pv)  int_ity eff_e,
      ML.mk_expr (ML.Evar to_pv)    int_ity eff_e in
    let for_rs    =
      let for_id  = id_fresh "for_loop_to" in
      let for_cty = create_cty [i_pv] [] [] Mxs.empty
                               Mpv.empty eff ity_unit in
      create_rsymbol for_id for_cty in
    let for_expr =
      let test = ML.mk_expr (ML.Eapp (op_b_rs, [i_expr; to_expr]))
                            (ML.I ity_bool) eff_empty in
      let next_expr =
        let one_const = Number.int_const_dec "1" in
        let one_expr  =
          ML.mk_expr (ML.Econst one_const) ML.ity_int eff_empty in
        let i_op_one = ML.Eapp (op_a_rs, [i_expr; one_expr]) in
        ML.mk_expr i_op_one ML.ity_int eff_empty in
       let rec_call  =
        ML.mk_expr (ML.Eapp (for_rs, [next_expr]))
                    ML.ity_unit eff in
      let seq_expr =
        ML.mk_expr (ML.eseq body_expr rec_call) ML.ity_unit eff in
      ML.mk_expr (ML.Eif (test, seq_expr, ML.mk_unit)) ML.ity_unit eff in
    let ty_int = ity ity_int in
    let for_call_expr   =
      let for_call      = ML.Eapp (for_rs, [from_expr]) in
      ML.mk_expr for_call ML.ity_unit eff in
    let pv_name pv = pv.pv_vs.vs_name in
    let args = [ pv_name  i_pv, ty_int, false ] in
    let for_rec_def = {
      ML.rec_sym  = for_rs; ML.rec_args = args;
      ML.rec_rsym = for_rs; ML.rec_exp  = for_expr;
      ML.rec_res  = ML.tunit;
    } in
    let for_let = ML.Elet (ML.Lrec [for_rec_def], for_call_expr) in
    ML.mk_expr for_let ML.ity_unit eff

  let mk_for_downto info i_pv from_pv to_pv body eff =
    let ge_rs, minus_rs =
      let ns = (Opt.get info.ML.from_mod).mod_export in
      ns_find_rs ns ["Int"; "infix >="], ns_find_rs ns ["Int"; "infix -"] in
    mk_for ge_rs minus_rs i_pv from_pv to_pv body eff

  let mk_for_to info i_pv from_pv to_pv body eff =
    let le_rs, plus_rs =
      let ns = (Opt.get info.ML.from_mod).mod_export in
      ns_find_rs ns ["Int"; "infix <="], ns_find_rs ns ["Int"; "infix +"] in
    mk_for le_rs plus_rs i_pv from_pv to_pv body eff

  exception ExtractionAny

  (* expressions *)
  let rec expr info ({e_effect = eff} as e) =
    assert (not eff.eff_ghost);
    match e.e_node with
    | Econst c ->
      let c = match c with Number.ConstInt c -> c | _ -> assert false in
      ML.mk_expr (ML.Econst c) (ML.I e.e_ity) eff
    | Evar pv ->
      ML.mk_expr (ML.Evar pv) (ML.I e.e_ity) eff
    | Elet (LDvar (_, e1), e2) when e_ghost e1 ->
      expr info e2
    | Elet (LDvar (_, e1), e2) when e_ghost e2 ->
      ML.mk_expr (ML.eseq (expr info e1) ML.mk_unit) ML.ity_unit eff
    | Elet (LDvar (pv, e1), e2)
      when pv.pv_ghost || not (Mpv.mem pv e2.e_effect.eff_reads) ->
      if eff_pure e1.e_effect then expr info e2
      else let e1 = ML.mk_ignore (expr info e1) in
        ML.mk_expr (ML.eseq e1 (expr info e2)) (ML.I e.e_ity) eff
    | Elet (LDvar (pv, e1), e2) ->
      let ml_let = ML.mk_let_var pv (expr info e1) (expr info e2) in
      ML.mk_expr ml_let (ML.I e.e_ity) eff
    | Elet (LDsym (rs, {c_node = Cfun ef; c_cty = cty}), ein) ->
      let args = params cty.cty_args in
      let ef = expr info ef in
      let ein = expr info ein in
      let res = ity cty.cty_result in
      let ml_letrec = ML.Elet (ML.Lsym (rs, res, args, ef), ein) in
      ML.mk_expr ml_letrec (ML.I e.e_ity) eff
    | Elet (LDsym (rsf, {c_node = Capp (rs_app, pvl); c_cty = cty}), ein)
      when isconstructor info rs_app ->
      (* partial application of constructor *)
      let eta_app = mk_eta_expansion rs_app pvl cty in
      let ein = expr info ein in
      let mk_func pv f = ity_func pv.pv_ity f in
      let func = List.fold_right mk_func cty.cty_args cty.cty_result in
      let res = ity func in
      let ml_letrec = ML.Elet (ML.Lsym (rsf, res, [], eta_app), ein) in
      ML.mk_expr ml_letrec (ML.I e.e_ity) e.e_effect
    | Elet (LDsym (rsf, {c_node = Capp (rs_app, pvl); c_cty = cty}), ein) ->
      (* partial application *)
      let pvl = app pvl rs_app.rs_cty.cty_args in
      let eapp =
        ML.mk_expr (ML.Eapp (rs_app, pvl)) (ML.C cty) cty.cty_effect in
      let ein  = expr info ein in
      let res  = ity cty.cty_result in
      let args = params cty.cty_args in
      let ml_letrec = ML.Elet (ML.Lsym (rsf, res, args, eapp), ein) in
      ML.mk_expr ml_letrec (ML.I e.e_ity) e.e_effect
    | Elet (LDrec rdefl, ein) ->
      let ein = expr info ein in
      let rdefl =
        List.map (fun rdef -> match rdef with
          | {rec_sym = rs1; rec_rsym = rs2;
             rec_fun = {c_node = Cfun ef; c_cty = cty}} ->
            let res  = ity rs1.rs_cty.cty_result in
            let args = params cty.cty_args in let ef = expr info ef in
            { ML.rec_sym  = rs1;  ML.rec_rsym = rs2;
              ML.rec_args = args; ML.rec_exp  = ef ; ML.rec_res  = res }
          | _ -> assert false) rdefl
      in
      let ml_letrec = ML.Elet (ML.Lrec rdefl, ein) in
      ML.mk_expr ml_letrec (ML.I e.e_ity) e.e_effect
    | Eexec ({c_node = Capp (rs, [])}, _) when is_rs_tuple rs ->
      ML.mk_unit
    | Eexec ({c_node = Capp (rs, _)}, _) when is_empty_record info rs ->
      ML.mk_unit
    | Eexec ({c_node = Capp (rs, _)}, _) when rs_ghost rs ->
      ML.mk_unit
    | Eexec ({c_node = Capp (rs, pvl); c_cty = cty}, _)
      when isconstructor info rs && cty.cty_args <> [] ->
      (* partial application of constructors *)
      mk_eta_expansion rs pvl cty
    | Eexec ({c_node = Capp (rs, pvl); _}, _) ->
      let pvl = app pvl rs.rs_cty.cty_args in
      begin match pvl with
      | [pv_expr] when is_optimizable_record_rs info rs -> pv_expr
      | _ -> ML.mk_expr (ML.Eapp (rs, pvl)) (ML.I e.e_ity) eff end
    | Eexec ({c_node = Cfun e; c_cty = {cty_args = []}}, _) ->
      (* abstract block *)
      expr info e
    | Eexec ({c_node = Cfun e; c_cty = cty}, _) ->
      let args = params cty.cty_args in
      ML.mk_expr (ML.Efun (args, expr info e)) (ML.I e.e_ity) eff
    | Eexec ({c_node = Cany}, _) -> (* raise ExtractionAny *)
      ML.mk_hole
    | Eabsurd ->
      ML.mk_expr ML.Eabsurd (ML.I e.e_ity) eff
    | Ecase (e1, _) when e_ghost e1 ->
      ML.mk_unit
    | Ecase (e1, pl) ->
      let e1 = expr info e1 in
      let pl = List.map (ebranch info) pl in
      ML.mk_expr (ML.Ematch (e1, pl)) (ML.I e.e_ity) eff
    | Eassert _ -> ML.mk_unit
    | Eif (e1, e2, e3) ->
      let e1 = expr info e1 in
      let e2 = expr info e2 in
      let e3 = expr info e3 in
      ML.mk_expr (ML.Eif (e1, e2, e3)) (ML.I e.e_ity) eff
    | Ewhile (e1, _, _, e2) ->
      let e1 = expr info e1 in
      let e2 = expr info e2 in
      ML.mk_expr (ML.Ewhile (e1, e2)) (ML.I e.e_ity) eff
    | Efor (pv1, (pv2, To, pv3), _, efor) ->
      let efor = expr info efor in
      mk_for_to info pv1 pv2 pv3 efor eff
    | Efor (pv1, (pv2, DownTo, pv3), _, efor) ->
      let efor = expr info efor in
      mk_for_downto info pv1 pv2 pv3 efor eff
    | Eghost _ -> assert false
    | Eassign al ->
      ML.mk_expr (ML.Eassign al) (ML.I e.e_ity) eff
    | Epure _ -> (* assert false (\*TODO*\) *) ML.mk_hole
    | Etry (etry, pvl_e_map) ->
      let etry = expr info etry in
      let bl   =
        let bl_map = Mxs.bindings pvl_e_map in
        List.map (fun (xs, (pvl, e)) -> xs, pvl, expr info e) bl_map in
      ML.mk_expr (ML.Etry (etry, bl)) (ML.I e.e_ity) eff
    | Eraise (xs, ex) ->
      let ex =
        match expr info ex with
        | {ML.e_node = ML.Eblock []} -> None
        | e -> Some e
      in
      ML.mk_expr (ML.Eraise (xs, ex)) (ML.I e.e_ity) eff
    | Elet (LDsym (_, {c_node=(Cany|Cpur (_, _)); _ }), _)
    (*   assert false (\*TODO*\) *)
    | Eexec ({c_node=Cpur (_, _); _ }, _) -> ML.mk_hole
    (*   assert false (\*TODO*\) *)

  and ebranch info ({pp_pat = p}, e) =
    (pat p, expr info e)

  let its_args ts = ts.its_ts.ts_args
  let itd_name td = td.itd_its.its_ts.ts_name

  (* type declarations/definitions *)
  let tdef itd =
    let s = itd.itd_its in
    let ddata_constructs = (* point-free *)
      List.map (fun ({rs_cty = rsc} as rs) ->
          rs.rs_name,
          let args = List.filter pv_not_ghost rsc.cty_args in
          List.map (fun {pv_vs = vs} -> type_ vs.vs_ty) args)
    in
    let drecord_fields ({rs_cty = rsc} as rs) =
      (List.exists (pv_equal (Opt.get rs.rs_field)) s.its_mfields),
      rs.rs_name,
      ity rsc.cty_result
    in
    let id = s.its_ts.ts_name in
    let is_private = s.its_private in
    let args = s.its_ts.ts_args in
    begin match s.its_def, itd.itd_constructors, itd.itd_fields with
      | None, [], [] ->
        ML.mk_its_defn id args is_private None
      | None, cl, [] ->
        let cl = ddata_constructs cl in
        ML.mk_its_defn id args is_private (Some (ML.Ddata cl))
      | None, _, pjl ->
        let p e = not (rs_ghost e) in
        let pjl = filter_ghost_params p drecord_fields pjl in
        begin match pjl with
          | [] -> ML.mk_its_defn id args is_private (Some (ML.Dalias ML.tunit))
          | [_, _, ty_pj] when is_optimizable_record_itd itd ->
            ML.mk_its_defn id args is_private (Some (ML.Dalias ty_pj))
          | pjl -> ML.mk_its_defn id args is_private (Some (ML.Drecord pjl))
        end
      | Some t, _, _ ->
         ML.mk_its_defn id args is_private (Some (ML.Dalias (ity t)))
    end

  exception ExtractionVal of rsymbol

  let is_val = function
    | Eexec ({c_node = Cany}, _) -> true
    | _ -> false

  (* pids: identifiers from cloned modules without definitions *)
  let pdecl _pids info pd =
    match pd.pd_node with
    | PDlet (LDsym (rs, _)) when rs_ghost rs ->
      []
    | PDlet (LDsym (_rs, {c_node = Cany})) ->
      []
      (* raise (ExtractionVal _rs) *)
    | PDlet (LDsym (_, {c_node = Cfun e})) when is_val e.e_node ->
      []
    | PDlet (LDsym ({rs_cty = cty} as rs, {c_node = Cfun e})) ->
      let args = params cty.cty_args in
      let res  = ity cty.cty_result in
      [ML.Dlet (ML.Lsym (rs, res, args, expr info e))]
    | PDlet (LDrec rl) ->
      let def {rec_fun = e; rec_sym = rs1; rec_rsym = rs2} =
        let e = match e.c_node with Cfun e -> e | _ -> assert false in
        let args = params rs1.rs_cty.cty_args in
        let res  = ity rs1.rs_cty.cty_result in
        { ML.rec_sym  = rs1;  ML.rec_rsym = rs2;
          ML.rec_args = args; ML.rec_exp  = expr info e;
          ML.rec_res  = res } in
      let rec_def = filter_ghost_rdef def rl in
      [ML.Dlet (ML.Lrec rec_def)]
    | PDlet (LDsym _) | PDpure | PDlet (LDvar _) ->
      []
    | PDtype itl ->
      let itsd = List.map tdef itl in
      [ML.Dtype itsd]
    | PDexn xs ->
      if ity_equal xs.xs_ity ity_unit then [ML.Dexn (xs, None)]
      else [ML.Dexn (xs, Some (ity xs.xs_ity))]

  let pdecl_m m pd =
    let info = { ML.from_mod = Some m; ML.from_km  = m.mod_known; } in
    pdecl Sid.empty info pd

  (* unit module declarations *)
  let rec mdecl pids info = function
    | Udecl pd -> pdecl pids info pd
    | Uscope (_, _, l) -> List.concat (List.map (mdecl pids info) l)
    | Uuse _ | Uclone _ | Umeta _ -> []

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
    | Uscope (_, _, l) -> List.for_all empty_munit l
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

  let make_param from mi =
    let id = mi.mi_mod.mod_theory.Theory.th_name in
    Format.printf "param %s@." id.id_string;
    let dl =
      List.concat (List.map (mdecl Sid.empty from) mi.mi_mod.mod_units) in
    ML.Dclone (id, dl)

  let ids_of_params pids mi =
    Mid.fold (fun id _ pids -> Sid.add id pids) mi.mi_mod.mod_known pids

  (* modules *)
  let module_ m =
    let from = { ML.from_mod = Some m; ML.from_km = m.mod_known; } in
    let params = find_params m.mod_units in
    let pids = List.fold_left ids_of_params Sid.empty params in
    let mod_decl = List.concat (List.map (mdecl pids from) m.mod_units) in
    let mod_decl = List.map (make_param from) params @ mod_decl in
    let add known_map decl =
      let idl = ML.get_decl_name decl in
      List.fold_left (ML.add_known_decl decl) known_map idl in
    let mod_known = List.fold_left add Mid.empty mod_decl in
    { ML.mod_from = from; ML.mod_decl = mod_decl; ML.mod_known = mod_known }

  let () = Exn_printer.register (fun fmt e -> match e with
    | ExtractionAny ->
      Format.fprintf fmt "Cannot extract an undefined node"
    | ExtractionVal rs ->
      Format.fprintf fmt "Function %a cannot be extracted"
        print_rs rs
    | _ -> raise e)

end

(** Some transformations *)

module Transform = struct

  open ML

  let no_reads_writes_conflict spv spv_mreg =
    let is_reg {pv_ity = ity} = match ity.ity_node with
        | Ityreg rho -> not (Mreg.mem rho spv_mreg)
        | _ -> true in
    Spv.for_all is_reg spv

  type subst = expr Mpv.t

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
         restricted substituion. This keeps some proxy lets, preventing
         undiserable captures inside the [Efun] expression. *)
      let e, spv = expr info restrict_subst e in
      mk (Efun (vl, e)), spv
    | Eif (e1, e2, e3) ->
      let e1, s1 = expr info subst e1 in
      let e2, s2 = expr info subst e2 in
      let e3, s3 = expr info subst e3 in
      mk (Eif (e1, e2, e3)), Spv.union (Spv.union s1 s2) s3
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
      let e = mk (Efor (x, pv1, dir, pv2, e)) in
      (* be careful when pv1 and pv2 are in subst *)
      mk_let subst pv1 (mk_let subst pv2 e), spv
    | Eraise (exn, None) -> mk (Eraise (exn, None)), Spv.empty
    | Eraise (exn, Some e) ->
      let e, spv = expr info subst e in
      mk (Eraise (exn, Some e)), spv
    | Etry (e, bl) ->
      let e, spv = expr info subst e in
      let e_bl, spv_bl = mk_list_eb bl (xbranch info subst) in
      mk (Etry (e, e_bl)), Spv.union spv spv_bl
    | Eassign al ->
      let assign e (_, _, pv) = mk_let subst pv e in
      List.fold_left assign e al, Spv.empty
    | Econst _ | Eabsurd | Ehole -> e, Spv.empty
    | Eignore e ->
      let e, spv = expr info subst e in
      mk (Eignore e), spv

  and mk_let subst pv e =
    try let e1 = Mpv.find pv subst in
      { e with e_node = Elet (Lvar (pv, e1), e) }
    with Not_found -> e

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
    | Lrec rl ->
      let rdef, spv = mk_list_eb rl (rdef info subst) in
      Lrec rdef, spv

  and rdef info subst r =
    let rec_exp, spv = expr info subst r.rec_exp in
    { r with rec_exp = rec_exp }, spv

  let pdecl info = function
    | Dtype _ | Dexn _ | Dclone _ as d -> d
    | Dlet def ->
      (* for top-level symbols we can forget the set of inlined variables *)
      let e, _ = let_def info Mpv.empty def in
      Dlet e

  let module_ m =
    let mod_decl = List.map (pdecl m.mod_from) m.mod_decl in
    let add known_map decl =
      let idl = get_decl_name decl in
      List.fold_left (ML.add_known_decl decl) known_map idl in
    let mod_known = List.fold_left add Mid.empty mod_decl in
    { m with mod_decl = mod_decl; mod_known = mod_known }

end

(*
 * Local Variables:
 * compile-command: "make -C ../.. -j3 bin/why3extract.opt"
 * End:
 *)
