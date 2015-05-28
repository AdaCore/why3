(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
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
    (Ity.ImpurePrivateField f.pv_ity)
  (* FIXME: the ImpurePrivateField error message in Ity is
     too restrictive wrt all the cases we use check_field.
     We should either provide different exceptions or rewrite
     the message. *)

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
  s.its_def = None

let create_semi_constructor id s fl pjl invl =
  let ity = ity_app s (List.map ity_var s.its_ts.ts_args) s.its_regions in
  let res = create_vsymbol (id_fresh "result") (ty_of_ity ity) in
  let t = t_var res in
  let get_pj p = match p.rs_logic with RLls s -> s | _ -> assert false in
  let mk_q {pv_vs = v} p = t_equ (fs_app (get_pj p) [t] v.vs_ty) (t_var v) in
  let q = create_post res (t_and_simp_l (List.map2 mk_q fl pjl)) in
  let c = create_cty fl invl [q] Mexn.empty eff_empty ity in
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

type mdecl = {
  md_node : mdecl_node;
  md_pure : Decl.decl list;
  md_syms : Sid.t;
  md_news : Sid.t;
  md_tag  : int;
}

and mdecl_node =
  | MDtype of its_defn list
  | MDlet  of let_defn
  | MDexn  of xsymbol
  | MDpure
