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
  - option to extract into a single file

  - no more why3extract.cma
    use driver preludes instead

  - 2 drivers for nums and zarith

  - no delcaration at all for a module -> no file produced
    (e.g. ref.Ref)

  - suggest a command line to compile the extracted code
    (for instance in a comment)

  - drivers for val now may use %1, %2, etc. (though not mandatory)
    Capp f x y
      "..." -> "..." x y
      "...%1..." -> "...x..." y
      "..(*%1*)..." -> "...(*x*)..." y
      "..%1..%3.." -> (fun z -> "..x..z..")  (y ignored)

  - extract file f.mlw into OCaml file f.ml, with sub-modules

  - "use (im|ex)port" -> "open"
    but OCaml's open is not transitive, so requires some extra work
    to figure out all the opens

  - if a WhyML module M is extracted to something that is a signature,
    then extract "module type B_sig = ..." (as well as "module B = ...")

  - use a black list in printer to avoid clash with Pervasives symbols
    (e.g. ref, (!), etc.)

*)

(*
  Questions pour Jean-Christophe et Andreï :
    - est-ce qu'il y a des utilisations particulières du champ
      [itd_fields], vis-à-vis du champ [itd_constructors] ?

    - comme l'AST [expr] est déjà en forme normale-A, est-ce que ça
      fait du sense pour vous d'utiliser des applications de la forme
      [Eapp of ident * ident list] ?

    - faire un module Erasure, pour y concentrer tout ce qui
      appartient à l'éffacement du code fantôme ?

    - comment est-ce qu'il marche la [mask] d'un [prog_pattern] ?

 *)

(*
  TODO: réfléchir sur l'affectation parallèle
*)


(** Abstract syntax of ML *)

open Ident
open Ity
open Ty
open Term
open Printer

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

  type exn =
    | Xident of ident

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
    | Ecast   of expr * ty
    | Eassign of (pvsymbol * rsymbol * pvsymbol) list
    | Etuple  of expr list (* at least 2 expressions *)
    | Ematch  of expr * (pat * expr) list
    | Ebinop  of expr * binop * expr
    | Enot    of expr
    | Eblock  of expr list
    | Ewhile  of expr * expr
    | Efor    of pvsymbol * pvsymbol * for_direction * pvsymbol * expr
    | Eraise  of exn * expr option
    | Etry    of expr * (exn * pvsymbol option * expr) list
    | Eabsurd

  and let_def =
    | Lvar of pvsymbol * expr
    | Lsym of rsymbol * var list * expr
    | Lrec of rdef list

  and rdef = {
    rec_sym  : rsymbol; (* exported *)
    rec_rsym : rsymbol; (* internal *)
    rec_args : var list;
    rec_exp  : expr;
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

  type decl = (* TODO add support for the extraction of ocaml modules *)
    | Dtype   of its_defn list
    | Dlet    of let_def
        (* TODO add return type? *)
    | Dexn    of xsymbol * ty option

  (* type pmodule = { *)
  (* } *)

  let mk_expr e_node e_ity e_effect =
    { e_node = e_node; e_ity = e_ity; e_effect = e_effect }

  (* smart constructors *)
  let ml_let_var pv e1 e2 =
    Elet (Lvar (pv, e1), e2)

  let tunit = Ttuple []

  let enope = Eblock []

  let mk_unit =
    mk_expr enope (I Ity.ity_unit) Ity.eff_empty

  let mk_var id ty ghost = (id, ty, ghost)

  let mk_its_defn id args private_ def =
    { its_name = id; its_args = args; its_private = private_; its_def = def; }

  let eseq e1 e2 =
    match e1.e_node, e2.e_node with
    | Eblock [], e | e, Eblock [] -> e
    | Eblock e1, Eblock e2 -> Eblock (e1 @ e2)
    | _, Eblock e2 -> Eblock (e1 :: e2)
    | Eblock e1, _ -> Eblock (e1 @ [e2])
    | _ -> Eblock [e1; e2]

end

type info = {
  info_syn          : syntax_map;
  info_convert      : syntax_map;
  info_current_th   : Theory.theory;
  info_current_mo   : Pmodule.pmodule option;
  info_th_known_map : Decl.known_map;
  info_mo_known_map : Pdecl.known_map;
  info_fname        : string option;
}

let has_syntax cxt id =
  (* Mid.iter *)
  (*   (fun id' _ -> Format.printf "id': %s@\n" id'.id_string) *)
  (*   cxt.info_syn; *)
  query_syntax cxt.info_syn id <> None ||
  query_syntax cxt.info_convert id <> None

(** Translation from Mlw to ML *)

module Translate = struct

  open Expr    (* Mlw expressions *)

  open Pmodule (* for the type of modules *)
  open Pdecl   (* for the type of program declarations *)

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

  let filter_ghost_params p def l =
    let rec filter_ghost_params_cps l k =
      match l with
      | [] -> k []
      | e :: r ->
        filter_ghost_params_cps r
          (fun fr -> k (if p e then (def e) :: fr else fr))
    in
    filter_ghost_params_cps l (fun x -> x)

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

  let rec pat p =
    match p.pat_node with
    | Pwild ->
      ML.Pwild
    | Pvar vs ->
      ML.Pident vs.vs_name
    | Por (p1, p2) ->
      ML.Por (pat p1, pat p2)
    | Pas (p, vs) ->
      ML.Pas (pat p, vs.vs_name)
    | Papp (ls, pl) when is_fs_tuple ls ->
      ML.Ptuple (List.map pat pl)
    | Papp (ls, pl) ->
      let rs = restore_rs ls in
      let args = rs.rs_cty.cty_args in
      let pat_pl = List.fold_left2
          (fun acc pv pp -> if not pv.pv_ghost then (pat pp) :: acc else acc)
          [] args pl
      in
      ML.Papp (ls, List.rev pat_pl)

  (** programs *)

  let pv_name pv = pv.pv_vs.vs_name

  let is_underscore pv =
    (pv_name pv).id_string = "_" && ity_equal pv.pv_ity ity_unit

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

  (* function arguments *)
  let args = (* point-free *)
    List.map pvty

  let isconstructor info rs =
    match Mid.find_opt rs.rs_name info.info_mo_known_map with
    | Some {pd_node = PDtype its} ->
      let is_constructor its =
        List.exists (rs_equal rs) its.itd_constructors in
      List.exists is_constructor its
    | _ -> false

  let make_eta_expansion rsc pvl cty_app =
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

  let app pvl =
    let def pv = ML.mk_expr (ML.Evar pv) (ML.I pv.pv_ity) eff_empty in
    filter_ghost_params pv_not_ghost def pvl

  (* expressions *)
  let rec expr info ({e_effect = eff} as e) =
    assert (not eff.eff_ghost);
    match e.e_node with
    | Econst c ->
      let c = match c with Number.ConstInt c -> c | _ -> assert false in
      ML.mk_expr (ML.Econst c) (ML.I e.e_ity) eff
    | Evar pvs ->
      ML.mk_expr (ML.Evar pvs) (ML.I e.e_ity) eff
    | Elet (LDvar (pvs, e1), e2) when is_underscore pvs && e_ghost e2 ->
      ML.mk_expr (ML.eseq (expr info e1) ML.mk_unit) (ML.I e.e_ity) eff
    | Elet (LDvar (pvs, e1), e2) when is_underscore pvs ->
      ML.mk_expr (ML.eseq (expr info e1) (expr info e2)) (ML.I e.e_ity) eff
    | Elet (LDvar (pvs, e1), e2) when e_ghost e1 ->
      let ml_let = ML.ml_let_var pvs ML.mk_unit (expr info e2) in
      ML.mk_expr ml_let (ML.I e.e_ity) eff
    | Elet (LDvar (pvs, e1), e2) ->
      let ml_let = ML.ml_let_var pvs (expr info e1) (expr info e2) in
      ML.mk_expr ml_let (ML.I e.e_ity) eff
    | Elet (LDsym (rs, {c_node = Cfun ef; c_cty = cty}), ein) ->
      let def pv = pv_name pv, ity pv.pv_ity, pv.pv_ghost in
      let al pv = pv_name pv, ML.tunit, false in
      let args = filter2_ghost_params pv_not_ghost def al cty.cty_args in
      let ef = expr info ef in
      let ein = expr info ein in
      let ml_letrec = ML.Elet (ML.Lsym (rs, args, ef), ein) in
      ML.mk_expr ml_letrec (ML.I e.e_ity) eff
    | Elet (LDsym (rsf, {c_node = Capp (rs_app, pvl); c_cty = cty}), ein)
      when isconstructor info rs_app ->

      let eta_app = make_eta_expansion rs_app pvl cty in
      let ein = expr info ein in
      let ml_letrec = ML.Elet (ML.Lsym (rsf, [], eta_app), ein) in
      ML.mk_expr ml_letrec (ML.I e.e_ity) e.e_effect
    | Elet (LDsym (rsf, {c_node = Capp (rs_app, pvl); c_cty = cty}), ein) ->
      let pvl = app pvl in
      let eapp =
        ML.mk_expr (ML.Eapp (rs_app, pvl)) (ML.C cty) cty.cty_effect in
      let ein = expr info ein in
      let ml_letrec = ML.Elet (ML.Lsym (rsf, [], eapp), ein) in
      ML.mk_expr ml_letrec (ML.I e.e_ity) e.e_effect
    | Elet (LDrec rdefl, ein) ->
      let def pv = pv_name pv, ity pv.pv_ity, pv.pv_ghost in
      let al pv = pv_name pv, ML.tunit, false in
      let ein = expr info ein in
      let rdefl =
        List.map (fun rdef ->
          match rdef with
          | {rec_sym = rs1; rec_rsym = rs2;
             rec_fun = {c_node = Cfun ef; c_cty = cty}} ->
            let args =
              filter2_ghost_params pv_not_ghost def al cty.cty_args in
            let ef = expr info ef in
            { ML.rec_sym = rs1; ML.rec_rsym = rs2;
              ML.rec_args = args; ML.rec_exp = ef }
          | _ -> assert false) rdefl
      in
      let ml_letrec = ML.Elet (ML.Lrec rdefl, ein) in
      ML.mk_expr ml_letrec (ML.I e.e_ity) e.e_effect
    | Eexec ({c_node = Capp (rs, [])}, _) when is_rs_tuple rs ->
      ML.mk_unit
    | Eexec ({c_node = Capp (rs, _)}, _) when rs_ghost rs ->
      ML.mk_unit
    | Eexec ({c_node = Capp (rs, pvl); _}, _) ->
      let pvl = app pvl in
      ML.mk_expr (ML.Eapp (rs, pvl)) (ML.I e.e_ity) eff
    | Eexec ({c_node = Cfun e; c_cty = cty}, _) ->
      let def pv = pv_name pv, ity pv.pv_ity, pv.pv_ghost in
      let al pv = pv_name pv, ML.tunit, false in
      let args = filter2_ghost_params pv_not_ghost def al cty.cty_args in
      ML.mk_expr (ML.Efun (args, expr info e)) (ML.I e.e_ity) eff
    | Eexec ({c_node = Cany}, _) ->
      (* Error message here *) assert false
    | Eabsurd ->
      ML.mk_expr ML.Eabsurd (ML.I e.e_ity) eff
    | Ecase (e1, _) when e_ghost e1 ->
      ML.mk_unit
    | Ecase (e1, pl) ->
      let e1 = expr info e1 in
      let pl = List.map (ebranch info) pl in
      ML.mk_expr (ML.Ematch (e1, pl)) (ML.I e.e_ity) eff
    | Eassert _ ->
      ML.mk_unit
    | Eif (e1, e2, e3) ->
      let e1 = expr info e1 in
      let e2 = expr info e2 in
      let e3 = expr info e3 in
      ML.mk_expr (ML.Eif (e1, e2, e3)) (ML.I e.e_ity) eff
    | Ewhile (e1, _, _, e2) ->
      let e1 = expr info e1 in
      let e2 = expr info e2 in
      ML.mk_expr (ML.Ewhile (e1, e2)) (ML.I e.e_ity) eff
    | Efor (pv1, (pv2, direction, pv3), _, efor) ->
      let efor = expr info efor in
      let direction = for_direction direction in
      ML.mk_expr (ML.Efor (pv1, pv2, direction, pv3, efor)) (ML.I e.e_ity) eff
    | Eghost _ ->
      assert false
    | Eassign [(rho, rs, pv)] ->
      ML.mk_expr (ML.Eassign [(rho, rs, pv)]) (ML.I e.e_ity) eff
    | Epure _ -> assert false
    | Etry _ -> assert false
    | Eraise (xs, ex) ->
      let ex =
        let open ML in
        match expr info ex with
        | {e_node = Eblock []} -> None
        | e -> Some e
      in
      let exn = ML.Xident xs.xs_name in
      ML.mk_expr (ML.Eraise (exn, ex)) (ML.I e.e_ity) eff
    | _ -> (* TODO *) assert false

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
    let drecord_fields ({rs_cty = rsc} as rs) = (* point-free *)
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
        ML.mk_its_defn id args is_private (Some (ML.Drecord pjl))
      | Some t, _, _ ->
         ML.mk_its_defn id args is_private (Some (ML.Dalias (ity t)))
    end

  let is_val e =
    match e.e_node with
    | Eexec ({c_node = Cany}, _) -> true
    | _ -> false

  (* program declarations *)
  let pdecl info pd =
    match pd.pd_node with
    | PDlet (LDsym (rs, _)) when rs_ghost rs ->
       []
    | PDlet (LDsym (_, {c_node = Cfun e})) when is_val e ->
      []
    | PDlet (LDsym ({rs_cty = cty} as rs, {c_node = Cfun e})) ->
      let args_filter =
        let p (_, _, is_ghost) = not is_ghost in
        let def = fun x -> x in
        let al = fun x -> x in
        filter2_ghost_params p def al (args cty.cty_args) in
      [ML.Dlet (ML.Lsym (rs, args_filter, expr info e))]
    | PDlet (LDrec rl) ->
      let rec_def =
        List.map (fun {rec_fun = e; rec_sym = rs1; rec_rsym = rs2} ->
          let e = match e.c_node with Cfun e -> e | _ -> assert false in
          let args_filter =
            let p (_, _, is_ghost) = not is_ghost in
            let def = fun x -> x in
            let al = fun x -> x in
            filter2_ghost_params p def al (args rs1.rs_cty.cty_args) in
          { ML.rec_sym = rs1; ML.rec_rsym = rs2;
            ML.rec_args = args_filter; ML.rec_exp = expr info e }) rl
      in
      [ML.Dlet (ML.Lrec rec_def)]
    | PDlet (LDsym _)
    | PDpure
    | PDlet (LDvar (_, _)) ->
      []
    | PDtype itl ->
      [ML.Dtype (List.map tdef itl)]
    | PDexn xs ->
       if ity_equal xs.xs_ity ity_unit then
         [ML.Dexn (xs, None)]
       else
         [ML.Dexn (xs, Some (ity xs.xs_ity))]

  (* unit module declarations *)
  let mdecl info = function
    | Udecl pd ->
       pdecl info pd
    |  _ -> (* TODO *) []

  (* modules *)
  let module_ info m =
    List.concat (List.map (mdecl info) m.mod_units)

end

(** Optimistion operations *)

(* module Erasure = struct *)

(*   open ML *)

(*   let rec remove_superf_let subs e = *)
(*     match e.e_node with *)
(*     | Evar pv -> try let Hpv.find pv  *)
(*     | Eapp    of rsymbol * expr list *)
(*     | Efun    of var list * expr *)
(*     | Elet    of let_def * expr *)
(*     | Eif     of expr * expr * expr *)
(*     | Ecast   of expr * ty *)
(*     | Eassign of (pvsymbol * rsymbol * pvsymbol) list *)
(*     | Etuple  of expr list (\* at least 2 expressions *\) *)
(*     | Ematch  of expr * (pat * expr) list *)
(*     | Ebinop  of expr * binop * expr *)
(*     | Enot    of expr *)
(*     | Eblock  of expr list *)
(*     | Ewhile  of expr * expr *)
(*     | Efor    of pvsymbol * pvsymbol * for_direction * pvsymbol * expr *)
(*     | Eraise  of exn * expr option *)
(*     | Etry    of expr * (exn * pvsymbol option * expr) list *)
(*     | _ -> e.e_node *)

(* end *)

(*
 * Local Variables:
 * compile-command: "make -C ../.. -j3 bin/why3extract.opt"
 * End:
 *)
