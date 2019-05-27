(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Expr
open Ident
open Ty
open Ity
open Term

type ty =
  | Tvar   of tvsymbol
  | Tapp   of ident * ty list
  | Ttuple of ty list

type is_ghost = bool

type var = ident * ty * is_ghost

type for_direction = To | DownTo

type pat =
  | Pwild
  | Pvar   of vsymbol
  | Papp   of lsymbol * pat list
  | Ptuple of pat list
  | Por    of pat * pat
  | Pas    of pat * vsymbol

type is_rec = bool

type binop = Band | Bor | Beq

type ity = I of Ity.ity | C of Ity.cty (* TODO: keep it like this? *)

type expr = {
  e_node   : expr_node;
  e_ity    : ity;
  e_effect : effect;
  e_attrs  : Sattr.t;
}

and expr_node =
  | Econst  of Number.int_constant
  | Evar    of pvsymbol
  | Eapp    of rsymbol * expr list
  | Efun    of var list * expr
  | Elet    of let_def * expr
  | Eif     of expr * expr * expr
  | Eassign of (pvsymbol * rsymbol * expr) list
  | Ematch  of expr * reg_branch list * exn_branch list
  | Eblock  of expr list
  | Ewhile  of expr * expr
  (* For loop for Why3's type int *)
  | Efor    of pvsymbol * pvsymbol * for_direction * pvsymbol * expr
  | Eraise  of xsymbol * expr option
  | Eexn    of xsymbol * ty option * expr
  | Eignore of expr
  | Eabsurd

and reg_branch = pat * expr

and exn_branch = xsymbol * pvsymbol list * expr

and let_def =
  | Lvar of pvsymbol * expr
  | Lsym of rsymbol * Stv.t * ty * var list * expr
  | Lany of rsymbol * Stv.t * ty * var list
  | Lrec of rdef list

and rdef = {
  rec_sym  : rsymbol;
  rec_args : var list;
  rec_exp  : expr;
  rec_res  : ty;
  rec_svar : Stv.t; (* set of type variables *)
}

type is_mutable = bool

type typedef =
  | Ddata    of (ident * ty list) list
  | Drecord  of (is_mutable * ident * ty) list
  | Dalias   of ty
  | Drange   of Number.int_range
  | Dfloat   of Number.float_format

type its_defn = {
  its_name    : ident;
  its_args    : tvsymbol list;
  its_private : bool;
  its_def     : typedef option;
}

type decl =
  | Dtype   of its_defn list
  | Dlet    of let_def
  | Dval    of pvsymbol * ty (* top-level constants, of the form [val c: tau] *)
  | Dexn    of xsymbol * ty option
  | Dmodule of string * decl list

type namespace = (ident * decl list) list

type from_module = {
  from_mod: Pmodule.pmodule option;
  from_km : Pdecl.known_map;
}

type known_map = decl Mid.t

type pmodule = {
  mod_from  : from_module; (* information about original Why3 module *)
  mod_decl  : decl list;   (* module declarations *)
  mod_known : known_map;   (* known identifiers *)
}

let rec get_decl_name = function
  | Dtype itdefl ->
      let add_id = function (* add name of constructors and projections *)
        | Some (Ddata l)   -> List.map (fun (idc,    _) -> idc) l
        | Some (Drecord l) -> List.map (fun (_, idp, _) -> idp) l
        | _ -> [] in
      let add_td_ids {its_name = id; its_def = def} = id :: (add_id def) in
      List.flatten (List.map add_td_ids itdefl)
  | Dlet (Lrec rdef) -> List.map (fun {rec_sym = rs} -> rs.rs_name) rdef
  | Dlet (Lvar ({pv_vs={vs_name=id}}, _))
  | Dlet (Lsym ({rs_name=id}, _, _, _, _))
  | Dlet (Lany ({rs_name=id}, _, _, _))
  | Dval ({pv_vs={vs_name=id}}, _)
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
  | Drange _ | Dfloat _ -> ()

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
  | Pwild | Pvar _ -> ()
  | Papp (ls, patl) ->
      f ls.ls_name;
      iter_deps_pat_list f patl
  | Ptuple patl -> iter_deps_pat_list f patl
  | Por (p1, p2) ->
      iter_deps_pat f p1;
      iter_deps_pat f p2
  | Pas (p, _) -> iter_deps_pat f p

and iter_deps_expr f e = match e.e_node with
  | Econst _ | Eabsurd -> ()
  | Evar pv -> f pv.pv_vs.vs_name
  | Eapp (rs, exprl) ->
      f rs.rs_name; List.iter (iter_deps_expr f) exprl
  | Efun (args, e) ->
      List.iter (fun (_, ty_arg, _) -> iter_deps_ty f ty_arg) args;
      iter_deps_expr f e
  | Elet (Lvar (_, e1), e2) ->
      iter_deps_expr f e1;
      iter_deps_expr f e2
  | Elet (Lsym (_, _, ty_result, args, e1), e2) ->
      iter_deps_ty f ty_result;
      List.iter (fun (_, ty_arg, _) -> iter_deps_ty f ty_arg) args;
      iter_deps_expr f e1;
      iter_deps_expr f e2
  | Elet (Lany (_, _, ty_result, args), e2) ->
      iter_deps_ty f ty_result;
      List.iter (fun (_, ty_arg, _) -> iter_deps_ty f ty_arg) args;
      iter_deps_expr f e2
  | Elet ((Lrec rdef), e) ->
      List.iter
        (fun {rec_sym = rs; rec_args = args; rec_exp = e; rec_res = res} ->
           f rs.rs_name; iter_deps_args f args;
           iter_deps_expr f e; iter_deps_ty f res) rdef;
      iter_deps_expr f e
  | Ematch (e, branchl, xl) ->
      iter_deps_expr f e;
      List.iter (fun (p, e) -> iter_deps_pat f p; iter_deps_expr f e) branchl;
      List.iter (iter_deps_xbranch f) xl
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
  | Eassign assingl ->
      List.iter (fun (_, rs, _) -> f rs.rs_name) assingl
  | Eignore e -> iter_deps_expr f e

let rec iter_deps f = function
  | Dtype its_dl ->
      List.iter (iter_deps_its_defn f) its_dl
  | Dlet (Lsym (_rs, _, ty_result, args, e)) ->
      iter_deps_ty f ty_result;
      iter_deps_args f args;
      iter_deps_expr f e
  | Dlet (Lany (_rs, _, ty_result, args)) ->
      iter_deps_ty f ty_result;
      iter_deps_args f args
  | Dlet (Lrec rdef) ->
      List.iter
        (fun {rec_sym = rs; rec_args = args; rec_exp = e; rec_res = res} ->
           f rs.rs_name; iter_deps_args f args;
           iter_deps_expr f e; iter_deps_ty f res) rdef
  | Dlet (Lvar (_, e)) -> iter_deps_expr f e
  | Dexn (_, None) -> ()
  | Dexn (_, Some ty) | Dval (_, ty) -> iter_deps_ty f ty
  | Dmodule (_, dl) -> List.iter (iter_deps f) dl

let ity_unit = I Ity.ity_unit

let ity_of_mask ity mask =
  let mk_ty acc ty = function MaskGhost -> acc | _ -> ty :: acc in
  match ity, mask with
  | _, MaskGhost   -> ity_unit
  | _, MaskVisible -> ity
  | I ({ity_node = Ityapp ({its_ts = s}, tl, _)}), MaskTuple m
    when is_ts_tuple s && List.length tl = List.length m ->
      let tl = List.fold_left2 mk_ty [] tl m in
      I (ity_tuple tl)
  | _ -> ity (* FIXME ? *)

let mk_expr e_node e_ity mask e_effect e_attrs =
  { e_node; e_ity = ity_of_mask e_ity mask; e_effect; e_attrs; }

let tunit = Ttuple []

let is_unit = function
  | I i -> ity_equal i Ity.ity_unit
  | _ -> false

let enope = Eblock []

let mk_var id ty ghost = (id, ty, ghost)

let mk_var_unit =
  let attrs = Sattr.singleton Dexpr.dummy_var_attr in
  mk_var (id_register (id_fresh ~attrs "_")) tunit false

let mk_its_defn its_name its_args its_private its_def =
  { its_name; its_args; its_private; its_def; }

(* smart constructors *)
let e_unit attrs =
  mk_expr enope (I Ity.ity_unit) MaskVisible Ity.eff_empty attrs

let dummy_expr_attr = Ident.create_attribute "__dummy_expr__"

let e_dummy_unit = e_unit (Sattr.singleton dummy_expr_attr)
let e_unit = e_unit Sattr.empty

let e_const c =
  mk_expr (Econst c)

let e_var pv =
  mk_expr (Evar pv)

let var_defn pv e =
  Lvar (pv, e)

let sym_defn f svars ty_res args e =
  Lsym (f, svars, ty_res, args, e)

let e_let ld e = mk_expr (Elet (ld, e))

let e_app rs pvl =
  mk_expr (Eapp (rs, pvl))

let e_fun args e = mk_expr (Efun (args, e))

let e_ignore e_ity e =
  (* TODO : avoid ignore around a unit type expresson *)
  if ity_equal e_ity Ity.ity_unit then e
  else mk_expr (Eignore e) ity_unit MaskVisible e.e_effect e.e_attrs

let e_if e1 e2 e3 =
  mk_expr (Eif (e1, e2, e3)) e2.e_ity

let e_while e1 e2 =
  mk_expr (Ewhile (e1, e2)) ity_unit

let e_for pv1 pv2 dir pv3 e1 =
  mk_expr (Efor (pv1, pv2, dir, pv3, e1)) ity_unit

let e_match e bl xl =
  mk_expr (Ematch (e, bl, xl))

(*
  let e_match_exn e bl eff_bl lbl_match xl =
    let ity = match bl with (_, d) :: _ -> d.e_ity | [] -> assert false in
    let e = e_match e bl ity eff_bl lbl_match in
    mk_expr (Etry (e, true, xl))
*)

let e_assign al ity mask eff attrs =
  if al = [] then e_unit else mk_expr (Eassign al) ity mask eff attrs

let e_absurd =
  mk_expr Eabsurd

let e_seq e1 e2 =
  let e = match e1.e_node, e2.e_node with
    | Eblock [], e | e, Eblock [] -> e
    | Eblock e1, Eblock e2 -> Eblock (e1 @ e2)
    | _, Eblock e2 -> Eblock (e1 :: e2)
    | Eblock e1, _ -> Eblock (e1 @ [e2])
    | _ -> Eblock [e1; e2] in
  mk_expr e

let var_list_of_pv_list pvl =
  let mk_var pv = mk_expr (Evar pv) (I pv.pv_ity)
      MaskVisible eff_empty Sattr.empty in
  List.map mk_var pvl

let ld_map fn ld = match ld with
  | Lsym (rs, tv, ty, vl, e) -> Lsym (rs, tv, ty, vl, fn e)
  | Lvar (pv, e) -> Lvar (pv, fn e)
  | Lany _ -> ld
  | Lrec rl ->
     Lrec (List.map (fun rd -> { rd with rec_exp = fn rd.rec_exp }) rl)

let e_map fn e =
  let mk en = { e with e_node = en } in
  match e.e_node with
  | Econst _ | Evar _ | Efun (_,_) | Eabsurd -> e
  | Eapp (rs,el) -> mk (Eapp(rs,(List.map fn el)))
  | Elet (ld,e) -> mk (Elet (ld_map fn ld, fn e))
  | Eif (c,t,e) -> mk (Eif (fn c, fn t, fn e))
  | Eassign al ->
     let al' = List.map (fun (pv, rs, e) -> pv, rs, fn e) al in
     mk (Eassign al')
  | Ematch (e,bl,xl) ->
     let bl' = List.map (fun (p,e) -> (p, fn e)) bl in
     let xl' = List.map (fun (x, vl, e) -> (x, vl, fn e)) xl in
     mk (Ematch (fn e, bl', xl'))
  | Eblock el -> mk (Eblock (List.map fn el))
  | Ewhile (c,b) -> mk (Ewhile (fn c, fn b))
  | Efor (i,vb,d,ve,e) -> mk (Efor (i, vb, d, ve, fn e))
  | Eraise (_, None) -> e
  | Eraise (x, Some e) -> mk (Eraise (x, Some (fn e)))
  | Eexn (x,t,e) -> mk (Eexn (x, t, fn e))
  | Eignore e -> mk (Eignore (fn e))


let ld_fold fn acc ld = match ld with
  | Lsym (_,_,_,_, e) | Lvar (_, e)-> fn acc e
  | Lany _ -> acc
  | Lrec rl -> List.fold_left (fun acc rd -> fn acc rd.rec_exp) acc rl

let e_fold fn acc e =
  match e.e_node with
  | Econst _ | Evar _
  | Efun (_,_) | Eabsurd -> acc
  | Eapp (_,el) -> List.fold_left fn acc el
  | Elet (ld,e) -> fn (ld_fold fn acc ld) e
  | Eif (c,t,e) ->
     let acc = fn acc c in
     let acc = fn acc t in
     fn acc e
  | Eassign al -> List.fold_left (fun acc (_,_,e) -> fn acc e) acc al
  | Ematch (e,bl,xl) ->
     let acc = List.fold_left (fun acc (_p,e) -> fn acc e) acc bl in
     let acc = List.fold_left (fun acc (_x, _vl, e) -> fn acc e) acc xl in
     fn acc e
  | Eblock el -> List.fold_left fn acc el
  | Ewhile (c,b) -> fn (fn acc c) b
  | Efor (_,_,_,_,e) -> fn acc e
  | Eraise (_, None) -> acc
  | Eraise (_, Some e) -> fn acc e
  | Eexn (_x,_t,e) -> fn acc e
  | Eignore e -> fn acc e

let ld_map_fold fn acc ld = match ld with
  | Lsym (rs, tv, ty, vl, e) ->
     let acc, e = fn acc e in
     acc, Lsym (rs, tv, ty, vl, e)
  | Lvar (pv, e) ->
     let acc, e = fn acc e in
     acc, Lvar (pv, e)
  | Lany _ -> acc, ld
  | Lrec rl ->
     let acc, rl =
       Lists.map_fold_left
         (fun acc rd ->
           let acc, re = fn acc rd.rec_exp in
           acc, { rd with rec_exp = re })
         acc rl in
     acc, Lrec rl

let e_map_fold fn acc e =
  let mk en = { e with e_node = en } in
  match e.e_node with
  | Econst _ | Evar _
  | Efun (_,_) | Eabsurd -> acc, e
  | Eapp (rs,el) ->
     let acc,el = Lists.map_fold_left fn acc el in
     acc,mk (Eapp(rs,el))
  | Elet (ld,e) ->
     let acc, ld = ld_map_fold fn acc ld in
     let acc, e = fn acc e in
     acc, mk (Elet (ld, e))
  | Eif (c,t,e) ->
     let acc, c = fn acc c in
     let acc, t = fn acc t in
     let acc, e = fn acc e in
     acc, mk (Eif (c, t, e))
  | Eassign al ->
     let acc,al' =
       Lists.map_fold_left
         (fun acc (pv, rs, e) ->
           let acc, e = fn acc e in
           acc, (pv, rs, e))
         acc al in
     acc, mk (Eassign al')
  | Ematch (e,bl,xl) ->
     let acc, bl' =
       Lists.map_fold_left
         (fun acc (p,e) ->
           let acc, e = fn acc e in
           acc, (p, e)) acc bl in
     let acc, xl' =
       Lists.map_fold_left
         (fun acc (x, vl, e) ->
           let acc, e = fn acc e in
           acc, (x, vl, e)) acc xl in
     let acc, e = fn acc e in
     acc, mk (Ematch (e, bl', xl'))
  | Eblock el ->
     let acc, el' = Lists.map_fold_left fn acc el in
     acc, mk (Eblock el')
  | Ewhile (c,b) ->
     let acc, c' = fn acc c in
     let acc, b' = fn acc b in
     acc, mk (Ewhile (c', b'))
  | Efor (i,vb,d,ve,e) ->
     let acc, e' = fn acc e in
     acc, mk (Efor (i, vb, d, ve, e'))
  | Eraise (_, None) -> acc, e
  | Eraise (x, Some e) ->
     let acc, e' = fn acc e in
     acc, mk (Eraise (x, Some e'))
  | Eexn (x,t,e) ->
     let acc, e' = fn acc e in
     acc, mk (Eexn (x, t, e'))
  | Eignore e ->
     let acc, e' = fn acc e in
     acc, mk (Eignore e')
