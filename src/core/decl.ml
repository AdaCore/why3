(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Util
open Ident
open Ty
open Term

(** Type declaration *)

type ty_def =
  | Tabstract
  | Talgebraic of lsymbol list

type ty_decl = tysymbol * ty_def

(** Logic declaration *)

type ls_defn = lsymbol * fmla

type logic_decl = lsymbol * ls_defn option

exception UnboundVars of Svs.t
exception IllegalConstructor of lsymbol

let check_fvs f =
  let fvs = f_freevars Svs.empty f in
  if Svs.is_empty fvs then f else raise (UnboundVars fvs)

let make_fs_defn fs vl t =
  if fs.ls_constr then raise (IllegalConstructor fs);
  let hd = t_app fs (List.map t_var vl) t.t_ty in
  let fd = f_forall vl [] (f_equ hd t) in
  fs, Some (fs, check_fvs fd)

let make_ps_defn ps vl f =
  let hd = f_app ps (List.map t_var vl) in
  let pd = f_forall vl [] (f_iff hd f) in
  ps, Some (ps, check_fvs pd)

let make_ls_defn ls vl = e_apply (make_fs_defn ls vl) (make_ps_defn ls vl)

let open_ls_defn (_,f) =
  let vl, ef = f_open_forall f in
  match ef.f_node with
    | Fapp (s, [t1; t2]) when s == ps_equ ->
        begin match t1.t_node with
          | Tapp (fs, _) -> vl, Term t2
          | _ -> assert false
        end
    | Fbinop (Fiff, f1, f2) ->
        begin match f1.f_node with
          | Fapp (ps, _) -> vl, Fmla f2
          | _ -> assert false
        end
    | _ -> assert false

let open_fs_defn ld = let vl,e = open_ls_defn ld in
  match e with Term t -> vl,t | _ -> assert false

let open_ps_defn ld = let vl,e = open_ls_defn ld in
  match e with Fmla f -> vl,f | _ -> assert false

let ls_defn_axiom (_,f) = f

(** Inductive predicate declaration *)

type prsymbol = {
  pr_name : ident;
}

module Prop = StructMake (struct
  type t = prsymbol
  let tag pr = pr.pr_name.id_tag
end)

module Spr = Prop.S
module Mpr = Prop.M
module Hpr = Prop.H

let create_prsymbol n = { pr_name = id_register n }

type prop = prsymbol * fmla

type ind_decl = lsymbol * prop list

(** Proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * prsymbol * fmla

(** Declaration type *)

type decl = {
  d_node : decl_node;
  d_tag  : int;
}

and decl_node =
  | Dtype  of ty_decl list      (* recursive types *)
  | Dlogic of logic_decl list   (* recursive functions/predicates *)
  | Dind   of ind_decl list     (* inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)

(** Declarations *)

module Hsdecl = Hashcons.Make (struct

  type t = decl

  let eq_td (ts1,td1) (ts2,td2) = ts1 == ts2 && match td1,td2 with
    | Tabstract, Tabstract -> true
    | Talgebraic l1, Talgebraic l2 -> list_all2 (==) l1 l2
    | _ -> false

  let eq_ld (ls1,ld1) (ls2,ld2) = ls1 == ls2 && match ld1,ld2 with
    | Some (_,f1), Some (_,f2) -> f1 == f2
    | None, None -> true
    | _ -> false

  let eq_iax (pr1,fr1) (pr2,fr2) = pr1 == pr1 && fr1 == fr2

  let eq_ind (ps1,al1) (ps2,al2) = ps1 == ps2 && list_all2 eq_iax al1 al2

  let equal d1 d2 = match d1.d_node, d2.d_node with
    | Dtype  l1, Dtype  l2 -> list_all2 eq_td l1 l2
    | Dlogic l1, Dlogic l2 -> list_all2 eq_ld l1 l2
    | Dind   l1, Dind   l2 -> list_all2 eq_ind l1 l2
    | Dprop (k1,pr1,f1), Dprop (k2,pr2,f2) ->
        k1 == k2 && pr1 == pr2 && f1 == f2
    | _,_ -> false

  let hs_td (ts,td) = match td with
    | Tabstract -> ts.ts_name.id_tag
    | Talgebraic l ->
        let tag fs = fs.ls_name.id_tag in
        1 + Hashcons.combine_list tag ts.ts_name.id_tag l

  let hs_ld (ls,ld) = Hashcons.combine ls.ls_name.id_tag
    (Hashcons.combine_option (fun (_,f) -> f.f_tag) ld)

  let hs_prop (pr,f) = Hashcons.combine pr.pr_name.id_tag f.f_tag

  let hs_ind (ps,al) = Hashcons.combine_list hs_prop ps.ls_name.id_tag al

  let hs_kind = function
    | Paxiom -> 7
    | Plemma -> 11
    | Pgoal  -> 13

  let hash d = match d.d_node with
    | Dtype  l -> Hashcons.combine_list hs_td 0 l
    | Dlogic l -> Hashcons.combine_list hs_ld 3 l
    | Dind   l -> Hashcons.combine_list hs_ind 5 l
    | Dprop (k,pr,f) -> Hashcons.combine (hs_kind k) (hs_prop (pr,f))

  let tag n d = { d with d_tag = n }

end)

module Decl = StructMake (struct
  type t = decl
  let tag d = d.d_tag
end)

module Sdecl = Decl.S
module Mdecl = Decl.M
module Hdecl = Decl.H

(** Declaration constructors *)

let mk_decl n = { d_node = n; d_tag = -1 }

let create_ty_decl tdl = Hsdecl.hashcons (mk_decl (Dtype tdl))
let create_logic_decl ldl = Hsdecl.hashcons (mk_decl (Dlogic ldl))
let create_ind_decl idl = Hsdecl.hashcons (mk_decl (Dind idl))
let create_prop_decl k p f = Hsdecl.hashcons (mk_decl (Dprop (k,p,f)))

exception ConstructorExpected of lsymbol
exception UnboundTypeVar of tvsymbol
exception IllegalTypeAlias of tysymbol
exception ClashIdent of ident
exception BadLogicDecl of ident
exception EmptyDecl

let add_id s id =
  if Sid.mem id s then raise (ClashIdent id);
  Sid.add id s

let create_ty_decl tdl =
  if tdl = [] then raise EmptyDecl;
  let check_constr ty acc fs =
    if not fs.ls_constr then raise (ConstructorExpected fs);
    let vty = of_option fs.ls_value in
    ignore (ty_match Mtv.empty vty ty);
    let add s ty = match ty.ty_node with
      | Tyvar v -> Stv.add v s
      | _ -> assert false
    in
    let vs = ty_fold add Stv.empty vty in
    let rec check () ty = match ty.ty_node with
      | Tyvar v -> if not (Stv.mem v vs) then raise (UnboundTypeVar v)
      | _ -> ty_fold check () ty
    in
    List.iter (check ()) fs.ls_args;
    add_id acc fs.ls_name
  in
  let check_decl acc (ts,td) = match td with
    | Tabstract -> add_id acc ts.ts_name
    | Talgebraic cl ->
        if ts.ts_def != None then raise (IllegalTypeAlias ts);
        let ty = ty_app ts (List.map ty_var ts.ts_args) in
        List.fold_left (check_constr ty) (add_id acc ts.ts_name) cl
  in
  ignore (List.fold_left check_decl Sid.empty tdl);
  create_ty_decl tdl

let create_logic_decl ldl =
  if ldl = [] then raise EmptyDecl;
  let check_decl acc (ls,ld) = match ld with
    | Some (s,_) when s != ls -> raise (BadLogicDecl ls.ls_name)
    | _ -> add_id acc ls.ls_name
  in
  ignore (List.fold_left check_decl Sid.empty ldl);
  create_logic_decl ldl

exception InvalidIndDecl of lsymbol * prsymbol
exception TooSpecificIndDecl of lsymbol * prsymbol * term
exception NonPositiveIndDecl of lsymbol * prsymbol * lsymbol

exception Found of lsymbol
let ls_mem s sps = if Sls.mem s sps then raise (Found s) else false
let t_pos_ps sps = t_s_all (fun _ -> true) (fun s -> not (ls_mem s sps))

let rec f_pos_ps sps pol f = match f.f_node, pol with
  | Fapp (s, _), Some false when ls_mem s sps -> false
  | Fapp (s, _), None when ls_mem s sps -> false
  | Fbinop (Fiff, f, g), _ ->
      f_pos_ps sps None f && f_pos_ps sps None g
  | Fbinop (Fimplies, f, g), _ ->
      f_pos_ps sps (option_map not pol) f && f_pos_ps sps pol g
  | Fnot f, _ ->
      f_pos_ps sps (option_map not pol) f
  | Fif (f,g,h), _ ->
      f_pos_ps sps None f && f_pos_ps sps pol g && f_pos_ps sps pol h
  | _ -> f_all (t_pos_ps sps) (f_pos_ps sps pol) f

let create_ind_decl idl =
  if idl = [] then raise EmptyDecl;
  let add acc (ps,_) = Sls.add ps acc in
  let sps = List.fold_left add Sls.empty idl in
  let check_ax ps acc (pr,f) =
    let rec clause acc f = match f.f_node with
      | Fquant (Fforall, f) ->
          let _,_,f = f_open_quant f in clause acc f
      | Fbinop (Fimplies, g, f) -> clause (g::acc) f
      | _ -> (acc, f)
    in
    let cls, f = clause [] (check_fvs f) in
    match f.f_node with
      | Fapp (s, tl) when s == ps ->
          let mtch sb t ty =
            try ty_match sb (t.t_ty) ty with TypeMismatch ->
              raise (TooSpecificIndDecl (ps, pr, t))
          in
          ignore (List.fold_left2 mtch Mtv.empty tl ps.ls_args);
          (try ignore (List.for_all (f_pos_ps sps (Some true)) cls)
          with Found ls ->
            raise (NonPositiveIndDecl (ps, pr, ls)));
          add_id acc pr.pr_name
      | _ -> raise (InvalidIndDecl (ps, pr))
  in
  let check_decl acc (ps,al) =
    List.fold_left (check_ax ps) (add_id acc ps.ls_name) al
  in
  ignore (List.fold_left check_decl Sid.empty idl);
  create_ind_decl idl

let create_prop_decl k p f = create_prop_decl k p (check_fvs f)

(** Split declarations *)

let build_dls get_id get_dep dl =
  let add_id acc d = Sid.add (get_id d) acc in
  let s = List.fold_left add_id Sid.empty dl in
  let add_dl (next,loan,dls,dl) d =
    let dl = d :: dl in
    let id = get_id d in
    let next = Sid.remove id next in
    let loan = Sid.remove id loan in
    let loan = get_dep next loan d in
    if Sid.is_empty loan
      then next, loan, List.rev dl :: dls, []
      else next, loan,                dls, dl
  in
  let init = (s, Sid.empty, [], []) in
  let next,loan,dls,dl = List.fold_left add_dl init dl in
  assert (Sid.is_empty next);
  assert (Sid.is_empty loan);
  assert (dl = []);
  dls

let get_ty_id (ts,_) = ts.ts_name

let get_ty_dep next loan (ts,td) =
  let dep acc ts = if Sid.mem ts.ts_name next
    then Sid.add ts.ts_name acc else acc in
  let loan = match ts.ts_def with
    | Some ty -> ty_s_fold dep loan ty
    | None    -> loan
  in
  let cns acc ls =
    List.fold_left (ty_s_fold dep) acc ls.ls_args in
  match td with
    | Tabstract      -> loan
    | Talgebraic fdl -> List.fold_left cns loan fdl

let get_logic_id (ls,_) = ls.ls_name

let get_logic_dep next loan (_,ld) =
  let dts acc _  = acc in
  let dep acc ls = if Sid.mem ls.ls_name next
    then Sid.add ls.ls_name acc else acc in
  match ld with
    | Some (_,f) -> f_s_fold dts dep loan f
    | None       -> loan

let get_ind_id (ps,_) = ps.ls_name

let get_ind_dep next loan (_,al) =
  let dts acc _  = acc in
  let dep acc ls = if Sid.mem ls.ls_name next
    then Sid.add ls.ls_name acc else acc in
  let prp acc (_,f) = f_s_fold dts dep acc f in
  List.fold_left prp loan al

let create_ty_decls tdl =
  let build = build_dls get_ty_id get_ty_dep in
  match tdl with
  | [_] -> [create_ty_decl tdl]
  | _   -> List.rev_map create_ty_decl (build tdl)

let create_logic_decls ldl =
  let build = build_dls get_logic_id get_logic_dep in
  match ldl with
  | [_] -> [create_logic_decl ldl]
  | _   -> List.rev_map create_logic_decl (build ldl)

let create_ind_decls idl =
  let build = build_dls get_ind_id get_ind_dep in
  match idl with
  | [_] -> [create_ind_decl idl]
  | _   -> List.rev_map create_ind_decl (build idl)


(** Utilities *)

let decl_map fnT fnF d = match d.d_node with
  | Dtype _ ->
      d
  | Dlogic l ->
      let fn = function
        | ls, Some ld ->
            let vl,e = open_ls_defn ld in
            make_ls_defn ls vl (e_map fnT fnF e)
        | ld -> ld
      in
      create_logic_decl (List.map fn l)
  | Dind l ->
      let fn (pr,f) = pr, fnF f in
      let fn (ps,l) = ps, List.map fn l in
      create_ind_decl (List.map fn l)
  | Dprop (k,pr,f) ->
      create_prop_decl k pr (fnF f)

let decl_fold fnT fnF acc d = match d.d_node with
  | Dtype _ -> acc
  | Dlogic l ->
      let fn acc = function
        | _, Some ld ->
            let _,e = open_ls_defn ld in
            e_fold fnT fnF acc e
        | _ -> acc
      in
      List.fold_left fn acc l
  | Dind l ->
      let fn acc (_,f) = fnF acc f in
      let fn acc (_,l) = List.fold_left fn acc l in
      List.fold_left fn acc l
  | Dprop (_,_,f) -> fnF acc f


(** Known identifiers *)

exception KnownIdent of ident
exception UnknownIdent of ident
exception RedeclaredIdent of ident

type known_map = decl Mid.t

let known_id kn id =
  if not (Mid.mem id kn) then raise (UnknownIdent id)

let known_ts kn () ts = known_id kn ts.ts_name
let known_ls kn () ls = known_id kn ls.ls_name

let known_ty kn ty = ty_s_fold (known_ts kn) () ty
let known_term kn t = t_s_fold (known_ts kn) (known_ls kn) () t
let known_fmla kn f = f_s_fold (known_ts kn) (known_ls kn) () f

let merge_known kn1 kn2 =
  let add_known id decl kn =
    try
      if Mid.find id kn2 != decl then raise (RedeclaredIdent id);
      kn
    with Not_found -> Mid.add id decl kn
  in
  Mid.fold add_known kn1 kn2

let add_known id decl kn =
  try
    if Mid.find id kn != decl then raise (RedeclaredIdent id);
    raise (KnownIdent id)
  with Not_found -> Mid.add id decl kn

let add_constr d kn fs = add_known fs.ls_name d kn

let add_type d kn (ts,def) =
  let kn = add_known ts.ts_name d kn in
  match def with
    | Tabstract -> kn
    | Talgebraic lfs -> List.fold_left (add_constr d) kn lfs

let check_type kn (ts,def) =
  let check_constr fs = List.iter (known_ty kn) fs.ls_args in
  match def with
    | Tabstract -> option_iter (known_ty kn) ts.ts_def
    | Talgebraic lfs -> List.iter check_constr lfs

let add_logic d kn (ls,_) = add_known ls.ls_name d kn

let check_ls_defn kn ld =
  let _,e = open_ls_defn ld in
  e_apply (known_term kn) (known_fmla kn) e

let check_logic kn (ls,ld) =
  List.iter (known_ty kn) ls.ls_args;
  option_iter (known_ty kn) ls.ls_value;
  option_iter (check_ls_defn kn) ld

let add_ind d kn (ps,la) =
  let kn = add_known ps.ls_name d kn in
  let add kn (pr,_) = add_known pr.pr_name d kn in
  List.fold_left add kn la

let check_ind kn (ps,la) =
  List.iter (known_ty kn) ps.ls_args;
  let check (_,f) = known_fmla kn f in
  List.iter check la

let add_decl kn d = match d.d_node with
  | Dtype dl  -> List.fold_left (add_type d) kn dl
  | Dlogic dl -> List.fold_left (add_logic d) kn dl
  | Dind dl   -> List.fold_left (add_ind d) kn dl
  | Dprop (_,pr,_) -> add_known pr.pr_name d kn

let check_decl kn d = match d.d_node with
  | Dtype dl  -> List.iter (check_type kn) dl
  | Dlogic dl -> List.iter (check_logic kn) dl
  | Dind dl   -> List.iter (check_ind kn) dl
  | Dprop (_,_,f) -> known_fmla kn f

let find_constructors kn ts =
  match (Mid.find ts.ts_name kn).d_node with
  | Dtype dl ->
      begin match List.assq ts dl with
        | Talgebraic cl -> cl
        | Tabstract -> []
      end
  | _ -> assert false

let find_inductive_cases kn ps =
  match (Mid.find ps.ls_name kn).d_node with
  | Dind dl -> List.assq ps dl
  | Dlogic _ -> []
  | _ -> assert false

let find_prop kn pr =
  match (Mid.find pr.pr_name kn).d_node with
  | Dind dl ->
      let test (_,l) = List.mem_assq pr l in
      List.assq pr (snd (List.find test dl))
  | Dprop (_,pr,f) -> f
  | _ -> assert false

exception NonExhaustiveExpr of (pattern list * expr)

let rec check_matchT kn () t = match t.t_node with
  | Tcase (tl,bl) ->
      let mk_b (pl,_,t) = (pl,t) in
      let bl = List.map (fun b -> mk_b (t_open_branch b)) bl in
      ignore (try Pattern.CompileTerm.compile (find_constructors kn) tl bl
      with Pattern.NonExhaustive pl -> raise (NonExhaustiveExpr (pl, Term t)))
  | _ -> t_fold (check_matchT kn) (check_matchF kn) () t

and check_matchF kn () f = match f.f_node with
  | Fcase (tl,bl) ->
      let mk_b (pl,_,f) = (pl,f) in
      let bl = List.map (fun b -> mk_b (f_open_branch b)) bl in
      ignore (try Pattern.CompileFmla.compile (find_constructors kn) tl bl
      with Pattern.NonExhaustive pl -> raise (NonExhaustiveExpr (pl, Fmla f)))
  | _ -> f_fold (check_matchT kn) (check_matchF kn) () f

let check_match kn d = decl_fold (check_matchT kn) (check_matchF kn) () d

let known_add_decl kn d =
  let kn = add_decl kn d in
  ignore (check_decl kn d);
  ignore (check_match kn d);
  kn

