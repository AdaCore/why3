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

(** Named propositions *)

type prop = {
  pr_name : ident;
  pr_fmla : fmla;
}

module Prop = struct
  type t = prop
  let equal = (==)
  let hash pr = pr.pr_name.id_tag
  let compare pr1 pr2 =
    Pervasives.compare pr1.pr_name.id_tag pr2.pr_name.id_tag
end
module Mpr = Map.Make(Prop)
module Spr = Set.Make(Prop)
module Hpr = Hashtbl.Make(Prop)

exception UnboundVars of Svs.t

let check_fvs f =
  let fvs = f_freevars Svs.empty f in
  if Svs.is_empty fvs then f else raise (UnboundVars fvs)

let create_prop n f = {
  pr_name = id_register n;
  pr_fmla = check_fvs f;
}

(** Declarations *)

(* type declaration *)

type ty_def =
  | Tabstract
  | Talgebraic of lsymbol list

type ty_decl = tysymbol * ty_def

(* logic declaration *)

type fs_defn = lsymbol * vsymbol list * term * fmla
type ps_defn = lsymbol * vsymbol list * fmla * fmla

type logic_decl =
  | Lfunction  of lsymbol * fs_defn option
  | Lpredicate of lsymbol * ps_defn option

exception IllegalConstructor of lsymbol

let make_fs_defn fs vl t =
  if fs.ls_constr then raise (IllegalConstructor fs);
  let hd = t_app fs (List.map t_var vl) t.t_ty in
  let fd = f_forall vl [] (f_equ hd t) in
  fs, vl, t, check_fvs fd

let make_ps_defn ps vl f =
  let hd = f_app ps (List.map t_var vl) in
  let pd = f_forall vl [] (f_iff hd f) in
  ps, vl, f, check_fvs pd

let extract_fs_defn f =
  let vl, ef = f_open_forall f in
  match ef.f_node with
    | Fapp (s, [t1; t2]) when s == ps_equ ->
        begin match t1.t_node with
          | Tapp (fs, _) -> fs, (fs, vl, t2, f)
          | _ -> assert false
        end
    | _ -> assert false

let extract_ps_defn f =
  let vl, ef = f_open_forall f in
  match ef.f_node with
    | Fbinop (Fiff, f1, f2) ->
        begin match f1.f_node with
          | Fapp (ps, _) -> ps, (ps, vl, f2, f)
          | _ -> assert false
        end
    | _ -> assert false

let open_fs_defn (fs,vl,t,_) = (fs,vl,t)
let open_ps_defn (ps,vl,f,_) = (ps,vl,f)

let fs_defn_axiom (_,_,_,fd) = fd
let ps_defn_axiom (_,_,_,pd) = pd

(* inductive predicate declaration *)

type ind_decl = lsymbol * prop list

(* proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * prop

(** Context and Theory *)

module Snm = Set.Make(String)
module Mnm = Map.Make(String)

type theory = {
  th_name   : ident;        (* theory name *)
  th_ctxt   : context;      (* theory declarations *)
  th_export : namespace;    (* exported namespace *)
  th_local  : Sid.t;        (* locally declared idents *)
}

and namespace = {
  ns_ts : tysymbol Mnm.t;   (* type symbols *)
  ns_ls : lsymbol Mnm.t;    (* logic symbols *)
  ns_pr : prop Mnm.t;       (* propositions *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
}

and context = {
  ctxt_decl   : decl;
  ctxt_prev   : context option;
  ctxt_known  : decl Mid.t;
  ctxt_cloned : Sid.t Mid.t;
  ctxt_tag    : int;
}

and decl = {
  d_node : decl_node;
  d_tag  : int;
}

and decl_node =
  | Dtype  of ty_decl list      (* recursive types *)
  | Dlogic of logic_decl list   (* recursive functions/predicates *)
  | Dind   of ind_decl list     (* inductive predicates *)
  | Dprop  of prop_decl         (* axiom / lemma / goal *)
  | Duse   of theory                         (* depend on a theory *)
  | Dclone of theory * (ident * ident) list  (* replicate a theory *)

(** Declarations *)

module Decl = struct

  type t = decl

  let for_all2 pr l1 l2 =
    try List.for_all2 pr l1 l2 with Invalid_argument _ -> false

  let eq_td (ts1,td1) (ts2,td2) = ts1 == ts2 && match td1,td2 with
    | Tabstract, Tabstract -> true
    | Talgebraic l1, Talgebraic l2 -> for_all2 (==) l1 l2
    | _ -> false

  let eq_fd fs1 fd1 fs2 fd2 = fs1 == fs2 && match fd1,fd2 with
    | Some (_,_,_,fd1), Some (_,_,_,fd2) -> fd1 == fd2
    | None, None -> true
    | _ -> false

  let eq_ld ld1 ld2 = match ld1,ld2 with
    | Lfunction  (fs1,fd1), Lfunction  (fs2,fd2) -> eq_fd fs1 fd1 fs2 fd2
    | Lpredicate (ps1,pd1), Lpredicate (ps2,pd2) -> eq_fd ps1 pd1 ps2 pd2
    | _ -> false

  let eq_ind (ps1,al1) (ps2,al2) = ps1 == ps2 && for_all2 (==) al1 al2

  let equal d1 d2 = match d1.d_node, d2.d_node with
    | Dtype  l1, Dtype  l2 -> for_all2 eq_td l1 l2
    | Dlogic l1, Dlogic l2 -> for_all2 eq_ld l1 l2
    | Dind   l1, Dind   l2 -> for_all2 eq_ind l1 l2
    | Dprop (k1,pr1), Dprop (k2,pr2) -> k1 == k2 && pr1 == pr2
    | Duse th1, Duse th2 -> th1.th_name == th2.th_name
    | Dclone (th1,sl1), Dclone (th2,sl2) -> th1.th_name == th2.th_name
        && for_all2 (fun (i,i') (j,j') -> i == j && i' == j') sl1 sl2
    | _,_ -> false

  let hs_td (ts,td) = match td with
    | Tabstract -> ts.ts_name.id_tag
    | Talgebraic l ->
        let tag fs = fs.ls_name.id_tag in
        1 + Hashcons.combine_list tag ts.ts_name.id_tag l

  let hs_fd fd = Hashcons.combine_option (fun (_,_,_,f) -> f.f_tag) fd

  let hs_ld ld = match ld with
    | Lfunction  (fs,fd) -> Hashcons.combine fs.ls_name.id_tag (hs_fd fd)
    | Lpredicate (ps,pd) -> Hashcons.combine ps.ls_name.id_tag (hs_fd pd)

  let hs_ind (ps,al) =
      let hs_pair pr = pr.pr_name.id_tag in
      Hashcons.combine_list hs_pair ps.ls_name.id_tag al

  let hash d = match d.d_node with
    | Dtype  l -> Hashcons.combine_list hs_td 0 l
    | Dlogic l -> Hashcons.combine_list hs_ld 3 l
    | Dind   l -> Hashcons.combine_list hs_ind 5 l
    | Dprop (Paxiom,pr) -> Hashcons.combine 7  pr.pr_name.id_tag
    | Dprop (Plemma,pr) -> Hashcons.combine 11 pr.pr_name.id_tag
    | Dprop (Pgoal, pr) -> Hashcons.combine 13 pr.pr_name.id_tag
    | Duse th -> Hashcons.combine 17 th.th_name.id_tag
    | Dclone (th,sl) ->
        let tag = Hashcons.combine 19 th.th_name.id_tag in
        let hs_pair (i1,i2) = Hashcons.combine i1.id_tag i2.id_tag in
        Hashcons.combine_list hs_pair tag sl

  let tag n d = { d with d_tag = n }

  let compare d1 d2 = Pervasives.compare d1.d_tag d2.d_tag

end
module Hdecl = Hashcons.Make(Decl)
module Mdecl = Map.Make(Decl)
module Sdecl = Set.Make(Decl)

(** Declaration constructors *)

let mk_decl n = { d_node = n; d_tag = -1 }

let create_ty_decl tdl = Hdecl.hashcons (mk_decl (Dtype tdl))
let create_logic_decl ldl = Hdecl.hashcons (mk_decl (Dlogic ldl))
let create_ind_decl indl = Hdecl.hashcons (mk_decl (Dind indl))
let create_prop_decl k p = Hdecl.hashcons (mk_decl (Dprop (k, p)))
let create_use_decl th = Hdecl.hashcons (mk_decl (Duse th))
let create_clone_decl th sl = Hdecl.hashcons (mk_decl (Dclone (th,sl)))

let prop_decl_of_fmla k n f = create_prop_decl k (create_prop n f)

exception ConstructorExpected of lsymbol
exception UnboundTypeVar of ident
exception IllegalTypeAlias of tysymbol

let create_ty_decl tdl =
  let check_constructor ty fs =
    if not fs.ls_constr then raise (ConstructorExpected fs);
    let vty = of_option fs.ls_value in
    ignore (Ty.matching Mid.empty vty ty);
    let add s ty = match ty.ty_node with
      | Tyvar v -> Sid.add v s
      | _ -> assert false
    in
    let vs = ty_fold add Sid.empty vty in
    let rec check () ty = match ty.ty_node with
      | Tyvar v -> if not (Sid.mem v vs) then raise (UnboundTypeVar v)
      | _ -> ty_fold check () ty
    in
    List.iter (check ()) fs.ls_args
  in
  let check_decl (ts,td) = match td with
    | Tabstract -> ()
    | Talgebraic fsl ->
        if ts.ts_def != None then raise (IllegalTypeAlias ts);
        let ty = ty_app ts (List.map ty_var ts.ts_args) in
        List.iter (check_constructor ty) fsl
  in
  List.iter check_decl tdl;
  create_ty_decl tdl

exception BadDecl of ident

let create_logic_decl ldl =
  let check_decl = function
    | Lfunction (fs, Some (s,_,_,_)) when s != fs ->
        raise (BadDecl fs.ls_name)
    | Lpredicate (ps, Some (s,_,_,_)) when s != ps ->
        raise (BadDecl ps.ls_name)
    | _ -> ()
  in
  List.iter check_decl ldl;
  create_logic_decl ldl


(** Built-in theory *)

module Ctxt = struct
  type t = context

  let equal a b = a.ctxt_decl == b.ctxt_decl &&
    match a.ctxt_prev, b.ctxt_prev with
      | Some na, Some nb -> na == nb
      | None, None -> true
      | _ -> false

  let hash ctxt =
    let prev = match ctxt.ctxt_prev with
      | Some ctxt -> 1 + ctxt.ctxt_tag
      | None -> 0
    in
    Hashcons.combine ctxt.ctxt_decl.d_tag prev

  let tag i ctxt = { ctxt with ctxt_tag = i }
end
module Hctxt = Hashcons.Make(Ctxt)

let mk_context decl prev known cloned = Hctxt.hashcons {
  ctxt_decl = decl;
  ctxt_prev = prev;
  ctxt_known = known;
  ctxt_cloned = cloned;
  ctxt_tag = -1;
}

let builtin_theory =
  let decl_int  = create_ty_decl [ts_int, Tabstract] in
  let decl_real = create_ty_decl [ts_real, Tabstract] in
  let decl_equ  = create_logic_decl [Lpredicate (ps_equ, None)] in
  let decl_neq  = create_logic_decl [Lpredicate (ps_neq, None)] in

  let kn_int    = Mid.add ts_int.ts_name decl_int Mid.empty in
  let kn_real   = Mid.add ts_real.ts_name decl_real kn_int in
  let kn_equ    = Mid.add ps_equ.ls_name decl_equ kn_real in
  let kn_neq    = Mid.add ps_neq.ls_name decl_neq kn_equ in

  let ctxt_int  = mk_context decl_int None kn_int Mid.empty in
  let ctxt_real = mk_context decl_real (Some ctxt_int) kn_real Mid.empty in
  let ctxt_equ  = mk_context decl_equ (Some ctxt_real) kn_equ Mid.empty in
  let ctxt_neq  = mk_context decl_neq (Some ctxt_equ) kn_neq Mid.empty in

  let ns_int    = Mnm.add ts_int.ts_name.id_short ts_int Mnm.empty in
  let ns_real   = Mnm.add ts_real.ts_name.id_short ts_real ns_int in
  let ns_equ    = Mnm.add ps_equ.ls_name.id_short ps_equ Mnm.empty in
  let ns_neq    = Mnm.add ps_neq.ls_name.id_short ps_neq ns_equ in

  let export = {  ns_ts = ns_real;    ns_ls = ns_neq;
                  ns_pr = Mnm.empty;  ns_ns = Mnm.empty } in

  { th_name   = id_register (id_fresh "BuiltIn");
    th_ctxt   = ctxt_neq;
    th_export = export;
    th_local  = Sid.empty }

let use_builtin = create_use_decl builtin_theory


(** Context constructors and utilities *)

type th_inst = {
  inst_ts    : tysymbol Mts.t;
  inst_ls    : lsymbol  Mls.t;
  inst_lemma : Spr.t;
  inst_goal  : Spr.t;
}

let empty_inst = {
  inst_ts    = Mts.empty;
  inst_ls    = Mls.empty;
  inst_lemma = Spr.empty;
  inst_goal  = Spr.empty;
}

module Context = struct

  let init_context =
    let known = builtin_theory.th_ctxt.ctxt_known in
    let known = Mid.add builtin_theory.th_name use_builtin known in
    mk_context use_builtin None known Mid.empty

  let push_decl ctxt kn d =
    let get_cl m id = try Mid.find id m with Not_found -> Sid.empty in
    let add_cl m m' (id,id') =
      Mid.add id' (Sid.add id (Sid.union (get_cl m id) (get_cl m' id'))) m'
    in
    let cloned = match d.d_node with
      | Dclone (th,sl) ->
          let m = th.th_ctxt.ctxt_cloned in
          List.fold_left (add_cl m) ctxt.ctxt_cloned sl
      | _ -> ctxt.ctxt_cloned
    in
    mk_context d (Some ctxt) kn cloned

  (* Manage known symbols *)

  exception UnknownIdent of ident
  exception RedeclaredIdent of ident

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

  exception DejaVu

  let add_known id decl kn =
    try
      if Mid.find id kn != decl then raise (RedeclaredIdent id);
      raise DejaVu
    with Not_found -> Mid.add id decl kn

  (* Manage declarations *)

  let add_type d kn (ts,def) =
    let kn = add_known ts.ts_name d kn in
    let add_constr kn fs = add_known fs.ls_name d kn in
    match def with
      | Tabstract -> kn
      | Talgebraic lfs -> List.fold_left add_constr kn lfs

  let check_type kn (ts,def) =
    let check_constr fs = List.iter (known_ty kn) fs.ls_args in
    match def with
      | Tabstract -> option_iter (known_ty kn) ts.ts_def
      | Talgebraic lfs -> List.iter check_constr lfs

  let add_logic d kn = function
    | Lfunction  (fs, df) -> add_known fs.ls_name d kn
    | Lpredicate (ps, dp) -> add_known ps.ls_name d kn

  let check_logic kn d =
    let check chk (_,_,e,_) = chk e in
    match d with
      | Lfunction (fs, df) ->
          known_ty kn (of_option fs.ls_value);
          List.iter (known_ty kn) fs.ls_args;
          option_iter (check (known_term kn)) df
      | Lpredicate (ps, dp) ->
          List.iter (known_ty kn) ps.ls_args;
          option_iter (check (known_fmla kn)) dp

  let add_ind d kn (ps,la) =
      let kn = add_known ps.ls_name d kn in
      let add kn pr = add_known pr.pr_name d kn in
      List.fold_left add kn la

  let check_ind kn (ps,la) =
      List.iter (known_ty kn) ps.ls_args;
      let check pr = known_fmla kn pr.pr_fmla in
      List.iter check la

  let add_decl ctxt d =
    try
      let kn = ctxt.ctxt_known in
      let kn = match d.d_node with
        | Dtype dl  -> List.fold_left (add_type d) kn dl
        | Dlogic dl -> List.fold_left (add_logic d) kn dl
        | Dind dl   -> List.fold_left (add_ind d) kn dl
        | Dprop (k,pr) -> add_known pr.pr_name d kn
        | Duse th -> add_known th.th_name d kn
        | Dclone _ -> kn
      in
      let () = match d.d_node with
        | Dtype dl  -> List.iter (check_type kn) dl
        | Dlogic dl -> List.iter (check_logic kn) dl
        | Dind dl   -> List.iter (check_ind kn) dl
        | Dprop (_,pr) -> known_fmla kn pr.pr_fmla
        | Duse _ | Dclone _ -> ()
      in
      push_decl ctxt kn d
    with DejaVu ->
      ctxt

  (* Generic utilities *)

  let rec ctxt_fold fn acc ctxt =
    let acc = fn acc ctxt.ctxt_decl in
    match ctxt.ctxt_prev with
      | Some ctxt -> ctxt_fold fn acc ctxt
      | None -> acc

  let rec ctxt_iter fn ctxt =
    fn ctxt.ctxt_decl;
    match ctxt.ctxt_prev with
      | Some ctxt -> ctxt_iter fn ctxt
      | None -> ()

  let get_decls ctxt = ctxt_fold (fun acc d -> d::acc) [] ctxt

  (* Use *)

  let add_use ctxt th =
    let d = create_use_decl th in
    try
      let kn = add_known th.th_name d ctxt.ctxt_known in
      let kn = merge_known kn th.th_ctxt.ctxt_known in
      push_decl ctxt kn d
    with DejaVu ->
      ctxt

  let rec use_export hide ctxt th =
    let d = create_use_decl th in
    try
      let kn = add_known th.th_name d ctxt.ctxt_known in
      let ctxt = push_decl ctxt kn d in
      let add_decl ctxt d = match d.d_node with
        | Duse th -> use_export true ctxt th
        | Dprop (Pgoal,_) when hide -> ctxt
        | Dprop (Plemma,pr) when hide ->
            add_decl ctxt (create_prop_decl Paxiom pr)
        | _ -> add_decl ctxt d
      in
      let decls = get_decls th.th_ctxt in
      List.fold_left add_decl ctxt decls
    with DejaVu ->
      ctxt

  (* Clone *)

  exception CannotInstantiate of ident

  type clones = {
    ts_table : tysymbol Hts.t;
    ls_table : lsymbol Hls.t;
    pr_table : prop Hpr.t;
    id_table : ident Hid.t;
    id_local : Sid.t;
  }

  let empty_clones s = {
    ts_table = Hts.create 17;
    ls_table = Hls.create 17;
    pr_table = Hpr.create 17;
    id_table = Hid.create 17;
    id_local = s;
  }

  let cl_add_ts cl ts ts' =
    Hts.add cl.ts_table ts ts';
    Hid.add cl.id_table ts.ts_name ts'.ts_name

  let cl_add_ls cl ls ls' =
    Hls.add cl.ls_table ls ls';
    Hid.add cl.id_table ls.ls_name ls'.ls_name

  let cl_add_pr cl pr pr' =
    Hpr.add cl.pr_table pr pr';
    Hid.add cl.id_table pr.pr_name pr'.pr_name

  let rec cl_find_ts cl ts =
    if not (Sid.mem ts.ts_name cl.id_local) then ts
    else try Hts.find cl.ts_table ts
    with Not_found ->
      let td' = option_map (ty_s_map (cl_find_ts cl)) ts.ts_def in
      let ts' = create_tysymbol (id_dup ts.ts_name) ts.ts_args td' in
      cl_add_ts cl ts ts';
      ts'

  let cl_trans_ty cl ty = ty_s_map (cl_find_ts cl) ty

  let cl_find_ls cl ls =
    if not (Sid.mem ls.ls_name cl.id_local) then ls
    else try Hls.find cl.ls_table ls
    with Not_found ->
      let ta' = List.map (cl_trans_ty cl) ls.ls_args in
      let vt' = option_map (cl_trans_ty cl) ls.ls_value in
      let ls' = create_lsymbol (id_dup ls.ls_name) ta' vt' ls.ls_constr in
      cl_add_ls cl ls ls';
      ls'

  let cl_trans_fmla cl f = f_s_map (cl_find_ts cl) (cl_find_ls cl) f

  let cl_find_pr cl pr =
    if not (Sid.mem pr.pr_name cl.id_local) then pr
    else try Hpr.find cl.pr_table pr
    with Not_found ->
      let f' = cl_trans_fmla cl pr.pr_fmla in
      let pr' = create_prop (id_dup pr.pr_name) f' in
      cl_add_pr cl pr pr';
      pr'

  let cl_add_type cl inst_ts acc (ts, def) =
    if Mts.mem ts inst_ts then begin
      if ts.ts_def <> None || def <> Tabstract then
        raise (CannotInstantiate ts.ts_name);
      acc
    end else
      let ts' = cl_find_ts cl ts in
      let def' = match def with
        | Tabstract -> Tabstract
        | Talgebraic ls -> Talgebraic (List.map (cl_find_ls cl) ls)
      in
      (ts', def') :: acc

  let cl_add_logic cl inst_ls acc = function
    | Lfunction (ls, Some _) | Lpredicate (ls, Some _)
      when Mls.mem ls inst_ls ->
        raise (CannotInstantiate ls.ls_name)
    | Lfunction (ls, Some (_,_,_,f)) ->
        let f' = cl_trans_fmla cl f in
        let ls', def' = extract_fs_defn f' in
        Lfunction (ls', Some def') :: acc
    | Lpredicate (_, Some (_,_,_,f)) ->
        let f' = cl_trans_fmla cl f in
        let ls', def' = extract_ps_defn f' in
        Lpredicate (ls', Some def') :: acc
    | Lfunction (ls, None) | Lpredicate (ls, None)
      when Mls.mem ls inst_ls ->
        acc
    | Lfunction (ls, None) ->
        Lfunction (cl_find_ls cl ls, None) :: acc
    | Lpredicate (ls, None) ->
        Lpredicate (cl_find_ls cl ls, None) :: acc

  let cl_add_ind cl inst_ls (ps,la) =
    if Mls.mem ps inst_ls then raise (CannotInstantiate ps.ls_name);
    cl_find_ls cl ps, List.map (cl_find_pr cl) la

  let cl_add_decl cl inst acc d = match d.d_node with
    | Dtype tyl ->
        let add = cl_add_type cl inst.inst_ts in
        let l = List.rev (List.fold_left add [] tyl) in
        if l = [] then acc else create_ty_decl l :: acc
    | Dlogic ll ->
        let add = cl_add_logic cl inst.inst_ls in
        let l = List.rev (List.fold_left add [] ll) in
        if l = [] then acc else create_logic_decl l :: acc
    | Dind indl ->
        let add = cl_add_ind cl inst.inst_ls in
        create_ind_decl (List.map add indl) :: acc
    | Dprop (Pgoal, _) ->
        acc
    | Dprop (_, pr) ->
        let k = if Spr.mem pr inst.inst_lemma then Plemma
          else if Spr.mem pr inst.inst_goal then Pgoal
          else Paxiom
        in
        create_prop_decl k (cl_find_pr cl pr) :: acc
    | Duse _ | Dclone _ ->
        d :: acc

  exception NonLocal of ident
  exception BadInstance of ident * ident

  let clone_theory th inst =
    let cl = empty_clones th.th_local in
    let check_ts ts ts' = let id = ts.ts_name in
      if not (Sid.mem id th.th_local) then raise (NonLocal id);
      if List.length ts.ts_args <> List.length ts'.ts_args
        then raise (BadInstance (id, ts'.ts_name));
      cl_add_ts cl ts ts'
    in
    let check_ls ls ls' = let id = ls.ls_name in
      if not (Sid.mem id th.th_local) then raise (NonLocal id);
      let tymatch sb ty ty' =
        try Ty.matching sb ty' (cl_trans_ty cl ty)
        with TypeMismatch -> raise (BadInstance (id, ls'.ls_name))
      in
      let sb = match ls.ls_value,ls'.ls_value with
        | Some ty, Some ty' -> tymatch Mid.empty ty ty'
        | None, None -> Mid.empty
        | _ -> raise (BadInstance (id, ls'.ls_name))
      in
      ignore (try List.fold_left2 tymatch sb ls.ls_args ls'.ls_args
      with Invalid_argument _ -> raise (BadInstance (id, ls'.ls_name)));
      cl_add_ls cl ls ls'
    in
    let check_pr pr = let id = pr.pr_name in
      if not (Sid.mem id th.th_local) then raise (NonLocal id);
    in
    Mts.iter check_ts inst.inst_ts;
    Mls.iter check_ls inst.inst_ls;
    Spr.iter check_pr inst.inst_lemma;
    Spr.iter check_pr inst.inst_goal;
    cl, ctxt_fold (cl_add_decl cl inst) [] th.th_ctxt

  let add_final ctxt th cl =
    let add id id' acc = (id,id') :: acc in
    let d = create_clone_decl th (Hid.fold add cl.id_table []) in
    add_decl ctxt d

  let add_clone ctxt th inst =
    let add_decl ctxt d = match d.d_node with
      | Duse th -> add_use ctxt th
      | _ -> add_decl ctxt d
    in
    let cl, decls = clone_theory th inst in
    let ctxt = List.fold_left add_decl ctxt decls in
    cl, add_final ctxt th cl

  let clone_export ctxt th inst =
    let add_decl ctxt d = match d.d_node with
      | Duse th  -> use_export true ctxt th
      | _ -> add_decl ctxt d
    in
    let cl, decls = clone_theory th inst in
    let ctxt = List.fold_left add_decl ctxt decls in
    add_final ctxt th cl

  let use_export ctxt th = use_export false ctxt th

end


(** Theory constructors and utilities *)

type theory_uc = {
  uc_name   : ident;
  uc_ctxt   : context;
  uc_import : namespace list;
  uc_export : namespace list;
  uc_local  : Sid.t;
}

module Theory = struct

  exception CloseTheory
  exception NoOpenedNamespace
  exception ClashSymbol of string

  (* Manage namespaces *)

  let empty_ns = {
    ns_ts = Mnm.empty;
    ns_ls = Mnm.empty;
    ns_ns = Mnm.empty;
    ns_pr = Mnm.empty;
  }

  let add_symbol chk x v m =
    if not chk then Mnm.add x v m
    else try
      if Mnm.find x m != v then raise (ClashSymbol x);
      m
    with Not_found -> Mnm.add x v m

  let merge_ns chk ns1 ns2 =
    { ns_ts = Mnm.fold (add_symbol chk) ns1.ns_ts ns2.ns_ts;
      ns_ls = Mnm.fold (add_symbol chk) ns1.ns_ls ns2.ns_ls;
      ns_ns = Mnm.fold (add_symbol chk) ns1.ns_ns ns2.ns_ns;
      ns_pr = Mnm.fold (add_symbol chk) ns1.ns_pr ns2.ns_pr; }

  let add_ts chk x ts ns = { ns with ns_ts = add_symbol chk x ts ns.ns_ts }
  let add_ls chk x fs ns = { ns with ns_ls = add_symbol chk x fs ns.ns_ls }
  let add_pr chk x f  ns = { ns with ns_pr = add_symbol chk x f  ns.ns_pr }
  let add_ns chk x v  ns = { ns with ns_ns = add_symbol chk x v  ns.ns_ns }

  let add_symbol add id v uc =
    match uc.uc_import, uc.uc_export with
    | i0 :: sti, e0 :: ste -> { uc with
        uc_import = add false id.id_short v i0 :: sti;
        uc_export = add true  id.id_short v e0 :: ste;
        uc_local  = Sid.add id uc.uc_local }
    | _ ->
        assert false

  (* Manage theories *)

  let create_theory n = {
    uc_name   = n;
    uc_ctxt   = Context.init_context;
    uc_import = [builtin_theory.th_export];
    uc_export = [builtin_theory.th_export];
    uc_local  = Sid.empty;
  }

  let create_theory n = create_theory (id_register n)

  let close_theory uc = match uc.uc_export with
    | [e] ->
        { th_name   = uc.uc_name;
          th_ctxt   = uc.uc_ctxt;
          th_export = e;
          th_local  = uc.uc_local; }
    | _ ->
        raise CloseTheory

  let open_namespace uc = match uc.uc_import with
    | ns :: _ ->
        { uc with
            uc_import =       ns :: uc.uc_import;
            uc_export = empty_ns :: uc.uc_export; }
    | [] ->
        assert false

  let close_namespace uc import s =
    match uc.uc_import, uc.uc_export with
    | _ :: i1 :: sti, e0 :: e1 :: ste ->
        let i1 = if import then merge_ns false e0 i1 else i1 in
        let _  = if import then merge_ns true  e0 e1 else e1 in
        let i1 = match s with Some s -> add_ns false s e0 i1 | _ -> i1 in
        let e1 = match s with Some s -> add_ns true  s e0 e1 | _ -> e1 in
        { uc with uc_import = i1 :: sti; uc_export = e1 :: ste; }
    | [_], [_] ->
        raise NoOpenedNamespace
    | _ ->
        assert false

  let use_export uc th =
    match uc.uc_import, uc.uc_export with
      | i0 :: sti, e0 :: ste -> { uc with
          uc_import = merge_ns false th.th_export i0 :: sti;
          uc_export = merge_ns true  th.th_export e0 :: ste;
          uc_ctxt   = Context.add_use uc.uc_ctxt th }
      | _ ->
          assert false

  let clone_export uc th inst =
    let cl,ctxt = Context.add_clone uc.uc_ctxt th inst in

    let add_local _ id' acc =
      if Mid.mem id' uc.uc_ctxt.ctxt_known then acc else Sid.add id' acc in
    let local = Hid.fold add_local cl.Context.id_table uc.uc_local in

    let find_ts ts = if Sid.mem ts.ts_name th.th_local
      then Hts.find cl.Context.ts_table ts else ts in
    let find_ls ls = if Sid.mem ls.ls_name th.th_local
      then Hls.find cl.Context.ls_table ls else ls in
    let find_pr pr = if Sid.mem pr.pr_name th.th_local
      then Hpr.find cl.Context.pr_table pr else pr in
    let f_ts n ts ns = add_ts true n (find_ts ts) ns in
    let f_ls n ls ns = add_ls true n (find_ls ls) ns in
    let f_pr n pr ns = add_pr true n (find_pr pr) ns in
    let rec f_ns n s = add_ns true n (merge_namespace empty_ns s)
    and merge_namespace acc ns =
      let acc = Mnm.fold f_ts ns.ns_ts acc in
      let acc = Mnm.fold f_ls ns.ns_ls acc in
      let acc = Mnm.fold f_pr ns.ns_pr acc in
      let acc = Mnm.fold f_ns ns.ns_ns acc in acc  in
    let ns = merge_namespace empty_ns th.th_export in

    match uc.uc_import, uc.uc_export with
      | i0 :: sti, e0 :: ste -> { uc with
          uc_import = merge_ns false ns i0 :: sti;
          uc_export = merge_ns true  ns e0 :: ste;
          uc_local  = local;
          uc_ctxt   = ctxt }
      | _ ->
          assert false

  (** Manage new declarations *)

  let add_type uc (ts,def) =
    let add_constr uc fs = add_symbol add_ls fs.ls_name fs uc in
    let uc = add_symbol add_ts ts.ts_name ts uc in
    match def with
      | Tabstract -> uc
      | Talgebraic lfs -> List.fold_left add_constr uc lfs

  let add_logic uc = function
    | Lfunction  (fs,_) -> add_symbol add_ls fs.ls_name fs uc
    | Lpredicate (ps,_) -> add_symbol add_ls ps.ls_name ps uc

  let add_ind uc (ps,la) =
    let uc = add_symbol add_ls ps.ls_name ps uc in
    let add uc pr = add_symbol add_pr pr.pr_name pr uc in
    List.fold_left add uc la

  let add_decl uc d =
    let uc = match d.d_node with
      | Dtype dl  -> List.fold_left add_type uc dl
      | Dlogic dl -> List.fold_left add_logic uc dl
      | Dind dl   -> List.fold_left add_ind uc dl
      | Dprop (_, pr) -> add_symbol add_pr pr.pr_name pr uc
      | Dclone _ | Duse _ -> uc
    in
    { uc with uc_ctxt = Context.add_decl uc.uc_ctxt d }

  let get_namespace uc = List.hd uc.uc_import

end

(** Debugging *)

let print_ident =
  let printer = create_printer [] in
  let print fmt id = Format.fprintf fmt "%s" (id_unique printer id) in
  print

let rec print_namespace fmt ns =
  fprintf fmt "@[<hov 2>types: ";
  Mnm.iter (fun x ty -> fprintf fmt "%s -> %a;@ " x print_ident ty.ts_name)
    ns.ns_ts;
  fprintf fmt "@]@\n@[<hov 2>logic symbols: ";
  Mnm.iter (fun x s -> fprintf fmt "%s -> %a;@ " x print_ident s.ls_name)
    ns.ns_ls;
  fprintf fmt "@]@\n@[<hov 2>namespace: ";
  Mnm.iter (fun x th -> fprintf fmt "%s -> [@[%a@]];@ " x print_namespace th)
    ns.ns_ns;
  fprintf fmt "@]"

let print_uc fmt uc = print_namespace fmt (Theory.get_namespace uc)

let print_ctxt fmt ctxt =
  fprintf fmt "@[<hov 2>ctxt : cloned : %a@]"
    (Pp.print_iter2 Mid.iter Pp.semi (Pp.constant_string "->")
    print_ident (Pp.print_iter1 Sid.iter Pp.simple_comma print_ident))
    ctxt.ctxt_cloned

let print_th fmt th = fprintf fmt "<theory (TODO>"

