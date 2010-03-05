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
open Pp
open Util
open Ident
open Ty
open Term

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
  | Linductive of lsymbol * (ident * fmla) list

exception UnboundVars of Svs.t

let check_fvs f =
  let fvs = f_freevars Svs.empty f in
  if Svs.is_empty fvs then f else raise (UnboundVars fvs)

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

(* proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * ident * fmla

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
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
  ns_pr : fmla Mnm.t;       (* propositions *)
}

and context = {
  ctxt_decls : (decl * context) option;
  ctxt_known : decl Mid.t;
  ctxt_tag   : int;
}

and decl = {
  d_node : decl_node;
  d_tag  : int;
}

and decl_node =
  | Dtype  of ty_decl list
  | Dlogic of logic_decl list
  | Dprop  of prop_decl
  | Duse   of theory
  | Dclone of (ident * ident) list


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
    | Linductive (ps1,al1), Linductive (ps2,al2) -> ps1 == ps2 &&
        for_all2 (fun (i1,f1) (i2,f2) -> i1 == i2 && f1 == f2) al1 al2
    | _ -> false

  let equal d1 d2 = match d1.d_node, d2.d_node with
    | Dtype  l1, Dtype  l2 -> for_all2 eq_td l1 l2
    | Dlogic l1, Dlogic l2 -> for_all2 eq_ld l1 l2
    | Dprop (k1,i1,f1), Dprop (k2,i2,f2) -> k1 == k2 && i1 == i2 && f1 == f2
    | Duse th1, Duse th2 -> th1.th_name == th2.th_name
    | _ -> false

  let hs_td (ts,td) = match td with
    | Tabstract -> ts.ts_name.id_tag
    | Talgebraic l ->
        let tag fs = fs.ls_name.id_tag in
        1 + Hashcons.combine_list tag ts.ts_name.id_tag l

  let hs_fd fd = Hashcons.combine_option (fun (_,_,_,f) -> f.f_tag) fd

  let hs_ld ld = match ld with
    | Lfunction  (fs,fd) -> Hashcons.combine fs.ls_name.id_tag (hs_fd fd)
    | Lpredicate (ps,pd) -> Hashcons.combine ps.ls_name.id_tag (hs_fd pd)
    | Linductive (ps,l)  ->
        let hs_pair (i,f) = Hashcons.combine i.id_tag f.f_tag in
        Hashcons.combine_list hs_pair ps.ls_name.id_tag l

  let hash d = match d.d_node with
    | Dtype  l -> Hashcons.combine_list hs_td 0 l
    | Dlogic l -> Hashcons.combine_list hs_ld 3 l
    | Dprop (Paxiom,i,f) -> Hashcons.combine2 7  i.id_tag f.f_tag
    | Dprop (Plemma,i,f) -> Hashcons.combine2 11 i.id_tag f.f_tag
    | Dprop (Pgoal, i,f) -> Hashcons.combine2 13 i.id_tag f.f_tag
    | Duse th -> 17 * th.th_name.id_tag
    | Dclone sl ->
        let hs_pair (i1,i2) = Hashcons.combine i1.id_tag i2.id_tag in
        Hashcons.combine_list hs_pair 19 sl

  let tag n d = { d with d_tag = n }

  let compare d1 d2 = Pervasives.compare d1.d_tag d2.d_tag

end
module Hdecl = Hashcons.Make(Decl)
module Mdecl = Map.Make(Decl)
module Sdecl = Set.Make(Decl)

(** Declaration constructors *)

let mk_decl n = { d_node = n; d_tag = -1 }

let create_type tdl = Hdecl.hashcons (mk_decl (Dtype tdl))
let create_logic ldl = Hdecl.hashcons (mk_decl (Dlogic ldl))
let create_prop k i f = Hdecl.hashcons (mk_decl (Dprop (k, id_register i, f)))
let create_use th = Hdecl.hashcons (mk_decl (Duse th))
let create_clone sl = Hdecl.hashcons (mk_decl (Dclone sl))

exception ConstructorExpected of lsymbol
exception UnboundTypeVar of ident
exception IllegalTypeAlias of tysymbol

let create_type tdl =
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
  create_type tdl

exception BadDecl of ident

let create_logic ldl =
  let check_decl = function
    | Lfunction (fs, Some (s,_,_,_)) when s != fs ->
        raise (BadDecl fs.ls_name)
    | Lpredicate (ps, Some (s,_,_,_)) when s != ps ->
        raise (BadDecl ps.ls_name)
    | Linductive (ps,la) ->
        let check_ax (_,f) =
          ignore (check_fvs f);
        in
        List.iter check_ax la
    | _ -> ()
  in
  List.iter check_decl ldl;
  create_logic ldl

let create_prop k i f =
  let fvs = f_freevars Svs.empty f in
  if not (Svs.is_empty fvs) then raise (UnboundVars fvs);
  create_prop k i f


(** Built-in symbols *)

let builtin_ts = [ts_int; ts_real]
let builtin_type =
  let decl ts = ts.ts_name, ts, create_type [ts, Tabstract] in
  List.map decl builtin_ts

let builtin_ls = [ps_equ; ps_neq]
let builtin_logic =
  let decl ls = ls.ls_name, ls, create_logic [Lpredicate (ls, None)] in
  List.map decl builtin_ls

let builtin_known =
  let add l = List.fold_right (fun (n,_,d) -> Mid.add n d) l in
  add builtin_logic (add builtin_type Mid.empty)


(** Context constructors and utilities *)

module Ctxt = struct
  type t = context

  let equal a b = match a.ctxt_decls, b.ctxt_decls with
    | Some (da, na), Some (db, nb) -> da == db && na == nb
    | None, None -> true
    | _ -> false

  let hash ctxt = match ctxt.ctxt_decls with
    | Some (d,n) -> 1 + (Hashcons.combine n.ctxt_tag d.d_tag)
    | None -> 0

  let tag i ctxt = { ctxt with ctxt_tag = i }
end
module Hctxt = Hashcons.Make(Ctxt)

type th_inst = {
  inst_ts : tysymbol Mts.t;
  inst_ls : lsymbol  Mls.t;
}

module Context = struct

  let empty_context = Hctxt.hashcons {
    ctxt_decls = None;
    ctxt_known = builtin_known;
    ctxt_tag   = -1;
  }

  let push_decl ctxt d =
    Hctxt.hashcons { ctxt with
      ctxt_decls = Some (d, ctxt);
    }

  let push_kn_decl ctxt kn d =
    Hctxt.hashcons { ctxt with
      ctxt_decls = Some (d, ctxt);
      ctxt_known = kn
    }

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

  let add_known kn id decl =
    try
      if Mid.find id kn != decl then raise (RedeclaredIdent id);
      raise DejaVu
    with Not_found -> Mid.add id decl kn

  (* Manage declarations *)

  let add_type d kn (ts,def) =
    let kn = add_known kn ts.ts_name d in
    let add_constr kn fs = add_known kn fs.ls_name d in
    match def with
      | Tabstract -> kn
      | Talgebraic lfs -> List.fold_left add_constr kn lfs

  let check_type kn (ts,def) =
    let check_constr fs = List.iter (known_ty kn) fs.ls_args in
    match def with
      | Tabstract -> option_iter (known_ty kn) ts.ts_def
      | Talgebraic lfs -> List.iter check_constr lfs

  let add_logic d kn = function
    | Lfunction  (fs, df) -> add_known kn fs.ls_name d
    | Lpredicate (ps, dp) -> add_known kn ps.ls_name d
    | Linductive (ps, la) ->
	let kn = add_known kn ps.ls_name d in
	let add kn (id,f) = add_known kn id d in
	List.fold_left add kn la

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
      | Linductive (ps, la) ->
          List.iter (known_ty kn) ps.ls_args;
          let check (_,f) = known_fmla kn f in
          List.iter check la

  let add_decl ctxt d =
    try
      let kn = ctxt.ctxt_known in
      let kn = match d.d_node with
        | Dtype dl  -> List.fold_left (add_type d) kn dl
        | Dlogic dl -> List.fold_left (add_logic d) kn dl
        | Dprop (k, id, _) -> add_known kn id d;
        | Duse _ | Dclone _ -> assert false
      in
      let () = match d.d_node with
        | Dtype dl  -> List.iter (check_type kn) dl
        | Dlogic dl -> List.iter (check_logic kn) dl;
        | Dprop (_, _, f) -> known_fmla kn f
        | Duse _ | Dclone _ -> assert false
      in
      push_kn_decl ctxt kn d
    with DejaVu ->
      ctxt

  (* Generic utilities *)

  let rec ctxt_fold fn acc ctxt = match ctxt.ctxt_decls with
    | Some (d, ctxt) -> ctxt_fold fn (fn acc d) ctxt
    | None -> acc

  let rec ctxt_iter fn ctxt = match ctxt.ctxt_decls with
    | Some (d, ctxt) -> fn d; ctxt_iter fn ctxt
    | None -> ()

  let get_decls ctxt = ctxt_fold (fun acc d -> d::acc) [] ctxt

  (* Use and clone *)

  let add_use ctxt th =
    let d = create_use th in
    try
      let kn = add_known ctxt.ctxt_known th.th_name d in
      let kn = merge_known kn th.th_ctxt.ctxt_known in
      push_kn_decl ctxt kn d
    with DejaVu ->
      ctxt

  let rec use_export ctxt th =
    let d = create_use th in
    try
      let kn = add_known ctxt.ctxt_known th.th_name d in
      let ctxt = push_kn_decl ctxt kn d in
      let add_decl ctxt d = match d.d_node with
        | Dtype _ | Dlogic _ | Dprop _ -> add_decl ctxt d
        | Duse th -> use_export ctxt th
        | Dclone _ -> push_decl ctxt d
      in
      let decls = get_decls th.th_ctxt in
      List.fold_left add_decl ctxt decls
    with DejaVu ->
      ctxt

  exception CannotInstantiate of ident

  let clone_theory th inst =
    let ts_table = Hts.create 17 in
    let ls_table = Hls.create 17 in
    let pr_table = Hashtbl.create 17 in
    let id_table = Hid.create 17 in

    let add_ts ts ts' =
      Hts.add ts_table ts ts';
      Hid.add id_table ts.ts_name ts'.ts_name
    in
    let add_ls ls ls' =
      Hls.add ls_table ls ls';
      Hid.add id_table ls.ls_name ls'.ls_name
    in
    Mts.iter add_ts inst.inst_ts;
    Mls.iter add_ls inst.inst_ls;

    let rec find_ts ts =
      if not (Sid.mem ts.ts_name th.th_local) then ts
      else try Hts.find ts_table ts
      with Not_found ->
        let td' = option_map trans_ty ts.ts_def in
        let ts' = create_tysymbol (id_dup ts.ts_name) ts.ts_args td' in
        add_ts ts ts';
        ts'

    and trans_ty ty = ty_s_map find_ts ty in

    let find_ls ls =
      if not (Sid.mem ls.ls_name th.th_local) then ls
      else try Hls.find ls_table ls
      with Not_found ->
        let ta' = List.map trans_ty ls.ls_args in
        let vt' = option_map trans_ty ls.ls_value in
        let ls' = create_lsymbol (id_dup ls.ls_name) ta' vt' ls.ls_constr in
        add_ls ls ls';
        ls'
    in
    let trans_fmla f = f_s_map find_ts find_ls f in

    let add_type acc (ts, def) =
      if Mts.mem ts inst.inst_ts then begin
        if ts.ts_def <> None || def <> Tabstract then
          raise (CannotInstantiate ts.ts_name);
        acc
      end else
        let ts' = find_ts ts in
        let def' = match def with
          | Tabstract -> Tabstract
          | Talgebraic ls -> Talgebraic (List.map find_ls ls)
        in
        (ts', def') :: acc
    in
    let add_logic acc = function
      | Lfunction (ls, Some _) | Lpredicate (ls, Some _) | Linductive (ls, _)
        when Mls.mem ls inst.inst_ls ->
          raise (CannotInstantiate ls.ls_name)
      | Lfunction (ls, Some (_,_,_,f)) ->
          let f' = trans_fmla f in
          let ls', def' = extract_fs_defn f' in
          Lfunction (ls', Some def') :: acc
      | Lpredicate (_, Some (_,_,_,f)) ->
          let f' = trans_fmla f in
          let ls', def' = extract_ps_defn f' in
          Lpredicate (ls', Some def') :: acc
      | Lfunction (ls, None) | Lpredicate (ls, None)
        when Mls.mem ls inst.inst_ls ->
          acc
      | Lfunction (ls, None) ->
          Lfunction (find_ls ls, None) :: acc
      | Lpredicate (ls, None) ->
          Lpredicate (find_ls ls, None) :: acc
      | Linductive (ls, fl) ->
          let trans (id, f) = (id, trans_fmla f) in
          Linductive (find_ls ls, List.map trans fl) :: acc
    in
    let add_prop acc k id f = match k with
      | Pgoal ->
          acc
      | Paxiom | Plemma ->
          let id' = id_dup id in
          let f' = trans_fmla f in
          let d' = create_prop Paxiom id' f' in
          let id' = match d'.d_node with
            | Dprop (_, id', _) -> id'
            | _ -> assert false
          in
          Hashtbl.add pr_table f.f_tag f';
          Hid.add id_table id id';
          d' :: acc
    in
    let add_decl acc d = match d.d_node with
      | Dtype tyl ->
          let l = List.fold_left add_type [] tyl in
          if l = [] then acc else create_type l :: acc
      | Dlogic ll ->
          let l = List.fold_left add_logic [] ll in
          if l = [] then acc else create_logic l :: acc
      | Dprop (k, id, f) ->
          add_prop acc k id f
      | Duse _ | Dclone _ ->
          d :: acc
    in
    let decls = ctxt_fold add_decl [] th.th_ctxt in
    ts_table, ls_table, pr_table, id_table, decls

  let add_final ctxt id_table =
    let add id id' acc = (id,id') :: acc in
    let d = create_clone (Hid.fold add id_table []) in
    push_decl ctxt d

  let add_clone ctxt th inst =
    let add_decl ctxt d = match d.d_node with
      | Dtype _ | Dlogic _ | Dprop _ -> add_decl ctxt d
      | Duse th  -> add_use ctxt th
      | Dclone _ -> push_decl ctxt d
    in
    let ts_t, ls_t, pr_t, id_t, decls = clone_theory th inst in
    let ctxt = List.fold_left add_decl ctxt decls in
    ts_t, ls_t, pr_t, add_final ctxt id_t

  let clone_export ctxt th inst =
    let add_decl ctxt d = match d.d_node with
      | Dtype _ | Dlogic _ | Dprop _ -> add_decl ctxt d
      | Duse th  -> use_export ctxt th
      | Dclone _ -> push_decl ctxt d
    in
    let _, _, _, id_t, decls = clone_theory th inst in
    let ctxt = List.fold_left add_decl ctxt decls in
    add_final ctxt id_t

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

  let add_to_ns x v m =
    if Mnm.mem x m then raise (ClashSymbol x);
    Mnm.add x v m

  let merge_ns ns1 ns2 =
    { ns_ts = Mnm.fold add_to_ns ns1.ns_ts ns2.ns_ts;
      ns_ls = Mnm.fold add_to_ns ns1.ns_ls ns2.ns_ls;
      ns_ns = Mnm.fold add_to_ns ns1.ns_ns ns2.ns_ns;
      ns_pr = Mnm.fold add_to_ns ns1.ns_pr ns2.ns_pr; }

  let add_ts x ts ns = { ns with ns_ts = add_to_ns x ts ns.ns_ts }
  let add_ls x fs ns = { ns with ns_ls = add_to_ns x fs ns.ns_ls }
  let add_pr x f  ns = { ns with ns_pr = add_to_ns x f  ns.ns_pr }
  let add_ns x v  ns = { ns with ns_ns = add_to_ns x v  ns.ns_ns }

  let add_symbol add id v uc =
    match uc.uc_import, uc.uc_export with
    | i0 :: sti, e0 :: ste -> { uc with
        uc_import = add id.id_short v i0 :: sti;
        uc_export = add id.id_short v e0 :: ste;
        uc_local  = Sid.add id uc.uc_local }
    | _ ->
        assert false

  let builtin_ns =
    let add fn = List.fold_right (fun (id,s,_) -> fn id.id_short s) in
    add add_ls builtin_logic (add add_ts builtin_type empty_ns)

  (* Manage theories *)

  let create_theory n = {
    uc_name   = n;
    uc_ctxt   = Context.empty_context;
    uc_import = [builtin_ns];
    uc_export = [empty_ns];
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

  let close_namespace uc s ~import =
    match uc.uc_import, uc.uc_export with
    | _ :: i1 :: sti, e0 :: e1 :: ste ->
        if Mnm.mem s i1.ns_ns then raise (ClashSymbol s);
        let i1 = if import then merge_ns e0 i1 else i1 in
        let i1 = { i1 with ns_ns = Mnm.add s e0 i1.ns_ns } in
        let e1 = { e1 with ns_ns = Mnm.add s e0 e1.ns_ns } in
        { uc with uc_import = i1 :: sti; uc_export = e1 :: ste; }
    | [_], [_] ->
        raise NoOpenedNamespace
    | _ ->
        assert false

  let use_export uc th =
    match uc.uc_import, uc.uc_export with
      | i0 :: sti, e0 :: ste -> { uc with
          uc_import = merge_ns th.th_export i0 :: sti;
          uc_export = merge_ns th.th_export e0 :: ste;
          uc_ctxt   = Context.add_use uc.uc_ctxt th }
      | _ ->
          assert false

  let clone_export uc th inst =
    let ts_t, ls_t, pr_t, ctxt = Context.add_clone uc.uc_ctxt th inst in
    let f_ts n ts acc = add_ts n (Hts.find ts_t ts) acc in
    let f_ls n ls acc = add_ls n (Hls.find ls_t ls) acc in
    let f_pr n f  acc = add_pr n (Hashtbl.find pr_t f.f_tag) acc in

    let rec merge_namespace acc ns =
      let acc = Mnm.fold f_ts ns.ns_ts acc in
      let acc = Mnm.fold f_ls ns.ns_ls acc in
      let acc = Mnm.fold f_pr ns.ns_pr acc in
      let acc = Mnm.fold f_ns ns.ns_ns acc in acc

    and f_ns n ns acc = add_ns n (merge_namespace empty_ns ns) acc in

    let ns = merge_namespace empty_ns th.th_export in
    match uc.uc_import, uc.uc_export with
      | i0 :: sti, e0 :: ste -> { uc with
              uc_import = merge_ns ns i0 :: sti;
              uc_export = merge_ns ns e0 :: ste;
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
    | Linductive (ps, la) ->
        let uc = add_symbol add_ls ps.ls_name ps uc in
        let add uc (id,f) = add_symbol add_pr id f uc in
        List.fold_left add uc la

  let add_decl uc d =
    let uc = match d.d_node with
      | Dtype dl  -> List.fold_left add_type uc dl
      | Dlogic dl -> List.fold_left add_logic uc dl
      | Dprop (_, id, f) -> add_symbol add_pr id f uc
      | Dclone _ | Duse _ -> assert false
    in
    { uc with uc_ctxt = Context.add_decl uc.uc_ctxt d }

  let get_namespace uc = List.hd uc.uc_import

end

(** Debugging *)

let print_ident =
  let printer = create_printer () in
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
let print_th fmt th = fprintf fmt "<theory (TODO>"

