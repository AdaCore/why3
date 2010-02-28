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
open Ident
open Ty
open Term

(** Declarations *)

(* type declaration *)

type ty_def =
  | Tabstract
  | Talgebraic of fsymbol list

type ty_decl = tysymbol * ty_def

(* logic declaration *)

type logic_decl =
  | Lfunction  of fsymbol * (vsymbol list * term) option (* FIXME: binders *)
  | Lpredicate of psymbol * (vsymbol list * fmla) option (* FIXME: binders *)
  | Linductive of psymbol * (ident * fmla) list

(* proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * ident * fmla

(* declaration *)

type decl_node =
  | Dtype  of ty_decl list
  | Dlogic of logic_decl list
  | Dprop  of prop_decl

type decl = {
  d_node : decl_node;
  d_tag  : int;
}

module D = struct

  type t = decl

  let for_all2 pr l1 l2 =
    try List.for_all2 pr l1 l2 with Invalid_argument _ -> false

  let eq_td (ts1,td1) (ts2,td2) = ts1 == ts2 && match td1,td2 with
    | Tabstract, Tabstract -> true
    | Talgebraic l1, Talgebraic l2 -> for_all2 (==) l1 l2
    | _ -> false

  let eq_fd fs1 fs2 fd1 fd2 = fs1 == fs2 && match fd1,fd2 with
    | None, None -> true
    | Some (l1,t1), Some (l2,t2) -> t1 == t2 && for_all2 (==) l1 l2
    | _ -> false

  let eq_ld ld1 ld2 = match ld1,ld2 with
    | Lfunction  (fs1,fd1), Lfunction  (fs2,fd2) -> eq_fd fs1 fs2 fd1 fd2
    | Lpredicate (ps1,pd1), Lpredicate (ps2,pd2) -> eq_fd ps1 ps2 pd1 pd2
    | Linductive (ps1,l1),  Linductive (ps2,l2)  -> ps1 == ps2 &&
        for_all2 (fun (i1,f1) (i2,f2) -> i1 == i2 && f1 == f2) l1 l2
    | _ -> false

  let equal d1 d2 = match d1.d_node, d2.d_node with
    | Dtype  l1, Dtype  l2 -> for_all2 eq_td l1 l2
    | Dlogic l1, Dlogic l2 -> for_all2 eq_ld l1 l2
    | Dprop (k1,i1,f1), Dprop (k2,i2,f2) -> k1 == k2 && i1 == i2 && f1 == f2
    | _ -> false

  let hs_td (ts,td) = match td with
    | Tabstract -> ts.ts_name.id_tag
    | Talgebraic l ->
        let tag fs = fs.fs_name.id_tag in
        1 + Hashcons.combine_list tag ts.ts_name.id_tag l

  let hs_ld ld = match ld with
    | Lfunction  (fs,fd) ->
        let tag vs = vs.vs_name.id_tag in
        let hsh (l,t) = Hashcons.combine_list tag t.t_tag l in
        Hashcons.combine fs.fs_name.id_tag (Hashcons.combine_option hsh fd)
    | Lpredicate (ps,pd) ->
        let tag vs = vs.vs_name.id_tag in
        let hsh (l,f) = Hashcons.combine_list tag f.f_tag l in
        Hashcons.combine ps.ps_name.id_tag (Hashcons.combine_option hsh pd)
    | Linductive (ps,l)  ->
        let hs_pair (i,f) = Hashcons.combine i.id_tag f.f_tag in
        Hashcons.combine_list hs_pair ps.ps_name.id_tag l

  let hash d = match d.d_node with
    | Dtype  l -> Hashcons.combine_list hs_td 0 l
    | Dlogic l -> Hashcons.combine_list hs_ld 1 l
    | Dprop (Paxiom,i,f) -> Hashcons.combine2 0 i.id_tag f.f_tag
    | Dprop (Plemma,i,f) -> Hashcons.combine2 1 i.id_tag f.f_tag
    | Dprop (Pgoal, i,f) -> Hashcons.combine2 2 i.id_tag f.f_tag

  let tag n d = { d with d_tag = n }

  let compare d1 d2 = Pervasives.compare d1.d_tag d2.d_tag

end
module Hdecl = Hashcons.Make(D)
module Mdecl = Map.Make(D)
module Sdecl = Set.Make(D)

(* smart constructors *)

let mk_decl n = { d_node = n; d_tag = -1 }

let create_type tdl = Hdecl.hashcons (mk_decl (Dtype tdl))
let create_logic ldl = Hdecl.hashcons (mk_decl (Dlogic ldl))
let create_prop k i f = Hdecl.hashcons (mk_decl (Dprop (k, id_register i, f)))


(** Theory *)

module Snm = Set.Make(String)
module Mnm = Map.Make(String)

type theory = {
  th_name   : ident;
  th_param  : Sid.t;          (* locally declared abstract symbols *)
  th_known  : ident Mid.t;    (* imported and locally declared symbols *)
  th_export : namespace;
  th_decls  : decl_or_use list;
}

and namespace = {
  ns_ts   : tysymbol Mnm.t;   (* type symbols *)
  ns_fs   : fsymbol Mnm.t;    (* function symbols *)
  ns_ps   : psymbol Mnm.t;    (* predicate symbols *)
  ns_ns   : namespace Mnm.t;  (* inner namespaces *)
  ns_prop : fmla Mnm.t;       (* propositions *)
}

and decl_or_use =
  | Decl of decl
  | Use of theory


(** Error reporting *)

exception CloseTheory
exception NoOpenedNamespace
exception RedeclaredIdent of ident
exception CannotInstantiate
exception ClashSymbol of string


(** Theory under construction *)

type theory_uc = {
  uc_name   : ident;
  uc_param  : Sid.t;
  uc_known  : ident Mid.t;
  uc_visible: namespace list; (* stack of visible symbols *)
  uc_import : namespace list;
  uc_export : namespace list;
  uc_decls  : decl_or_use list;
}

(* creating environments *)

let empty_ns = {
  ns_ts   = Mnm.empty;
  ns_fs   = Mnm.empty;
  ns_ps   = Mnm.empty;
  ns_ns   = Mnm.empty;
  ns_prop = Mnm.empty;
}

let create_theory n = {
  uc_name     = n;
  uc_param    = Sid.empty;
  uc_known    = Mid.add n n Mid.empty;
  uc_visible  = [empty_ns];
  uc_import   = [empty_ns];
  uc_export   = [empty_ns];
  uc_decls    = [];
}

let create_theory n = create_theory (id_register n)

let close_theory uc = match uc.uc_export with
  | [e] ->
      { th_name   = uc.uc_name;
        th_param  = uc.uc_param;
        th_known  = uc.uc_known;
        th_export = e;
        th_decls  = List.rev uc.uc_decls; }
  | _ ->
      raise CloseTheory

let open_namespace uc = match uc.uc_visible with
  | ns :: _ as st ->
      { uc with
	  uc_visible = ns :: st;
	  uc_import  = empty_ns :: uc.uc_import;
	  uc_export  = empty_ns :: uc.uc_export; }
  | [] ->
      assert false

let merge_ns ~check ns1 ns2 =
  let add k v m =
    if check && Mnm.mem k m then raise (ClashSymbol k);
    Mnm.add k v m
  in
  { ns_ts   = Mnm.fold add ns1.ns_ts ns2.ns_ts;
    ns_fs   = Mnm.fold add ns1.ns_fs ns2.ns_fs;
    ns_ps   = Mnm.fold add ns1.ns_ps ns2.ns_ps;
    ns_ns   = Mnm.fold add ns1.ns_ns ns2.ns_ns;
    ns_prop = Mnm.fold add ns1.ns_prop ns2.ns_prop; }

let close_namespace uc s ~import =
  match uc.uc_visible, uc.uc_import, uc.uc_export with
  | _ :: v1 :: stv, _ :: i1 :: sti, e0 :: e1 :: ste ->
      if Mnm.mem s i1.ns_ns then raise (ClashSymbol s);
      let v1 = { v1 with ns_ns = Mnm.add s e0 v1.ns_ns } in
      let i1 = { i1 with ns_ns = Mnm.add s e0 i1.ns_ns } in
      let e1 = { e1 with ns_ns = Mnm.add s e0 e1.ns_ns } in
      let v1 = if import then merge_ns ~check:false e0 v1 else v1 in
      let i1 = if import then merge_ns ~check:true  e0 i1 else i1 in
      { uc with
          uc_visible = v1 :: stv;
          uc_import = i1 :: sti;
          uc_export = e1 :: ste; }
  | [_], [_], [_] ->
      raise NoOpenedNamespace
  | _ ->
      assert false

let merge_known m1 m2 =
  let add k i m =
    try
      if Mid.find k m2 != i then raise (RedeclaredIdent i);
      m
    with Not_found -> Mid.add k i m
  in
  Mid.fold add m1 m2

let use_export uc th =
  match uc.uc_visible, uc.uc_import, uc.uc_export with
    | v0 :: stv, i0 :: sti, e0 :: ste ->
	{ uc with
	    uc_visible = merge_ns ~check:false th.th_export v0 :: stv;
	    uc_import  = merge_ns ~check:true  th.th_export i0 :: sti;
	    uc_export  = merge_ns ~check:false th.th_export e0 :: ste;
	    uc_known   = merge_known uc.uc_known th.th_known;
	}
    | _ ->
	assert false

type th_inst = {
  inst_ts : tysymbol Mts.t;
  inst_fs : fsymbol  Mfs.t;
  inst_ps : psymbol  Mps.t;
}

let check_sym id t =
  if not (Sid.mem id t.th_param) then raise CannotInstantiate

let clone_export th t i =
  let check_ts s _ = check_sym s.ts_name t in
  Mts.iter check_ts i.inst_ts;
  let check_fs s _ = check_sym s.fs_name t in
  Mfs.iter check_fs i.inst_fs;
  let check_ps s _ = check_sym s.ps_name t in
  Mps.iter check_ps i.inst_ps;
  assert false (* TODO *)

let check_fmla k f =
  () (* TODO *)

let generic_add ~check x v m =
  if check && Mnm.mem x m then raise (ClashSymbol x);
  Mnm.add x v m

let add_tysymbol ~check x ty ns =
  { ns with ns_ts = generic_add ~check x ty ns.ns_ts }

let add_fsymbol ~check x ty ns =
  { ns with ns_fs = generic_add ~check x ty ns.ns_fs }

let add_psymbol ~check x ty ns =
  { ns with ns_ps = generic_add ~check x ty ns.ns_ps }

let add_prop ~check x v ns =
  { ns with ns_prop = generic_add ~check x v ns.ns_prop }

let add_symbol add x v uc =
  match uc.uc_visible, uc.uc_import, uc.uc_export with
  | v0 :: stv, i0 :: sti, e0 :: ste ->
      let x = x.id_short in
      { uc with
	  uc_visible = add ~check:false x v v0 :: stv;
	  uc_import  = add ~check:true  x v i0 :: sti;
	  uc_export  = add ~check:false x v e0 :: ste }

  | _ ->
      assert false

let add_known id uc =
  if Mid.mem id uc.uc_known then raise (RedeclaredIdent id);
  { uc with uc_known = Mid.add id uc.uc_name uc.uc_known }

let add_param id uc =
  let uc = add_known id uc in
  { uc with uc_param = Sid.add id uc.uc_param }

let add_type uc (ts, def) = match def with
  | Tabstract ->
      let uc = match ts.ts_def with
        | Some _ -> add_known ts.ts_name uc
        | None   -> add_param ts.ts_name uc
      in
      add_symbol add_tysymbol ts.ts_name ts uc
  | Talgebraic _ ->
      assert false (*TODO*)

let add_logic uc = function
  | Lfunction (fs, df) ->
      let uc = match df with
        | Some _  -> add_known fs.fs_name uc
        | None    -> add_param fs.fs_name uc
      in
      add_symbol add_fsymbol fs.fs_name fs uc
  | Lpredicate (ps, dp) ->
      let uc = match dp with
        | Some _  -> add_known ps.ps_name uc
        | None    -> add_param ps.ps_name uc
      in
      add_symbol add_psymbol ps.ps_name ps uc
  | Linductive (ps, dp) ->
      let uc = add_known ps.ps_name uc in
      let uc = add_symbol add_psymbol ps.ps_name ps uc in
      assert false (*TODO*)

let add_decl uc d =
  let uc = match d.d_node with
    | Dtype dl ->
	List.fold_left add_type uc dl
    | Dlogic dl ->
	List.fold_left add_logic uc dl
    | Dprop (k, id, f) ->
	check_fmla uc.uc_known f;
	let uc = add_known id uc in
	add_symbol add_prop id f uc
  in
  { uc with uc_decls = Decl d :: uc.uc_decls }

(** Querying environments *)

let get_namespace th = match th.uc_visible with
  | ns :: _ -> ns
  | [] -> assert false

(*
let find_tysymbol  ns s = Mnm.find s ns.ns_ts
let find_fsymbol   ns s = Mnm.find s ns.ns_fs
let find_psymbol   ns s = Mnm.find s ns.ns_ps
let find_namespace ns s = Mnm.find s ns.ns_ns
let find_prop      ns s = Mnm.find s ns.ns_prop

let mem_tysymbol  ns s = Mnm.mem s ns.ns_ts
let mem_fsymbol   ns s = Mnm.mem s ns.ns_fs
let mem_psymbol   ns s = Mnm.mem s ns.ns_ps
let mem_namespace ns s = Mnm.mem s ns.ns_ns
let mem_prop      ns s = Mnm.mem s ns.ns_prop
*)

(** Debugging *)

let print_ident =
  let printer = create_printer () in
  let print fmt id = Format.fprintf fmt "%s" (id_unique printer id) in
  print

let rec print_namespace fmt ns =
  fprintf fmt "@[<hov 2>types: ";
  Mnm.iter (fun x ty -> fprintf fmt "%s -> %a;@ " x print_ident ty.ts_name)
    ns.ns_ts;
  fprintf fmt "@]@\n@[<hov 2>function symbols: ";
  Mnm.iter (fun x s -> fprintf fmt "%s -> %a;@ " x print_ident s.fs_name)
    ns.ns_fs;
  fprintf fmt "@]@\n@[<hov 2>predicate symbols: ";
  Mnm.iter (fun x s -> fprintf fmt "%s -> %a;@ " x print_ident s.ps_name)
    ns.ns_ps;
  fprintf fmt "@]@\n@[<hov 2>namespace: ";
  Mnm.iter (fun x th -> fprintf fmt "%s -> [@[%a@]];@ " x print_namespace th)
    ns.ns_ns;
  fprintf fmt "@]"

let print_th fmt th =
  print_namespace fmt (get_namespace th)

let print_t fmt t =
  fprintf fmt "<theory (TODO>"

(*
Local Variables:
compile-command: "make -C .. test"
End:
*)
