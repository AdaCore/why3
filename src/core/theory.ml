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

(** Error reporting *)

exception CloseTheory
exception NoOpenedNamespace
exception RedeclaredIdent of ident
exception CannotInstantiate
exception ClashSymbol of string

(** The environment type *)

module M = Map.Make(String)

type ty_def = 
  | Ty_abstract
  | Ty_algebraic of fsymbol list

type ty_decl = tysymbol * ty_def 

type logic_decl = 
  | Lfunction  of fsymbol * (vsymbol list * term) option (* FIXME: binders *)
  | Lpredicate of psymbol * (vsymbol list * fmla) option (* FIXME: binders *)
  | Linductive of psymbol * (ident * fmla) list

type prop_kind = 
  | Axiom | Lemma | Goal

type decl =
  | Dtype  of ty_decl list
  | Dlogic of logic_decl list
  | Dprop  of prop_kind * ident * fmla

type decl_or_use =
  | Decl of decl
  | Use of theory

and theory = {
  th_name      : ident;
  th_param     : Sid.t;           (* locally declared abstract symbols *)
  th_known     : ident Mid.t;     (* imported and locally declared symbols *)
  th_export    : namespace;
  th_decls     : decl_or_use list;
}

and namespace = {
  tysymbols : tysymbol M.t;  (* type symbols *)
  fsymbols  : fsymbol M.t;   (* function symbols *)
  psymbols  : psymbol M.t;   (* predicate symbols *)
  props     : fmla M.t;      (* formula *)
  namespace : namespace M.t;      
}

type theory_uc = {
  uc_name   : ident;
  uc_param  : Sid.t;
  uc_known  : ident Mid.t;
  uc_visible: namespace list; (* stack of visible symbols *)
  uc_import : namespace list;
  uc_export : namespace list;
  uc_decls  : decl_or_use list;
}

(** Creating environments *)

let empty_ns = {
  tysymbols = M.empty;
  fsymbols  = M.empty;
  psymbols  = M.empty;
  props     = M.empty;
  namespace = M.empty;
}

let create_theory n = {
  uc_name  = n;
  uc_param = Sid.empty;
  uc_known = Mid.add n n Mid.empty;
  uc_visible = [empty_ns];
  uc_import = [empty_ns];
  uc_export = [empty_ns];
  uc_decls = [];
}
  
let close_theory th = match th.uc_export with
  | [e] -> 
      { th_name   = th.uc_name;
        th_param  = th.uc_param;
        th_known  = th.uc_known;
        th_export = e;
        th_decls  = List.rev th.uc_decls; }
  | _ -> 
      raise CloseTheory

let open_namespace th = match th.uc_visible with
  | ns :: _ as st ->
      { th with 
	  uc_visible = ns :: st;
	  uc_import  = empty_ns :: th.uc_import;
	  uc_export  = empty_ns :: th.uc_export; }
  | [] ->
      assert false

let fusion ~check ns1 ns2 =
  let merge_ns m1 m2 =
    M.fold 
      (fun k1 v1 m2 -> 
	 if check && M.mem k1 m2 then raise (ClashSymbol k1);
	 M.add k1 v1 m2) 
      m1 m2
  in
  { tysymbols = merge_ns ns1.tysymbols ns2.tysymbols;
    fsymbols  = merge_ns ns1.fsymbols  ns2.fsymbols;
    psymbols  = merge_ns ns1.psymbols  ns2.psymbols;
    props     = merge_ns ns1.props     ns2.props;
    namespace = merge_ns ns1.namespace ns2.namespace; }

let add_known id uc =
  if Mid.mem id uc.uc_known then raise (RedeclaredIdent id);
  { uc with uc_known = Mid.add id uc.uc_name uc.uc_known }

let close_namespace uc n ~import = 
  match uc.uc_visible, uc.uc_import, uc.uc_export with
  | v0 :: v1 :: stv, i0 :: i1 :: sti, e0 :: e1 :: ste ->
      let s = n.id_short in
      let add ~check ns1 ns2 = 
	if check && M.mem s ns2.namespace then raise (ClashSymbol s);
	{ ns2 with namespace = M.add s ns1 ns2.namespace } 
      in
      let v1 = add ~check:false v0 v1 in
      let i1 = add ~check:true  i0 i1 in
      let e1 = add ~check:false e0 e1 in
      let v1 = if import then fusion ~check:false v0 v1 else v1 in
      let i1 = if import then fusion ~check:true  i0 i1 else i1 in
      add_known n 
	{ uc with 
	    uc_visible = v1 :: stv; 
	    uc_import = i1 :: sti; 
	    uc_export = e1 :: ste; }
  | [_], [_], [_] ->
      raise NoOpenedNamespace
  | _ ->
      assert false

let merge_known m1 m2 =
  Mid.fold 
    (fun k1 id1 m -> 
       try
	 let id2 = Mid.find k1 m2 in
	 if id1 != id2 then raise (RedeclaredIdent id1);
	 m
       with Not_found -> 
	 Mid.add k1 id1 m) 
    m1 m2

let use_export uc th =
  match uc.uc_visible, uc.uc_import, uc.uc_export with
    | v0 :: stv, i0 :: sti, e0 :: ste ->
	{ uc with 
	    uc_visible = fusion ~check:false th.th_export v0 :: stv; 
	    uc_import  = fusion ~check:true  th.th_export i0 :: sti; 
	    uc_export  = fusion ~check:false th.th_export e0 :: ste;
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
  if check && M.mem x m then raise (ClashSymbol x);
  M.add x v m

let add_tysymbol ~check x ty ns = 
  { ns with tysymbols = generic_add ~check x ty ns.tysymbols }
let add_fsymbol ~check x ty ns = 
  { ns with fsymbols = generic_add ~check x ty ns.fsymbols }
let add_psymbol ~check x ty ns = 
  { ns with psymbols = generic_add ~check x ty ns.psymbols }
let add_prop ~check x v ns =
  { ns with props = generic_add ~check x v ns.props }

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

let add_param id uc =
  let uc = add_known id uc in
  { uc with uc_param = Sid.add id uc.uc_param }

let add_type uc (ty, def) = match def with
  | Ty_abstract ->
      let uc = add_param ty.ts_name uc in
      add_symbol add_tysymbol ty.ts_name ty uc
  | Ty_algebraic _ ->
      assert false (*TODO*)

let add_logic uc = function
  | Lfunction (fs, _) ->
      let uc = add_param fs.fs_name uc in
      add_symbol add_fsymbol fs.fs_name fs uc
  | Lpredicate (ps, _) ->
      let uc = add_param ps.ps_name uc in
      add_symbol add_psymbol ps.ps_name ps uc
  | Linductive _ ->
      assert false (*TODO*)

let add_decl uc d = 
  let uc = match d with
    | Dtype dl ->
	List.fold_left add_type uc dl
    | Dlogic dl ->
	List.fold_left add_logic uc dl
    | Dprop (k, id, f) ->
	check_fmla uc.uc_known f;
	let uc = add_known id uc in
	add_symbol add_prop id f uc
  in
  { uc with uc_decls = (Decl d) :: uc.uc_decls }

(** Querying environments *)

let get_namespace th = match th.uc_visible with
  | ns :: _ -> ns
  | [] -> assert false

let find_tysymbol  ns s = M.find s ns.tysymbols
let find_fsymbol   ns s = M.find s ns.fsymbols
let find_psymbol   ns s = M.find s ns.psymbols
let find_namespace ns s = M.find s ns.namespace
let find_prop      ns s = M.find s ns.props

let mem_tysymbol  ns s = M.mem s ns.tysymbols
let mem_fsymbol   ns s = M.mem s ns.fsymbols
let mem_psymbol   ns s = M.mem s ns.psymbols
let mem_namespace ns s = M.mem s ns.namespace
let mem_prop      ns s = M.mem s ns.props

(** Debugging *)

let print_ident =
  let printer = create_printer () in
  let print fmt id = Format.fprintf fmt "%s" (id_unique printer id) in
  print

let rec print_namespace fmt ns =
  fprintf fmt "@[<hov 2>types: ";
  M.iter (fun x ty -> fprintf fmt "%s -> %a;@ " x print_ident ty.ts_name)
    ns.tysymbols;
  fprintf fmt "@]@\n@[<hov 2>function symbols: ";
  M.iter (fun x s -> fprintf fmt "%s -> %a;@ " x print_ident s.fs_name)
    ns.fsymbols;
  fprintf fmt "@]@\n@[<hov 2>predicate symbols: ";
  M.iter (fun x s -> fprintf fmt "%s -> %a;@ " x print_ident s.ps_name)
    ns.psymbols;
  fprintf fmt "@]@\n@[<hov 2>namespace: ";
  M.iter (fun x th -> fprintf fmt "%s -> [@[%a@]];@ " x print_namespace th)
    ns.namespace;
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
