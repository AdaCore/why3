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

type error = 
  | OpenTheory
  | CloseTheory
  | NoOpenedTheory
  | NoOpenedNamespace
  | RedeclaredIdent
  | CannotInstantiate

exception Error of error

let error e = raise (Error e)

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
  | Use of t

and t = {
  t_name : ident;
  t_local : Sid.t;           (* locally declared abstract symbols *)
  t_known : Sid.t;           (* imported and locally declared symbols *)
  t_namespace : namespace;
  t_decls : decl_or_use list;
}

and namespace = {
  tysymbols : tysymbol M.t;  (* type symbols *)
  fsymbols  : fsymbol M.t;   (* function symbols *)
  psymbols  : psymbol M.t;   (* predicate symbols *)
  props     : fmla M.t;      (* formula *)
  namespace : namespace M.t;      
}

type th = {
  th_name  : ident;
  th_local : Sid.t;
  th_known : Sid.t;
  th_stack : (namespace * namespace) list; (* stack of imports/exports *)
  th_decls : decl_or_use list;
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
  th_name = n;
  th_local = Sid.empty;
  th_known = Sid.empty;
  th_stack = [empty_ns, empty_ns];
  th_decls = [];
}
  
let close_theory th = match th.th_stack with
  | [_, e] -> 
      { t_name = th.th_name;
        t_local = th.th_local;
        t_known = th.th_known;
        t_namespace = e;
        t_decls = List.rev th.th_decls; }
  | _ -> 
      error CloseTheory

let open_namespace th = match th.th_stack with
  | (i, _) :: _ as st ->
      { th with th_stack = (i, empty_ns) :: st }
  | [] ->
      assert false

let close_namespace th n ~import = match th.th_stack with
  | (_, e0) :: (i, e) :: st ->
      let s = n.id_short in
      let add ns = { ns with namespace = M.add s e0 ns.namespace } in
      { th with th_stack = (add i, add e) :: st }
  | [_] ->
      error NoOpenedNamespace
  | [] ->
      assert false

let use_export th t =
  assert false (* TODO *)

type th_inst = {
  inst_ts : tysymbol Mts.t;
  inst_fs : fsymbol  Mfs.t;
  inst_ps : psymbol  Mps.t;
}

let check_sym id t =
  if Sid.mem id t.t_local then () else error CannotInstantiate

let clone_export th t i =
  let check_ts s _ = check_sym s.ts_name t in
  let _ = Mts.iter check_ts i.inst_ts in
  let check_fs s _ = check_sym s.fs_name t in
  let _ = Mfs.iter check_fs i.inst_fs in
  let check_ps s _ = check_sym s.ps_name t in
  let _ = Mps.iter check_ps i.inst_ps in
  assert false (* TODO *)

let add_tysymbol x ty ns = { ns with tysymbols = M.add x ty ns.tysymbols }
let add_fsymbol x ty ns = { ns with fsymbols = M.add x ty ns.fsymbols }
let add_psymbol x ty ns = { ns with psymbols = M.add x ty ns.psymbols }

let add_ns add x v th = match th.th_stack with
  | (i, e) :: st -> 
      let x = x.id_short in (add x v i, add x v e) :: st
  | [] -> assert false

let add_known id th =
  let _ = if Sid.mem id th.th_known 
          then error RedeclaredIdent else ()
  in
  { th with th_known = Sid.add id th.th_known }

let add_local id th =
  let th = add_known id th in
  { th with th_local = Sid.add id th.th_local }

let add_decl th d = 
  let st = match d with
    | Dtype [ty, Ty_abstract] ->
        let th = add_local ty.ts_name th in
        add_ns add_tysymbol ty.ts_name ty th
    | Dlogic [Lfunction (fs, None)] ->
        let th = add_local fs.fs_name th in
        add_ns add_fsymbol fs.fs_name fs th
    | Dlogic [Lpredicate (ps, None)] ->
        let th = add_local ps.ps_name th in
        add_ns add_psymbol ps.ps_name ps th
    | _ ->
        assert false (* TODO *)
  in
  { th with 
      th_stack = st;
      th_decls = (Decl d) :: th.th_decls }

(** Querying environments *)

let get_namespace th = match th.th_stack with
  | (ns, _) :: _ -> ns
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

(** Error reporting *)

let report fmt = function
  | OpenTheory ->
      fprintf fmt "cannot open a new theory in a non-empty context"
  | CloseTheory ->
      fprintf fmt "cannot close theory: there are still unclosed namespaces"
  | NoOpenedTheory ->
      fprintf fmt "no opened theory"
  | NoOpenedNamespace ->
      fprintf fmt "no opened namespace"
  | RedeclaredIdent ->
      fprintf fmt "cannot redeclare identifiers"
  | CannotInstantiate ->
      fprintf fmt "cannot instantiate a defined symbol"

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
