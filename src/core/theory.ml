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
  | Lfunction  of fsymbol * fmla option
  | Lpredicate of psymbol * fmla option
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

  let eq_fd fs1 fd1 fs2 fd2 = fs1 == fs2 && match fd1,fd2 with
    | Some fd1, Some fd2 -> fd1 == fd2
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
    | _ -> false

  let hs_td (ts,td) = match td with
    | Tabstract -> ts.ts_name.id_tag
    | Talgebraic l ->
        let tag fs = fs.fs_name.id_tag in
        1 + Hashcons.combine_list tag ts.ts_name.id_tag l

  let hs_fd fd = Hashcons.combine_option (fun f -> f.f_tag) fd

  let hs_ld ld = match ld with
    | Lfunction  (fs,fd) -> Hashcons.combine fs.fs_name.id_tag (hs_fd fd)
    | Lpredicate (ps,pd) -> Hashcons.combine ps.ps_name.id_tag (hs_fd pd)
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

(* error reporting *)

exception NotAConstructor of fsymbol
exception IllegalTypeAlias of tysymbol
exception UnboundTypeVar of ident

exception IllegalConstructor of fsymbol
exception MalformedDefinition of fmla
exception UnboundVars of Svs.t

let make_fdef fs vl t =
  let hd = t_app fs (List.map t_var vl) t.t_ty in
  Lfunction  (fs, Some (f_forall vl [] (f_equ hd t)))

let make_pdef ps vl f =
  let hd = f_app ps (List.map t_var vl) in
  Lpredicate (ps, Some (f_forall vl [] (f_iff hd f)))

let create_type tdl =
  let check_constructor ty fs =
    if not fs.fs_constr then raise (NotAConstructor fs);
    let lty,rty = fs.fs_scheme in
    ignore (Ty.matching Mid.empty rty ty);
    let add s ty = match ty.ty_node with
      | Tyvar v -> Sid.add v s
      | _ -> assert false
    in
    let vs = ty_fold add Sid.empty rty in
    let rec check () ty = match ty.ty_node with
      | Tyvar v -> if not (Sid.mem v vs) then raise (UnboundTypeVar v)
      | _ -> ty_fold check () ty
    in
    List.iter (check ()) lty
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

let create_logic ldl =
  let check_fv f =
    let fvs = f_freevars Svs.empty f in
    if not (Svs.is_empty fvs) then raise (UnboundVars fvs);
  in
  let check_def fd =
    check_fv fd;
    match fd.f_node with
      | Fquant (Fforall, fq) -> f_open_quant fq
      | _ -> ([],[],fd)
  in
  let check_ax (_,f) =
    check_fv f;
    assert false (* TODO *)
  in
  let check_decl = function
    | Lfunction (fs, Some fd) ->
        if fs.fs_constr then raise (IllegalConstructor fs);
        let (vl,_,f) = check_def fd in
        let hd = match f.f_node with
          | Fapp (ps, [hd; _]) when ps == ps_equ -> hd
          | _ -> raise (MalformedDefinition fd)
        in
        let t = try t_app fs (List.map t_var vl) hd.t_ty with
          | _ -> raise (MalformedDefinition fd)
        in
        if t != hd then raise (MalformedDefinition fd)
    | Lpredicate (ps, Some pd) ->
        let (vl,_,f) = check_def pd in
        let hd = match f.f_node with
          | Fbinop (Fiff, hd, _) -> hd
          | _ -> raise (MalformedDefinition pd)
        in
        let f = try f_app ps (List.map t_var vl) with
          | _ -> raise (MalformedDefinition pd)
        in
        if f != hd then raise (MalformedDefinition pd)
    | Linductive (ps,la) ->
        List.iter check_ax la
    | _ -> ()
  in
  List.iter check_decl ldl;
  create_logic ldl

let create_prop k i f =
  let fvs = f_freevars Svs.empty f in
  if not (Svs.is_empty fvs) then raise (UnboundVars fvs);
  create_prop k i f


(** Theory *)

module Snm = Set.Make(String)
module Mnm = Map.Make(String)

type theory = {
  th_name   : ident;
  th_param  : Sid.t;        (* locally declared abstract symbols *)
  th_known  : ident Mid.t;  (* imported and locally declared symbols *)
  th_export : namespace;
  th_decls  : decl_or_use list;
}

and namespace = {
  ns_ts : tysymbol Mnm.t;   (* type symbols *)
  ns_fs : fsymbol Mnm.t;    (* function symbols *)
  ns_ps : psymbol Mnm.t;    (* predicate symbols *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
  ns_pr : fmla Mnm.t;       (* propositions *)
}

and decl_or_use =
  | Decl of decl
  | Use of theory


(** Theory under construction *)

type theory_uc = {
  uc_name   : ident;
  uc_param  : Sid.t;
  uc_known  : ident Mid.t;
  uc_import : namespace list;
  uc_export : namespace list;
  uc_decls  : decl_or_use list;
}


(** Error reporting *)

exception CloseTheory
exception NoOpenedNamespace
exception RedeclaredIdent of ident
exception UnknownIdent of ident
exception CannotInstantiate of ident
exception ClashSymbol of string


(** Manage known symbols *)

let known_id kn id =
  if not (Mid.mem id kn) then raise (UnknownIdent id)

let known_ts kn () ts = known_id kn ts.ts_name
let known_fs kn () fs = known_id kn fs.fs_name
let known_ps kn () ps = known_id kn ps.ps_name

let known_ty kn ty = ty_s_fold (known_ts kn) () ty
let known_term kn t = t_s_fold (known_ts kn) (known_fs kn) (known_ps kn) () t
let known_fmla kn f = f_s_fold (known_ts kn) (known_fs kn) (known_ps kn) () f

let merge_known kn1 kn2 =
  let add id tid kn =
    try
      if Mid.find id kn2 != tid then raise (RedeclaredIdent id);
      kn
    with Not_found -> Mid.add id tid kn
  in
  Mid.fold add kn1 kn2

let add_known id uc =
  if Mid.mem id uc.uc_known then raise (RedeclaredIdent id);
  { uc with uc_known = Mid.add id uc.uc_name uc.uc_known }


(** Manage namespaces *)

let empty_ns = {
  ns_ts = Mnm.empty;
  ns_fs = Mnm.empty;
  ns_ps = Mnm.empty;
  ns_ns = Mnm.empty;
  ns_pr = Mnm.empty;
}

let add_to_ns x v m =
  if Mnm.mem x m then raise (ClashSymbol x);
  Mnm.add x v m

let merge_ns ns1 ns2 =
  { ns_ts = Mnm.fold add_to_ns ns1.ns_ts ns2.ns_ts;
    ns_fs = Mnm.fold add_to_ns ns1.ns_fs ns2.ns_fs;
    ns_ps = Mnm.fold add_to_ns ns1.ns_ps ns2.ns_ps;
    ns_ns = Mnm.fold add_to_ns ns1.ns_ns ns2.ns_ns;
    ns_pr = Mnm.fold add_to_ns ns1.ns_pr ns2.ns_pr; }

let add_ts x ts ns = { ns with ns_ts = add_to_ns x ts ns.ns_ts }
let add_fs x fs ns = { ns with ns_fs = add_to_ns x fs ns.ns_fs }
let add_ps x ps ns = { ns with ns_ps = add_to_ns x ps ns.ns_ps }
let add_pr x f  ns = { ns with ns_pr = add_to_ns x f  ns.ns_pr }

let add_symbol add id v uc =
  let uc = add_known id uc in
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste ->
      let im = add id.id_short v i0 :: sti in
      let ex = add id.id_short v e0 :: ste in
      { uc with uc_import = im; uc_export = ex }
  | _ ->
      assert false

let get_namespace uc = List.hd uc.uc_import


(** Built-in symbols *)

let builtin_ts = [ts_int; ts_real]
let builtin_ps = [ps_equ; ps_neq]

let ts_name x = x.ts_name
let ps_name x = x.ps_name

let builtin_ns =
  let add adder name = List.fold_right (fun s -> adder (name s).id_short s) in
  let ns = add add_ts ts_name builtin_ts empty_ns in
  let ns = add add_ps ps_name builtin_ps ns in
  ns

let builtin_th = id_register (id_fresh "Builtin")

let builtin_known =
  let add name = List.fold_right (fun s -> Mid.add (name s) builtin_th) in
  let kn = Mid.add builtin_th builtin_th Mid.empty in
  let kn = add ts_name builtin_ts kn in
  let kn = add ps_name builtin_ps kn in
  kn


(** Manage theories *)

let create_theory n = {
  uc_name   = n;
  uc_param  = Sid.empty;
  uc_known  = Mid.add n n builtin_known;
  uc_import = [builtin_ns];
  uc_export = [empty_ns];
  uc_decls  = [];
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
    | i0 :: sti, e0 :: ste ->
        { uc with
            uc_import = merge_ns th.th_export i0 :: sti;
            uc_export = merge_ns th.th_export e0 :: ste;
            uc_known  = merge_known uc.uc_known th.th_known;
            uc_decls  = Use th :: uc.uc_decls;
        }
    | _ ->
        assert false


(** Manage new declarations *)

let add_param id uc = { uc with uc_param = Sid.add id uc.uc_param }

let add_type uc (ts,def) =
  let uc = add_symbol add_ts ts.ts_name ts uc in
  match def with
  | Tabstract ->
      if ts.ts_def == None then add_param ts.ts_name uc else uc
  | Talgebraic lfs ->
      let add_constr uc fs = add_symbol add_fs fs.fs_name fs uc in
      List.fold_left add_constr uc lfs

let check_type kn (ts,def) = match def with
  | Tabstract ->
      begin match ts.ts_def with
        | Some ty -> known_ty kn ty
        | None -> ()
      end
  | Talgebraic lfs ->
      let check fs = List.iter (known_ty kn) (fst fs.fs_scheme) in
      List.iter check lfs

let add_logic uc = function
  | Lfunction (fs, df) ->
      let uc = add_symbol add_fs fs.fs_name fs uc in
      if df == None then add_param fs.fs_name uc else uc
  | Lpredicate (ps, dp) ->
      let uc = add_symbol add_ps ps.ps_name ps uc in
      if dp == None then add_param ps.ps_name uc else uc
  | Linductive (ps, la) ->
      let uc = add_symbol add_ps ps.ps_name ps uc in
      let add uc (id,f) = add_symbol add_pr id f uc in
      List.fold_left add uc la

let check_logic kn = function
  | Lfunction (fs, df) ->
      known_ty kn (snd fs.fs_scheme);
      List.iter (known_ty kn) (fst fs.fs_scheme);
      begin match df with
        | Some f -> known_fmla kn f
        | None -> ()
      end
  | Lpredicate (ps, dp) ->
      List.iter (known_ty kn) ps.ps_scheme;
      begin match dp with
        | Some f -> known_fmla kn f
        | None -> ()
      end
  | Linductive (ps, la) ->
      List.iter (known_ty kn) ps.ps_scheme;
      let check (_,f) = known_fmla kn f in
      List.iter check la

let add_decl uc d =
  let uc = match d.d_node with
    | Dtype dl ->
        let uc = List.fold_left add_type uc dl in
        List.iter (check_type uc.uc_known) dl;
        uc
    | Dlogic dl ->
        let uc = List.fold_left add_logic uc dl in
        List.iter (check_logic uc.uc_known) dl;
        uc
    | Dprop (k, id, f) ->
        known_fmla uc.uc_known f;
        add_symbol add_pr id f uc
  in
  { uc with uc_decls = Decl d :: uc.uc_decls }


(** Clone theories *)

type th_inst = {
  inst_ts : tysymbol Mts.t;
  inst_fs : fsymbol  Mfs.t;
  inst_ps : psymbol  Mps.t;
}

let clone_export th t i =
  let check_sym id =
    if not (Sid.mem id t.th_param) then raise (CannotInstantiate id)
  in
  let check_ts s _ = check_sym s.ts_name in Mts.iter check_ts i.inst_ts;
  let check_fs s _ = check_sym s.fs_name in Mfs.iter check_fs i.inst_fs;
  let check_ps s _ = check_sym s.ps_name in Mps.iter check_ps i.inst_ps;
  assert false (* TODO *)


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
compile-command: "make -C ../.. test"
End:
*)
