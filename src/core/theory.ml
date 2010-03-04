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

(* proposition declaration *)

type prop_kind =
  | Paxiom
  | Plemma
  | Pgoal

type prop_decl = prop_kind * ident * fmla

(* declaration *)

(** Theory *)

module Snm = Set.Make(String)
module Mnm = Map.Make(String)

type theory = {
  th_name   : ident;
  th_param  : Sid.t;        (* locally declared abstract symbols *)
  th_export : namespace;
  th_ctxt   : ctxt;
}

and ctxt = {
  ctxt_tag   : int;
  ctxt_known : decl Mid.t;  (* imported and locally declared symbols *)
  ctxt_decls : (decl * ctxt) option;
}

and namespace = {
  ns_ts : tysymbol Mnm.t;   (* type symbols *)
  ns_ls : lsymbol Mnm.t;    (* logic symbols *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
  ns_pr : fmla Mnm.t;       (* propositions *)
}

and decl_node =
  | Dtype  of ty_decl list
  | Dlogic of logic_decl list
  | Dprop  of prop_decl
  | Duse of theory
  | Dclone of (ident * ident) list


and decl = {
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
    | Dprop (Paxiom,i,f) -> Hashcons.combine2 7 i.id_tag f.f_tag
    | Dprop (Plemma,i,f) -> Hashcons.combine2 11 i.id_tag f.f_tag
    | Dprop (Pgoal, i,f) -> Hashcons.combine2 13 i.id_tag f.f_tag
    | Duse th -> 17 * th.th_name.id_tag
    | Dclone sl -> Hashcons.combine_list
        (fun (i1,i2) -> Hashcons.combine i1.id_tag i2.id_tag)
          19 sl
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

exception ConstructorExpected of lsymbol
exception IllegalTypeAlias of tysymbol
exception UnboundTypeVar of ident

exception IllegalConstructor of lsymbol
exception UnboundVars of Svs.t
exception BadDecl of ident

let check_fvs f =
  let fvs = f_freevars Svs.empty f in
  if Svs.is_empty fvs then f else raise (UnboundVars fvs)

let make_fs_defn fs vl t =
  if fs.ls_constr then raise (IllegalConstructor fs);
  let hd = t_app fs (List.map t_var vl) t.t_ty in
  let fd = f_forall vl [] (f_equ hd t) in
  fs, vl, t, check_fvs fd

let make_ps_defn ps vl f =
  let hd = f_app ps (List.map t_var vl) in
  let pd = f_forall vl [] (f_iff hd f) in
  ps, vl, f, check_fvs pd

let open_fs_defn (fs,vl,t,_) = (fs,vl,t)
let open_ps_defn (ps,vl,f,_) = (ps,vl,f)

let fs_defn_axiom (_,_,_,fd) = fd
let ps_defn_axiom (_,_,_,pd) = pd

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

let create_logic ldl =
  let check_decl = function
    | Lfunction (fs, Some (s,_,_,_)) when s != fs ->
        raise (BadDecl fs.ls_name)
    | Lpredicate (ps, Some (s,_,_,_)) when s != ps ->
        raise (BadDecl ps.ls_name)
    | Linductive (ps,la) ->
        let check_ax (_,f) =
          ignore (check_fvs f);
          assert false (* TODO *)
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



(** Theory under construction *)

type theory_uc = {
  uc_name   : ident;
  uc_param  : Sid.t;
  uc_import : namespace list;
  uc_export : namespace list;
  uc_ctxt   : ctxt;
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
let known_ls kn () ls = known_id kn ls.ls_name

let known_ty kn ty = ty_s_fold (known_ts kn) () ty
let known_term kn t = t_s_fold (known_ts kn) (known_ls kn) () t
let known_fmla kn f = f_s_fold (known_ts kn) (known_ls kn) () f

let merge_known kn1 kn2 =
  let add id tid kn =
    try
      if Mid.find id kn2 != tid then raise (RedeclaredIdent id);
      kn
    with Not_found -> Mid.add id tid kn
  in
  Mid.fold add kn1 kn2

(** Manage namespaces *)

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

let add_symbol add id v uc =
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
let builtin_type = 
  List.map (fun ts -> ts.ts_name, ts, create_type [ts, Tabstract]) builtin_ts
let builtin_ls = [ps_equ; ps_neq]
let builtin_logic = 
  List.map (fun ls -> ls.ls_name, ls, create_logic [Lpredicate (ls, None)]) 
    builtin_ls

let builtin_ns =
  let add adder = List.fold_right (fun (id,s,_) -> adder id.id_short s) in
  let ns = add add_ts builtin_type empty_ns in
  let ns = add add_ls builtin_logic ns in
  ns

let builtin_th = id_register (id_fresh "Builtin")

let builtin_known =
  let add l = List.fold_right (fun (n,_,d) -> Mid.add n d) l in
  let kn = Mid.empty in
  let kn = add builtin_type kn in
  let kn = add builtin_logic kn in
  kn


(** Manage theories *)

module Ctxt =
  struct
    type t = ctxt
    let hash ctxt = match ctxt.ctxt_decls with
      | None -> 0
      | Some (d,n) -> 1 + (Hashcons.combine n.ctxt_tag d.d_tag)

    let equal a b = match a.ctxt_decls, b.ctxt_decls with
      | None, None -> 
	  true
      | Some (da, na), Some (db, nb) -> 
	  na.ctxt_decls == nb.ctxt_decls && da.d_tag == db.d_tag
      | _ -> 
	  false

    let tag i ctxt = {ctxt with ctxt_tag = i}
  end

module Hctxt = Hashcons.Make(Ctxt)

let empty_ctxt = Hctxt.hashcons {
  ctxt_tag   = -1;
  ctxt_known = builtin_known;
  ctxt_decls = None;
}

module Context = struct

  let add_known ctxt id decl =
    try
      let d = Mid.find id ctxt.ctxt_known in
      if d != decl then raise (RedeclaredIdent id);
      ctxt
    with Not_found ->
      { ctxt with ctxt_known = Mid.add id decl ctxt.ctxt_known }

  let check_type kn (ts,def) = match def with
    | Tabstract ->
	begin match ts.ts_def with
          | Some ty -> known_ty kn ty
          | None -> ()
	end
    | Talgebraic lfs ->
	let check fs = List.iter (known_ty kn) fs.ls_args in
	List.iter check lfs

  let add_type d ctxt (ts,def) =
    let ctxt = add_known ctxt ts.ts_name d in
    match def with
      | Tabstract ->
	  ctxt
      | Talgebraic lfs ->
	  let add_constr ctxt fs = add_known ctxt fs.ls_name d in
	  List.fold_left add_constr ctxt lfs

  let check_logic kn = function
    | Lfunction (fs, df) ->
	known_ty kn (of_option fs.ls_value);
	List.iter (known_ty kn) fs.ls_args;
	begin match df with
          | Some (_,_,t,_) -> known_term kn t
          | None -> ()
	end
    | Lpredicate (ps, dp) ->
	List.iter (known_ty kn) ps.ls_args;
	begin match dp with
          | Some (_,_,f,_) -> known_fmla kn f
          | None -> ()
	end
    | Linductive (ps, la) ->
	List.iter (known_ty kn) ps.ls_args;
	let check (_,f) = known_fmla kn f in
	List.iter check la

  let add_logic d ctxt = function
    | Lfunction (fs, df) ->
	add_known ctxt fs.ls_name d
    | Lpredicate (ps, dp) ->
	add_known ctxt ps.ls_name d
    | Linductive (ps, la) ->
	let ctxt = add_known ctxt ps.ls_name d in
	let add ctxt (id,f) = add_known ctxt id d in
	List.fold_left add ctxt la

  let add_decl ctxt d =
    let ctxt = match d.d_node with
      | Duse th ->
	  let kn = merge_known ctxt.ctxt_known th.th_ctxt.ctxt_known in
	  { ctxt with ctxt_known = kn }
      | Dtype dl ->
          let ctxt = List.fold_left (add_type d) ctxt dl in
          List.iter (check_type ctxt.ctxt_known) dl;
          ctxt
      | Dlogic dl ->
          let ctxt = List.fold_left (add_logic d) ctxt dl in
          List.iter (check_logic ctxt.ctxt_known) dl;
          ctxt
      | Dprop (k, id, f) ->
          known_fmla ctxt.ctxt_known f;
          add_known ctxt id d
      | Dclone _ -> 
	  assert false (* TODO *)
    in
    Hctxt.hashcons { ctxt with ctxt_decls = Some (d, ctxt) }

  let rec iter f c = match c.ctxt_decls with
    | None -> ()
    | Some (d, ctxt) -> iter f ctxt; f d
 
  let rec fold_left f acc c = match c.ctxt_decls with
    | None -> acc
    | Some (d, ctxt) -> let acc = fold_left f acc ctxt in f acc d

end


(* theories *)

let create_theory n = {
  uc_name   = n;
  uc_param  = Sid.empty;
  uc_import = [builtin_ns];
  uc_export = [empty_ns];
  uc_ctxt   = empty_ctxt;
}

let create_theory n = create_theory (id_register n)

let close_theory uc = match uc.uc_export with
  | [e] ->
      { th_name   = uc.uc_name;
        th_param  = uc.uc_param;
        th_export = e;
        th_ctxt   = uc.uc_ctxt; }
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
	let ctxt = Context.add_decl uc.uc_ctxt (mk_decl (Duse th)) in
        { uc with
            uc_import = merge_ns th.th_export i0 :: sti;
            uc_export = merge_ns th.th_export e0 :: ste;
            uc_ctxt   = ctxt;
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
      let add_constr uc fs = add_symbol add_ls fs.ls_name fs uc in
      List.fold_left add_constr uc lfs

let add_logic uc = function
  | Lfunction (fs, df) ->
      let uc = add_symbol add_ls fs.ls_name fs uc in
      if df == None then add_param fs.ls_name uc else uc
  | Lpredicate (ps, dp) ->
      let uc = add_symbol add_ls ps.ls_name ps uc in
      if dp == None then add_param ps.ls_name uc else uc
  | Linductive (ps, la) ->
      let uc = add_symbol add_ls ps.ls_name ps uc in
      let add uc (id,f) = add_symbol add_pr id f uc in
      List.fold_left add uc la

(** Clone theories *)

type th_inst = {
  inst_ts : tysymbol Mts.t;
  inst_ls : lsymbol  Mls.t;
}

(***
let clone_export uc th i =
  let check_sym id =
    if not (Sid.mem id th.th_param) then raise (CannotInstantiate id)
  in
  let check_ts s _ = check_sym s.ts_name in Mts.iter check_ts i.inst_ts;
  let check_ls s _ = check_sym s.ls_name in Mls.iter check_ls i.inst_ls;
  (* memo tables *)
  let ts_table = Hashtbl.create 17 in
  let known = ref th.th_known in
  let rec memo_ts ts =
    try
      Hashtbl.find ts_table ts.ts_name
    with Not_found ->
      let nm = id_clone ts.ts_name in
      let def = match ts.ts_def with
	| None -> None
	| Some ty -> Some (ty_s_map memo_ts ty)
      in
      let ts' = create_tysymbol nm ts.ts_args def in
      Hashtbl.add ts_table ts.ts_name ts';
      known := Mid.add ts'.ts_name uc.uc_name (Mid.remove ts.ts_name !known);
      ts'
  in
  let find_ts ts =
    let tid = Mid.find ts.ts_name th.th_known in
    if tid == th.th_name then memo_ts ts else ts
  in
  (* 1. merge in the new namespace *)
  let rec merge_namespace acc ns =
    let acc =
      Mnm.fold (fun n ts acc -> add_ts n (find_ts ts) acc) ns.ns_ts acc
    in
    (* ... *)
    (* let acc = Mnm.fold (fun n ns acc -> ) ns.ns_ns acc in *)
    acc
  in
  let ns = merge_namespace empty_ns th.th_export in
  let uc = match uc.uc_import, uc.uc_export with
    | i0 :: sti, e0 :: ste ->
        { uc with
            uc_import = merge_ns ns i0 :: sti;
            uc_export = merge_ns ns e0 :: ste;
	    uc_known  = merge_known uc.uc_known !known }
    | _ ->
	assert false
  in
  (* 2. merge in the new declarations *)
  (* ... *)
  uc
***)
let clone_export uc th i = assert false (*TODO*)

let add_decl uc d =
  let uc = { uc with uc_ctxt = Context.add_decl uc.uc_ctxt d } in
  match d.d_node with
    | Dtype dl ->
        List.fold_left add_type uc dl
    | Dlogic dl ->
        List.fold_left add_logic uc dl
    | Dprop (k, id, f) ->
        add_symbol add_pr id f uc
    | Dclone _ | Duse _ -> 
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
  fprintf fmt "@]@\n@[<hov 2>logic symbols: ";
  Mnm.iter (fun x s -> fprintf fmt "%s -> %a;@ " x print_ident s.ls_name)
    ns.ns_ls;
  fprintf fmt "@]@\n@[<hov 2>namespace: ";
  Mnm.iter (fun x th -> fprintf fmt "%s -> [@[%a@]];@ " x print_namespace th)
    ns.ns_ns;
  fprintf fmt "@]"

let print_uc fmt uc = print_namespace fmt (get_namespace uc)
let print_th fmt th = fprintf fmt "<theory (TODO>"

(*
Local Variables:
compile-command: "make -C ../.. test"
End:
*)
