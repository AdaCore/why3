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
open Decl

(** Namespace *)

module Snm = Sstr
module Mnm = Mstr

type namespace = {
  ns_ts : tysymbol Mnm.t;   (* type symbols *)
  ns_ls : lsymbol Mnm.t;    (* logic symbols *)
  ns_pr : prop Mnm.t;       (* propositions *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_ts = Mnm.empty;
  ns_ls = Mnm.empty;
  ns_ns = Mnm.empty;
  ns_pr = Mnm.empty;
}

exception ClashSymbol of string

let ns_add chk x v m =
  if not chk then Mnm.add x v m
  else try
    if Mnm.find x m != v then raise (ClashSymbol x);
    m
  with Not_found -> Mnm.add x v m

let rec merge_ns chk ns1 ns2 =
  { ns_ts = Mnm.fold (ns_add chk) ns1.ns_ts ns2.ns_ts;
    ns_ls = Mnm.fold (ns_add chk) ns1.ns_ls ns2.ns_ls;
    ns_pr = Mnm.fold (ns_add chk) ns1.ns_pr ns2.ns_pr;
    ns_ns = Mnm.fold (fusion chk) ns1.ns_ns ns2.ns_ns; }

and fusion chk x ns m =
  let os = try Mnm.find x m with Not_found -> empty_ns in
  Mnm.add x (merge_ns chk os ns) m

let add_ts chk x ts ns = { ns with ns_ts = ns_add chk x ts ns.ns_ts }
let add_ls chk x ls ns = { ns with ns_ls = ns_add chk x ls ns.ns_ls }
let add_pr chk x pf ns = { ns with ns_pr = ns_add chk x pf ns.ns_pr }
let add_ns chk x nn ns = { ns with ns_ns = fusion chk x nn ns.ns_ns }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mnm.find a (get_map ns)
  | a::l -> ns_find get_map (Mnm.find a ns.ns_ns) l

let ns_find_ts = ns_find (fun ns -> ns.ns_ts)
let ns_find_ls = ns_find (fun ns -> ns.ns_ls)

let ns_find_prop = ns_find (fun ns -> ns.ns_pr)
let ns_find_pr   ns sl = fst (ns_find_prop ns sl)
let ns_find_fmla ns sl = snd (ns_find_prop ns sl)


(** Theory *)

type theory = {
  th_name   : ident;        (* theory name *)
  th_decls  : tdecl list;   (* theory declarations *)
  th_export : namespace;    (* exported namespace *)
  th_clone  : clone_map;    (* cloning history *)
  th_known  : known_map;    (* known identifiers *)
  th_local  : Sid.t;        (* locally declared idents *)
}

and tdecl =
  | Decl  of decl
  | Use   of theory
  | Clone of theory * (ident * ident) list

and clone_map = Sid.t Mid.t

let builtin_theory =
  let decl_int  = create_ty_decl [ts_int, Tabstract] in
  let decl_real = create_ty_decl [ts_real, Tabstract] in
  let decl_equ  = create_logic_decl [ps_equ, None] in
  let decl_neq  = create_logic_decl [ps_neq, None] in

  let decls   = [ Decl decl_int; Decl decl_real;
                  Decl decl_equ; Decl decl_neq ] in

  let kn_int  = known_add_decl Mid.empty decl_int in
  let kn_real = known_add_decl kn_int decl_real in
  let kn_equ  = known_add_decl kn_real decl_equ in
  let kn_neq  = known_add_decl kn_equ decl_neq in

  let ns_int  = Mnm.add ts_int.ts_name.id_short ts_int Mnm.empty in
  let ns_real = Mnm.add ts_real.ts_name.id_short ts_real ns_int in
  let ns_equ  = Mnm.add ps_equ.ls_name.id_short ps_equ Mnm.empty in
  let ns_neq  = Mnm.add ps_neq.ls_name.id_short ps_neq ns_equ in

  let export  = { ns_ts = ns_real;   ns_ls = ns_neq;
                  ns_pr = Mnm.empty; ns_ns = Mnm.empty } in

  { th_name   = id_register (id_fresh "BuiltIn");
    th_decls  = decls;
    th_export = export;
    th_clone  = Mid.empty;
    th_known  = kn_neq;
    th_local  = Sid.empty }


(** Constructors and utilities *)

type theory_uc = {
  uc_name   : ident;
  uc_decls  : tdecl list;
  uc_import : namespace list;
  uc_export : namespace list;
  uc_clone  : clone_map;
  uc_known  : known_map;
  uc_local  : Sid.t;
}

exception CloseTheory
exception NoOpenedNamespace

let create_theory n =
  { uc_name   = id_register n;
    uc_decls  = [Use builtin_theory];
    uc_import = [builtin_theory.th_export];
    uc_export = [builtin_theory.th_export];
    uc_clone  = Mid.empty;
    uc_known  = builtin_theory.th_known;
    uc_local  = Sid.empty; }

let close_theory uc = match uc.uc_export with
  | [e] ->
      { th_name   = uc.uc_name;
        th_decls  = List.rev uc.uc_decls;
        th_export = e;
        th_clone  = uc.uc_clone;
        th_known  = uc.uc_known;
        th_local  = uc.uc_local; }
  | _ ->
      raise CloseTheory

let get_namespace uc = List.hd uc.uc_import

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
      uc_known  = merge_known uc.uc_known th.th_known;
      uc_decls  = Use th :: uc.uc_decls }
  | _ ->
      assert false

let add_symbol add id v uc =
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = add false id.id_short v i0 :: sti;
      uc_export = add true  id.id_short v e0 :: ste;
      uc_local  = Sid.add id uc.uc_local }
  | _ ->
      assert false

let add_type uc (ts,def) =
  let add_constr uc fs = add_symbol add_ls fs.ls_name fs uc in
  let uc = add_symbol add_ts ts.ts_name ts uc in
  match def with
    | Tabstract -> uc
    | Talgebraic lfs -> List.fold_left add_constr uc lfs

let add_logic uc (ls,_) = add_symbol add_ls ls.ls_name ls uc

let add_ind uc (ps,la) =
  let uc = add_symbol add_ls ps.ls_name ps uc in
  let add uc (pr,f) = add_symbol add_pr pr.pr_name (pr,f) uc in
  List.fold_left add uc la

let add_prop uc (_,pr,f) = add_symbol add_pr pr.pr_name (pr,f) uc

let add_decl uc d =
  let uc = match d.d_node with
    | Dtype dl  -> List.fold_left add_type uc dl
    | Dlogic dl -> List.fold_left add_logic uc dl
    | Dind dl   -> List.fold_left add_ind uc dl
    | Dprop p   -> add_prop uc p
  in
  { uc with uc_decls = Decl d :: uc.uc_decls;
            uc_known = known_add_decl uc.uc_known d }

let merge_clone cl th sl =
  let get m id = try Mid.find id m with Not_found -> Sid.empty in
  let add m m' (id,id') =
    Mid.add id' (Sid.add id (Sid.union (get m id) (get m' id'))) m'
  in
  List.fold_left (add th.th_clone) cl sl

let add_clone uc th sl =
  let decls = Clone (th,sl) :: uc.uc_decls in
  let clone = merge_clone uc.uc_clone th sl in
  { uc with uc_decls = decls; uc_clone = clone }


(** Clone *)

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

let create_inst ~ts ~ls ~lemma ~goal =
  let ts =
    List.fold_left (fun acc (tso,tsn) -> Mts.add tso tsn acc) Mts.empty ts in
  let ls =
    List.fold_left (fun acc (lso,lsn) -> Mls.add lso lsn acc) Mls.empty ls in
  let make_list = List.fold_left (fun acc lem -> Spr.add lem acc) Spr.empty in
  {
    inst_ts    = ts;
    inst_ls    = ls;
    inst_lemma = make_list lemma;
    inst_goal  = make_list goal;
  }

exception CannotInstantiate of ident

type clones = {
  ts_table : tysymbol Hts.t;
  ls_table : lsymbol Hls.t;
  pr_table : prop Hpr.t;
  id_table : ident Hid.t;
  nw_local : unit Hid.t;
  id_local : Sid.t;
}

let empty_clones s = {
  ts_table = Hts.create 17;
  ls_table = Hls.create 17;
  pr_table = Hpr.create 17;
  id_table = Hid.create 17;
  nw_local = Hid.create 17;
  id_local = s;
}

let cl_add_ts cl ts ts' =
  Hts.add cl.ts_table ts ts';
  Hid.add cl.id_table ts.ts_name ts'.ts_name

let cl_add_ls cl ls ls' =
  Hls.add cl.ls_table ls ls';
  Hid.add cl.id_table ls.ls_name ls'.ls_name

(* populate the clone structure *)

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

let cl_trans_prop cl (pr,f) =
  let pr' = create_prsymbol (id_dup pr.pr_name) in
  let f' = cl_trans_fmla cl f in
  Hid.add cl.id_table pr.pr_name pr'.pr_name;
  Hpr.add cl.pr_table pr (pr',f');
  pr', f'

(* initialize the clone structure *)

exception NonLocal of ident
exception BadInstance of ident * ident

let cl_init_ts cl ts ts' =
  let id = ts.ts_name in
  if not (Sid.mem id cl.id_local) then raise (NonLocal id);
  if List.length ts.ts_args <> List.length ts'.ts_args
    then raise (BadInstance (id, ts'.ts_name));
  cl_add_ts cl ts ts'

let cl_init_ls cl ls ls' =
  let id = ls.ls_name in
  if not (Sid.mem id cl.id_local) then raise (NonLocal id);
  let tymatch sb ty ty' =
    try Ty.matching sb ty' (cl_trans_ty cl ty)
    with TypeMismatch -> raise (BadInstance (id, ls'.ls_name))
  in
  let sb = match ls.ls_value,ls'.ls_value with
    | Some ty, Some ty' -> tymatch Mtv.empty ty ty'
    | None, None -> Mtv.empty
    | _ -> raise (BadInstance (id, ls'.ls_name))
  in
  ignore (try List.fold_left2 tymatch sb ls.ls_args ls'.ls_args
  with Invalid_argument _ -> raise (BadInstance (id, ls'.ls_name)));
  cl_add_ls cl ls ls'

let cl_init_pr cl pr =
  if not (Sid.mem pr.pr_name cl.id_local) then raise (NonLocal pr.pr_name)

let cl_init th inst =
  let cl = empty_clones th.th_local in
  Mts.iter (cl_init_ts cl) inst.inst_ts;
  Mls.iter (cl_init_ls cl) inst.inst_ls;
  Spr.iter (cl_init_pr cl) inst.inst_lemma;
  Spr.iter (cl_init_pr cl) inst.inst_goal;
  cl

(* clone declarations *)

let cl_new_ts cl ts =
  let ts' = cl_find_ts cl ts in
  Hid.add cl.nw_local ts'.ts_name ();
  ts'

let cl_new_ls cl ls =
  let ls' = cl_find_ls cl ls in
  Hid.add cl.nw_local ls'.ls_name ();
  ls'

let cl_new_prop cl pf =
  let pf' = cl_trans_prop cl pf in
  Hid.add cl.nw_local (fst pf').pr_name ();
  pf'

let cl_add_type cl inst_ts acc (ts, def) =
  if Mts.mem ts inst_ts then begin
    if ts.ts_def <> None || def <> Tabstract then
      raise (CannotInstantiate ts.ts_name);
    acc
  end else
    let ts' = cl_new_ts cl ts in
    let def' = match def with
      | Tabstract -> Tabstract
      | Talgebraic ls -> Talgebraic (List.map (cl_new_ls cl) ls)
    in
    (ts', def') :: acc

let extract_ls_defn f =
  let vl, ef = f_open_forall f in
  match ef.f_node with
    | Fapp (s, [t1; t2]) when s == ps_equ ->
        begin match t1.t_node with
          | Tapp (fs, _) -> make_fs_defn fs vl t2
          | _ -> assert false
        end
    | Fbinop (Fiff, f1, f2) ->
        begin match f1.f_node with
          | Fapp (ps, _) -> make_ps_defn ps vl f2
          | _ -> assert false
        end
    | _ -> assert false

let cl_add_logic cl inst_ls acc (ls,ld) = match ld with
  | None when Mls.mem ls inst_ls ->
      acc
  | None ->
      (cl_new_ls cl ls, None) :: acc
  | Some _ when Mls.mem ls inst_ls ->
      raise (CannotInstantiate ls.ls_name)
  | Some ld ->
      let _ = cl_new_ls cl ls in
      let f = ls_defn_axiom ld in
      extract_ls_defn (cl_trans_fmla cl f) :: acc

let cl_add_ind cl inst_ls (ps,la) =
  if Mls.mem ps inst_ls then raise (CannotInstantiate ps.ls_name);
  cl_new_ls cl ps, List.map (cl_new_prop cl) la

let cl_add_decl cl inst d = match d.d_node with
  | Dtype tyl ->
      let add = cl_add_type cl inst.inst_ts in
      let l = List.rev (List.fold_left add [] tyl) in
      if l = [] then None else Some (create_ty_decl l)
  | Dlogic ll ->
      let add = cl_add_logic cl inst.inst_ls in
      let l = List.rev (List.fold_left add [] ll) in
      if l = [] then None else Some (create_logic_decl l)
  | Dind indl ->
      let add = cl_add_ind cl inst.inst_ls in
      Some (create_ind_decl (List.map add indl))
  | Dprop (Pgoal, _, _) ->
      None
  | Dprop (Plemma, pr, _) when Spr.mem pr inst.inst_goal ->
      None
  | Dprop (k, pr, f) ->
      let k' = match k with
        | Paxiom when Spr.mem pr inst.inst_lemma -> Plemma
        | Paxiom when Spr.mem pr inst.inst_goal  -> Pgoal
        | _                                      -> Paxiom
      in
      let pr',f' = cl_new_prop cl (pr,f) in
      Some (create_prop_decl k' pr' f')

let cl_add_tdecl cl inst uc td = match td with
  | Decl d ->
      begin match cl_add_decl cl inst d with
        | Some d -> { uc with
            uc_decls = Decl d :: uc.uc_decls;
            uc_known = known_add_decl uc.uc_known d }
        | None -> uc
      end
  | Use th -> { uc with
      uc_decls = td :: uc.uc_decls;
      uc_known = merge_known uc.uc_known th.th_known }
  | Clone (th,sl) ->
      add_clone uc th sl

let clone_export uc th inst =
  let cl = cl_init th inst in
  let add_tdecl = cl_add_tdecl cl inst in
  let uc = List.fold_left add_tdecl uc th.th_decls in

  let add_idid id id' acc = (id,id') :: acc in
  let sl = Hid.fold add_idid cl.id_table [] in
  let uc = add_clone uc th sl in

  let add_local id' () acc = Sid.add id' acc in
  let lc = Hid.fold add_local cl.nw_local uc.uc_local in
  let uc = { uc with uc_local = lc } in

  let f_ts n ts ns =
    if Sid.mem ts.ts_name th.th_local then
      let ts' = Hts.find cl.ts_table ts in
      if Hid.mem cl.nw_local ts'.ts_name
      then add_ts true n ts' ns else ns
    else add_ts true n ts ns in

  let f_ls n ls ns =
    if Sid.mem ls.ls_name th.th_local then
      let ls' = Hls.find cl.ls_table ls in
      if Hid.mem cl.nw_local ls'.ls_name
      then add_ls true n ls' ns else ns
    else add_ls true n ls ns in

  let f_pr n (pr,f) ns =
    if Sid.mem pr.pr_name th.th_local then
      if Hpr.mem cl.pr_table pr then
        let (pr',f') = Hpr.find cl.pr_table pr in
        if Hid.mem cl.nw_local pr'.pr_name
        then add_pr true n (pr',f') ns else ns
      else ns
    else add_pr true n (pr,f) ns in

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
        uc_export = merge_ns true  ns e0 :: ste; }
    | _ ->
        assert false

