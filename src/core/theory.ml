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
  ns_pr : prsymbol Mnm.t;   (* propositions *)
  ns_ns : namespace Mnm.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_ts = Mnm.empty;
  ns_ls = Mnm.empty;
  ns_ns = Mnm.empty;
  ns_pr = Mnm.empty;
}

exception ClashSymbol of string

let ns_add eq chk x v m =
  if not chk then Mnm.add x v m
  else try
    if not (eq (Mnm.find x m) v) then raise (ClashSymbol x);
    m
  with Not_found -> Mnm.add x v m

let ts_add = ns_add ts_equal
let ls_add = ns_add ls_equal
let pr_add = ns_add pr_equal

let rec merge_ns chk ns1 ns2 =
  { ns_ts = Mnm.fold (ts_add chk) ns1.ns_ts ns2.ns_ts;
    ns_ls = Mnm.fold (ls_add chk) ns1.ns_ls ns2.ns_ls;
    ns_pr = Mnm.fold (pr_add chk) ns1.ns_pr ns2.ns_pr;
    ns_ns = Mnm.fold (fusion chk) ns1.ns_ns ns2.ns_ns; }

and fusion chk x ns m =
  let os = try Mnm.find x m with Not_found -> empty_ns in
  Mnm.add x (merge_ns chk os ns) m

let add_ts chk x ts ns = { ns with ns_ts = ts_add chk x ts ns.ns_ts }
let add_ls chk x ls ns = { ns with ns_ls = ls_add chk x ls ns.ns_ls }
let add_pr chk x pf ns = { ns with ns_pr = pr_add chk x pf ns.ns_pr }
let add_ns chk x nn ns = { ns with ns_ns = fusion chk x nn ns.ns_ns }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mnm.find a (get_map ns)
  | a::l -> ns_find get_map (Mnm.find a ns.ns_ns) l

let ns_find_ts = ns_find (fun ns -> ns.ns_ts)
let ns_find_ls = ns_find (fun ns -> ns.ns_ls)
let ns_find_pr = ns_find (fun ns -> ns.ns_pr)

(** Meta properties *)

type meta_arg_type =
  | MTtysymbol
  | MTlsymbol
  | MTprsymbol
  | MTstring
  | MTint

type meta_arg =
  | MAts  of tysymbol
  | MAls  of lsymbol
  | MApr  of prsymbol
  | MAstr of string
  | MAint of int

type meta = {
  meta_name : string;
  meta_type : meta_arg_type list;
  meta_excl : bool;
  meta_tag  : int;
}

module SMmeta = StructMake(struct type t = meta let tag m = m.meta_tag end)

module Smeta = SMmeta.S
module Mmeta = SMmeta.M
module Hmeta = SMmeta.H

let meta_equal = (==)

let meta_hash m = m.meta_tag

exception KnownMeta of meta
exception UnknownMeta of string
exception BadMetaArity of meta * int * int
exception MetaTypeMismatch of meta * meta_arg_type * meta_arg_type

let meta_table = Hashtbl.create 17

let mk_meta =
  let c = ref (-1) in
  fun s al excl -> {
    meta_name = s;
    meta_type = al;
    meta_excl = excl;
    meta_tag  = (incr c; !c) }

let register_meta s al excl =
  try
    let m = Hashtbl.find meta_table s in
    if al = m.meta_type && excl = m.meta_excl then m
    else raise (KnownMeta m)
  with Not_found ->
    let m = mk_meta s al excl in
    Hashtbl.add meta_table s m;
    m

let register_meta_excl s al = register_meta s al true
let register_meta      s al = register_meta s al false

let lookup_meta s =
  try Hashtbl.find meta_table s
  with Not_found -> raise (UnknownMeta s)

let list_metas () = Hashtbl.fold (fun _ v acc -> v::acc) meta_table []

(** Theory *)

type theory = {
  th_name   : ident;      (* theory name *)
  th_decls  : tdecl list; (* theory declarations *)
  th_export : namespace;  (* exported namespace *)
  th_known  : known_map;  (* known identifiers *)
  th_local  : Sid.t;      (* locally declared idents *)
  th_used   : Sid.t;      (* used theories *)
}

and tdecl = {
  td_node : tdecl_node;
  td_tag  : int;
}

and tdecl_node =
  | Decl  of decl
  | Use   of theory
  | Clone of theory * tysymbol Mts.t * lsymbol Mls.t * prsymbol Mpr.t
  | Meta  of meta * meta_arg list

(** Theory declarations *)

module Hstdecl = Hashcons.Make (struct

  type t = tdecl

  let eq_marg a1 a2 = match a1,a2 with
    | MAts ts1, MAts ts2 -> ts_equal ts1 ts2
    | MAls ls1, MAls ls2 -> ls_equal ls1 ls2
    | MApr pr1, MApr pr2 -> pr_equal pr1 pr2
    | MAstr s1, MAstr s2 -> s1 = s2
    | MAint i1, MAint i2 -> i1 = i2
    | _,_ -> false

  let equal td1 td2 = match td1.td_node, td2.td_node with
    | Decl d1, Decl d2 -> d_equal d1 d2
    | Use th1, Use th2 -> id_equal th1.th_name th2.th_name
    | Clone (th1,tm1,lm1,pm1), Clone (th2,tm2,lm2,pm2) ->
        id_equal th1.th_name th2.th_name &&
        Mts.equal ts_equal tm1 tm2 &&
        Mls.equal ls_equal lm1 lm2 &&
        Mpr.equal pr_equal pm1 pm2
    | Meta (t1,al1), Meta (t2,al2) ->
        t1 = t2 && list_all2 eq_marg al1 al2
    | _,_ -> false

  let hs_cl_ts _ ts acc = Hashcons.combine acc (ts_hash ts)
  let hs_cl_ls _ ls acc = Hashcons.combine acc (ls_hash ls)
  let hs_cl_pr _ pr acc = Hashcons.combine acc (pr_hash pr)

  let hs_ta = function
    | MAts ts -> ts_hash ts
    | MAls ls -> ls_hash ls
    | MApr pr -> pr_hash pr
    | MAstr s -> Hashtbl.hash s
    | MAint i -> Hashtbl.hash i

  let hash td = match td.td_node with
    | Decl d -> d_hash d
    | Use th -> id_hash th.th_name
    | Clone (th,tm,lm,pm) ->
        Mts.fold hs_cl_ts tm (Mls.fold hs_cl_ls lm
          (Mpr.fold hs_cl_pr pm (id_hash th.th_name)))
    | Meta (t,al) -> Hashcons.combine_list hs_ta (Hashtbl.hash t) al

  let tag n td = { td with td_tag = n }

end)

let mk_tdecl n = Hstdecl.hashcons { td_node = n ; td_tag = -1 }

module Tdecl = StructMake (struct
  type t = tdecl
  let tag td = td.td_tag
end)

module Stdecl = Tdecl.S
module Mtdecl = Tdecl.M
module Htdecl = Tdecl.H

let td_equal = (==)
let td_hash td = td.td_tag

(** Constructors and utilities *)

type theory_uc = {
  uc_name   : ident;
  uc_decls  : tdecl list;
  uc_import : namespace list;
  uc_export : namespace list;
  uc_known  : known_map;
  uc_local  : Sid.t;
  uc_used   : Sid.t;
}

exception CloseTheory
exception NoOpenedNamespace

let empty_theory n = {
  uc_name   = id_register n;
  uc_decls  = [];
  uc_import = [empty_ns];
  uc_export = [empty_ns];
  uc_known  = Mid.empty;
  uc_local  = Sid.empty;
  uc_used   = Sid.empty;
}

let close_theory uc = match uc.uc_export with
  | [e] -> {
      th_name   = uc.uc_name;
      th_decls  = List.rev uc.uc_decls;
      th_export = e;
      th_known  = uc.uc_known;
      th_local  = uc.uc_local;
      th_used   = uc.uc_used }
  | _ -> raise CloseTheory

let get_namespace uc = List.hd uc.uc_import
let get_known uc = uc.uc_known

let open_namespace uc = match uc.uc_import with
  | ns :: _ -> { uc with
      uc_import =       ns :: uc.uc_import;
      uc_export = empty_ns :: uc.uc_export; }
  | [] -> assert false

let close_namespace uc import s =
  match uc.uc_import, uc.uc_export with
  | _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = match s with Some s -> add_ns false s e0 i1 | _ -> i1 in
      let e1 = match s with Some s -> add_ns true  s e0 e1 | _ -> e1 in
      { uc with uc_import = i1 :: sti; uc_export = e1 :: ste; }
  | [_], [_] -> raise NoOpenedNamespace
  | _ -> assert false

(* Base constructors *)

let known_clone kn tm lm pm =
  Mts.iter (fun _ ts -> known_id kn ts.ts_name) tm;
  Mls.iter (fun _ ls -> known_id kn ls.ls_name) lm;
  Mpr.iter (fun _ pr -> known_id kn pr.pr_name) pm

let known_meta kn al =
  let check = function
    | MAts ts -> known_id kn ts.ts_name
    | MAls ls -> known_id kn ls.ls_name
    | MApr pr -> known_id kn pr.pr_name
    | _ -> ()
  in
  List.iter check al

let add_tdecl uc td = match td.td_node with
  | Decl d -> { uc with
      uc_decls = td :: uc.uc_decls;
      uc_known = known_add_decl uc.uc_known d;
      uc_local = Sid.union uc.uc_local d.d_news }
  | Use th when Sid.mem th.th_name uc.uc_used -> uc
  | Use th -> { uc with
      uc_decls = td :: uc.uc_decls;
      uc_known = merge_known uc.uc_known th.th_known;
      uc_used  = Sid.union uc.uc_used (Sid.add th.th_name th.th_used) }
  | Clone (_,tm,lm,pm) -> known_clone uc.uc_known tm lm pm;
      { uc with uc_decls = td :: uc.uc_decls }
  | Meta (_,al) -> known_meta uc.uc_known al;
      { uc with uc_decls = td :: uc.uc_decls }

(** Declarations *)

let add_symbol add id v uc =
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = add false id.id_string v i0 :: sti;
      uc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_type uc (ts,def) =
  let add_constr uc fs = add_symbol add_ls fs.ls_name fs uc in
  let uc = add_symbol add_ts ts.ts_name ts uc in
  match def with
    | Tabstract -> uc
    | Talgebraic lfs -> List.fold_left add_constr uc lfs

let add_logic uc (ls,_) = add_symbol add_ls ls.ls_name ls uc

let add_ind uc (ps,la) =
  let uc = add_symbol add_ls ps.ls_name ps uc in
  let add uc (pr,_) = add_symbol add_pr pr.pr_name pr uc in
  List.fold_left add uc la

let add_prop uc (_,pr,_) = add_symbol add_pr pr.pr_name pr uc

let create_decl d = mk_tdecl (Decl d)

let add_decl uc d =
  let uc = add_tdecl uc (create_decl d) in
  match d.d_node with
    | Dtype dl  -> List.fold_left add_type uc dl
    | Dlogic dl -> List.fold_left add_logic uc dl
    | Dind dl   -> List.fold_left add_ind uc dl
    | Dprop p   -> add_prop uc p

(** Declaration constructors + add_decl *)

let add_ty_decl uc dl = add_decl uc (create_ty_decl dl)
let add_logic_decl uc dl = add_decl uc (create_logic_decl dl)
let add_ind_decl uc dl = add_decl uc (create_ind_decl dl)
let add_prop_decl uc k p f = add_decl uc (create_prop_decl k p f)

(** Use *)

let create_use th = mk_tdecl (Use th)

let use_export uc th =
  let uc = add_tdecl uc (create_use th) in
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = merge_ns false th.th_export i0 :: sti;
      uc_export = merge_ns true  th.th_export e0 :: ste }
  | _ -> assert false

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
  let add_ts acc (tso,tsn) = Mts.add tso tsn acc in
  let add_ls acc (lso,lsn) = Mls.add lso lsn acc in
  let add_pr acc lem = Spr.add lem acc in {
    inst_ts    = List.fold_left add_ts Mts.empty ts;
    inst_ls    = List.fold_left add_ls Mls.empty ls;
    inst_lemma = List.fold_left add_pr Spr.empty lemma;
    inst_goal  = List.fold_left add_pr Spr.empty goal }

exception CannotInstantiate of ident

type clones = {
  cl_local : Sid.t;
  mutable id_local : Sid.t;
  mutable ts_table : tysymbol Mts.t;
  mutable ls_table : lsymbol Mls.t;
  mutable pr_table : prsymbol Mpr.t;
}

let empty_clones s = {
  cl_local = s;
  id_local = Sid.empty;
  ts_table = Mts.empty;
  ls_table = Mls.empty;
  pr_table = Mpr.empty;
}

(* populate the clone structure *)

let rec cl_find_ts cl ts =
  if not (Sid.mem ts.ts_name cl.cl_local) then ts
  else try Mts.find ts cl.ts_table
  with Not_found ->
    let td' = option_map (cl_trans_ty cl) ts.ts_def in
    let ts' = create_tysymbol (id_dup ts.ts_name) ts.ts_args td' in
    cl.id_local <- Sid.add ts'.ts_name cl.id_local;
    cl.ts_table <- Mts.add ts ts' cl.ts_table;
    ts'

and cl_trans_ty cl ty = ty_s_map (cl_find_ts cl) ty

let cl_find_ls cl ls =
  if not (Sid.mem ls.ls_name cl.cl_local) then ls
  else try Mls.find ls cl.ls_table
  with Not_found ->
    let ta' = List.map (cl_trans_ty cl) ls.ls_args in
    let vt' = option_map (cl_trans_ty cl) ls.ls_value in
    let ls' = create_lsymbol (id_dup ls.ls_name) ta' vt' in
    cl.id_local <- Sid.add ls'.ls_name cl.id_local;
    cl.ls_table <- Mls.add ls ls' cl.ls_table;
    ls'

let cl_trans_fmla cl f = f_s_map (cl_find_ts cl) (cl_find_ls cl) f

let cl_find_pr cl pr =
  if not (Sid.mem pr.pr_name cl.cl_local) then pr
  else try Mpr.find pr cl.pr_table
  with Not_found ->
    let pr' = create_prsymbol (id_dup pr.pr_name) in
    cl.id_local <- Sid.add pr'.pr_name cl.id_local;
    cl.pr_table <- Mpr.add pr pr' cl.pr_table;
    pr'

(* initialize the clone structure *)

exception NonLocal of ident
exception BadInstance of ident * ident

let cl_init_ts cl ts ts' =
  let id = ts.ts_name in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  if List.length ts.ts_args <> List.length ts'.ts_args
    then raise (BadInstance (id, ts'.ts_name));
  cl.ts_table <- Mts.add ts ts' cl.ts_table

let cl_init_ls cl ls ls' =
  let id = ls.ls_name in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  let mtch sb ty ty' =
    try ty_match sb ty' (cl_trans_ty cl ty)
    with TypeMismatch _ -> raise (BadInstance (id, ls'.ls_name))
  in
  let sb = match ls.ls_value,ls'.ls_value with
    | Some ty, Some ty' -> mtch Mtv.empty ty ty'
    | None, None -> Mtv.empty
    | _ -> raise (BadInstance (id, ls'.ls_name))
  in
  ignore (try List.fold_left2 mtch sb ls.ls_args ls'.ls_args
  with Invalid_argument _ -> raise (BadInstance (id, ls'.ls_name)));
  cl.ls_table <- Mls.add ls ls' cl.ls_table

let cl_init_pr cl pr =
  let id = pr.pr_name in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id)

let cl_init th inst =
  let cl = empty_clones th.th_local in
  Mts.iter (cl_init_ts cl) inst.inst_ts;
  Mls.iter (cl_init_ls cl) inst.inst_ls;
  Spr.iter (cl_init_pr cl) inst.inst_lemma;
  Spr.iter (cl_init_pr cl) inst.inst_goal;
  cl

(* clone declarations *)

let cl_type cl inst tdl =
  let add_constr ls =
    if Mls.mem ls inst.inst_ls
      then raise (CannotInstantiate ls.ls_name)
      else cl_find_ls cl ls
  in
  let add_type (ts,td) acc =
    if Mts.mem ts inst.inst_ts then
      if ts.ts_def = None && td = Tabstract then acc
      else raise (CannotInstantiate ts.ts_name)
    else
      let ts' = cl_find_ts cl ts in
      let td' = match td with
        | Tabstract -> Tabstract
        | Talgebraic cl -> Talgebraic (List.map add_constr cl)
      in
      (ts',td') :: acc
  in
  create_ty_decl (List.fold_right add_type tdl [])

let extract_ls_defn f =
  let vl, ef = f_open_forall f in
  match ef.f_node with
    | Fapp (s, [t1; t2]) when ls_equal s ps_equ ->
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

let cl_logic cl inst ldl =
  let add_logic (ls,ld) acc = match ld with
    | None when Mls.mem ls inst.inst_ls ->
        acc
    | None ->
        (cl_find_ls cl ls, None) :: acc
    | Some _ when Mls.mem ls inst.inst_ls ->
        raise (CannotInstantiate ls.ls_name)
    | Some ld ->
        let f = ls_defn_axiom ld in
        extract_ls_defn (cl_trans_fmla cl f) :: acc
  in
  create_logic_decl (List.fold_right add_logic ldl [])

let cl_ind cl inst idl =
  let add_case (pr,f) =
    if Spr.mem pr inst.inst_lemma || Spr.mem pr inst.inst_goal
      then raise (CannotInstantiate pr.pr_name)
      else cl_find_pr cl pr, cl_trans_fmla cl f
  in
  let add_ind (ps,la) =
    if Mls.mem ps inst.inst_ls
      then raise (CannotInstantiate ps.ls_name)
      else cl_find_ls cl ps, List.map add_case la
  in
  create_ind_decl (List.map add_ind idl)

let cl_prop cl inst (k,pr,f) =
  let k' = match k with
    | Pskip | Pgoal -> Pskip
    | Plemma when Spr.mem pr inst.inst_goal -> Pskip
    | Paxiom when Spr.mem pr inst.inst_goal -> Pgoal
    | Paxiom when Spr.mem pr inst.inst_lemma -> Plemma
    | Paxiom | Plemma -> Paxiom
  in
  let pr' = cl_find_pr cl pr in
  let f' = cl_trans_fmla cl f in
  create_prop_decl k' pr' f'

let cl_decl cl inst d = match d.d_node with
  | Dtype tdl -> cl_type cl inst tdl
  | Dlogic ldl -> cl_logic cl inst ldl
  | Dind idl -> cl_ind cl inst idl
  | Dprop p -> cl_prop cl inst p

let cl_marg cl = function
  | MAts ts -> MAts (cl_find_ts cl ts)
  | MAls ls -> MAls (cl_find_ls cl ls)
  | MApr pr -> MApr (cl_find_pr cl pr)
  | a -> a

let cl_tdecl cl inst td = match td.td_node with
  | Decl d -> Decl (cl_decl cl inst d)
  | Use th -> Use th
  | Clone (th,tm,lm,pm) -> Clone (th, Mts.map (cl_find_ts cl) tm,
          Mls.map (cl_find_ls cl) lm, Mpr.map (cl_find_pr cl) pm)
  | Meta (id,al) -> Meta (id, List.map (cl_marg cl) al)

let clone_theory cl add_td acc th inst =
  let add acc td =
    let td =
      try  Some (mk_tdecl (cl_tdecl cl inst td))
      with EmptyDecl -> None
    in
    option_apply acc (add_td acc) td
  in
  let acc = List.fold_left add acc th.th_decls in
  add_td acc (mk_tdecl (Clone (th, cl.ts_table, cl.ls_table, cl.pr_table)))

let clone_export uc th inst =
  let cl = cl_init th inst in
  let lc = uc.uc_local in
  let uc = clone_theory cl add_tdecl uc th inst in

  assert (Sid.equal uc.uc_local (Sid.union lc cl.id_local));

  let f_ts n ts ns =
    if Sid.mem ts.ts_name th.th_local then
      let ts' = Mts.find ts cl.ts_table in
      if Sid.mem ts'.ts_name cl.id_local
      then add_ts true n ts' ns else ns
    else add_ts true n ts ns in

  let f_ls n ls ns =
    if Sid.mem ls.ls_name th.th_local then
      let ls' = Mls.find ls cl.ls_table in
      if Sid.mem ls'.ls_name cl.id_local
      then add_ls true n ls' ns else ns
    else add_ls true n ls ns in

  let f_pr n pr ns =
    if Sid.mem pr.pr_name th.th_local then
      let pr' = Mpr.find pr cl.pr_table in
      if Sid.mem pr'.pr_name cl.id_local
      then add_pr true n pr' ns else ns
    else add_pr true n pr ns in

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
    | _ -> assert false

let clone_theory add_td acc th inst =
  clone_theory (cl_init th inst) add_td acc th inst

let create_clone = clone_theory (fun tdl td -> td :: tdl)

let create_null_clone th =
  mk_tdecl (Clone (th, Mts.empty, Mls.empty, Mpr.empty))


(** Meta properties *)

let get_meta_arg_type = function
  | MAts  _ -> MTtysymbol
  | MAls  _ -> MTlsymbol
  | MApr  _ -> MTprsymbol
  | MAstr _ -> MTstring
  | MAint _ -> MTint

let create_meta m al =
  let get_meta_arg at a =
    let mt = get_meta_arg_type a in
    if at = mt then a else raise (MetaTypeMismatch (m,at,mt))
  in
  let al = try List.map2 get_meta_arg m.meta_type al
    with Invalid_argument _ ->
      raise (BadMetaArity (m, List.length m.meta_type, List.length al))
  in
  mk_tdecl (Meta (m,al))

let add_meta uc s al = add_tdecl uc (create_meta s al)

let clone_meta tdt th tdc = match tdt.td_node, tdc.td_node with
  | Meta (t,al), Clone (th',tm,lm,pm) when id_equal th.th_name th'.th_name ->
      let find_ts ts = try Mts.find ts tm with Not_found -> ts in
      let find_ls ls = try Mls.find ls lm with Not_found -> ls in
      let find_pr pr = try Mpr.find pr pm with Not_found -> pr in
      let cl_marg = function
        | MAts ts -> MAts (find_ts ts)
        | MAls ls -> MAls (find_ls ls)
        | MApr pr -> MApr (find_pr pr)
        | a -> a
      in
      mk_tdecl (Meta (t, List.map cl_marg al))
  | _,_ -> invalid_arg "clone_meta"


(** Base theories *)

let builtin_theory =
  let uc = empty_theory (id_fresh "BuiltIn") in
  let uc = add_ty_decl uc [ts_int, Tabstract] in
  let uc = add_ty_decl uc [ts_real, Tabstract] in
  let uc = add_logic_decl uc [ps_equ, None] in
  close_theory uc

let create_theory n = use_export (empty_theory n) builtin_theory

let tuple_theory = Util.memo_int 17 (fun n ->
  let uc = empty_theory (id_fresh ("Tuple" ^ string_of_int n)) in
  let uc = add_ty_decl uc [ts_tuple n, Talgebraic [fs_tuple n]] in
  close_theory uc)

(* Exception reporting *)

let print_meta_arg_type fmt = function
  | MTtysymbol -> fprintf fmt "type_symbol"
  | MTlsymbol -> fprintf fmt "logic_symbol"
  | MTprsymbol -> fprintf fmt "proposition"
  | MTstring -> fprintf fmt "string"
  | MTint -> fprintf fmt "int"

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | NonLocal id ->
      Format.fprintf fmt "Non-local ident: %s" id.id_string
  | CannotInstantiate id ->
      Format.fprintf fmt "Cannot instantiate a defined ident %s" id.id_string
  | BadInstance (id1, id2) ->
      Format.fprintf fmt "Cannot instantiate ident %s with %s"
        id1.id_string id2.id_string
  | CloseTheory ->
      Format.fprintf fmt "Cannot close theory: some namespaces are still open"
  | NoOpenedNamespace ->
      Format.fprintf fmt "No opened namespaces"
  | ClashSymbol s ->
      Format.fprintf fmt "Symbol %s is already defined in the current scope" s
  | UnknownMeta s ->
      Format.fprintf fmt "Unknown metaproperty %s" s
  | KnownMeta m ->
      Format.fprintf fmt "Metaproperty %s is already registered with \
        a conflicting signature" m.meta_name
  | BadMetaArity (m,i1,i2) ->
      Format.fprintf fmt "Metaproperty %s requires %d arguments but \
        is applied to %d" m.meta_name i1 i2
  | MetaTypeMismatch (m,t1,t2) ->
      Format.fprintf fmt "Metaproperty %s expects %a argument but \
        is applied to %a"
        m.meta_name print_meta_arg_type t1 print_meta_arg_type t2
  | _ -> raise exn
  end

