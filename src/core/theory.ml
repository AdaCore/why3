(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Wstdlib
open Ident
open Ty
open Term
open Decl

(** Namespace *)

type namespace = {
  ns_ts : tysymbol Mstr.t;   (* type symbols *)
  ns_ls : lsymbol Mstr.t;    (* logic symbols *)
  ns_pr : prsymbol Mstr.t;   (* propositions *)
  ns_ns : namespace Mstr.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_ts = Mstr.empty;
  ns_ls = Mstr.empty;
  ns_pr = Mstr.empty;
  ns_ns = Mstr.empty;
}

exception ClashSymbol of string

let ns_replace eq chk x vo vn =
  if not chk then vn else
  if eq vo vn then vo else
  raise (ClashSymbol x)

let rec merge_ns chk ns1 ns2 =
  if ns1 == ns2 then ns1 else
  let join eq x n o = Some (ns_replace eq chk x o n) in
  let ns_union eq m1 m2 =
    if m1 == m2 then m1 else Mstr.union (join eq) m1 m2 in
  let fusion _ ns1 ns2 = Some (merge_ns chk ns1 ns2) in
  { ns_ts = ns_union ts_equal ns1.ns_ts ns2.ns_ts;
    ns_ls = ns_union ls_equal ns1.ns_ls ns2.ns_ls;
    ns_pr = ns_union pr_equal ns1.ns_pr ns2.ns_pr;
    ns_ns = Mstr.union fusion ns1.ns_ns ns2.ns_ns; }

let add_ns chk x ns m = Mstr.change (function
  | Some os -> Some (merge_ns chk ns os)
  | None    -> Some ns) x m

let ns_add eq chk x vn m = Mstr.change (function
  | Some vo -> Some (ns_replace eq chk x vo vn)
  | None    -> Some vn) x m

let add_ts chk x ts ns = { ns with ns_ts = ns_add ts_equal chk x ts ns.ns_ts }
let add_ls chk x ls ns = { ns with ns_ls = ns_add ls_equal chk x ls ns.ns_ls }
let add_pr chk x pf ns = { ns with ns_pr = ns_add pr_equal chk x pf ns.ns_pr }
let add_ns chk x nn ns = { ns with ns_ns = add_ns          chk x nn ns.ns_ns }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_ts = ns_find (fun ns -> ns.ns_ts)
let ns_find_ls = ns_find (fun ns -> ns.ns_ls)
let ns_find_pr = ns_find (fun ns -> ns.ns_pr)
let ns_find_ns = ns_find (fun ns -> ns.ns_ns)

(** Meta properties *)

type meta_arg_type =
  | MTty
  | MTtysymbol
  | MTlsymbol
  | MTprsymbol
  | MTstring
  | MTint

type meta_arg =
  | MAty  of ty
  | MAts  of tysymbol
  | MAls  of lsymbol
  | MApr  of prsymbol
  | MAstr of string
  | MAint of int

type meta = {
  meta_name : string;
  meta_type : meta_arg_type list;
  meta_excl : bool;
  meta_desc : Pp.formatted;
  meta_tag  : int;
}

let print_meta_desc fmt m =
  fprintf fmt "@[%s@\n  @[%a@]@]"
    m.meta_name Pp.formatted m.meta_desc

module SMmeta = MakeMSH(struct type t = meta let tag m = m.meta_tag end)

module Smeta = SMmeta.S
module Mmeta = SMmeta.M
module Hmeta = SMmeta.H

let meta_equal : meta -> meta -> bool = (==)

let meta_hash m = m.meta_tag

exception KnownMeta of meta
exception UnknownMeta of string
exception BadMetaArity of meta * int
exception MetaTypeMismatch of meta * meta_arg_type * meta_arg_type

let meta_table = Hstr.create 17

let mk_meta =
  let c = ref (-1) in
  fun desc s al excl -> {
    meta_name = s;
    meta_type = al;
    meta_excl = excl;
    meta_desc = desc;
    meta_tag  = (incr c; !c);
  }

let register_meta ~desc s al excl =
  try
    let m = Hstr.find meta_table s in
    if al = m.meta_type && excl = m.meta_excl then m
    else raise (KnownMeta m)
  with Not_found ->
    let m = mk_meta desc s al excl in
    Hstr.add meta_table s m;
    m

let register_meta_excl ~desc s al = register_meta ~desc s al true
let register_meta      ~desc s al = register_meta ~desc s al false

let lookup_meta s = Hstr.find_exn meta_table (UnknownMeta s) s

let list_metas () = Hstr.fold (fun _ v acc -> v::acc) meta_table []

let meta_range = register_meta "range_type" [MTtysymbol; MTlsymbol]
    ~desc:"Projection@ of@ a@ range@ type."

let meta_float = register_meta "float_type" [MTtysymbol; MTlsymbol; MTlsymbol]
    ~desc:"Projection@ and@ finiteness@ of@ a@ floating-point@ type."

(** Theory *)

type theory = {
  th_name   : ident;      (* theory name *)
  th_path   : string list;(* environment qualifiers *)
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
  | Clone of theory * symbol_map
  | Meta  of meta * meta_arg list

and symbol_map = {
  sm_ts : tysymbol Mts.t;
  sm_ls : lsymbol Mls.t;
  sm_pr : prsymbol Mpr.t;
}

(** Theory declarations *)

module Hstdecl = Hashcons.Make (struct

  type t = tdecl

  let eq_marg a1 a2 = match a1,a2 with
    | MAty ty1, MAty ty2 -> ty_equal ty1 ty2
    | MAts ts1, MAts ts2 -> ts_equal ts1 ts2
    | MAls ls1, MAls ls2 -> ls_equal ls1 ls2
    | MApr pr1, MApr pr2 -> pr_equal pr1 pr2
    | MAstr s1, MAstr s2 -> s1 = s2
    | MAint i1, MAint i2 -> i1 = i2
    | _,_ -> false

  let eq_smap sm1 sm2 =
    Mts.equal ts_equal sm1.sm_ts sm2.sm_ts &&
    Mls.equal ls_equal sm1.sm_ls sm2.sm_ls &&
    Mpr.equal pr_equal sm1.sm_pr sm2.sm_pr

  let equal td1 td2 = match td1.td_node, td2.td_node with
    | Decl d1, Decl d2 -> d_equal d1 d2
    | Use th1, Use th2 -> id_equal th1.th_name th2.th_name
    | Clone (th1,sm1), Clone (th2,sm2) ->
        id_equal th1.th_name th2.th_name && eq_smap sm1 sm2
    | Meta (t1,al1), Meta (t2,al2) ->
        t1 = t2 && Lists.equal eq_marg al1 al2
    | _,_ -> false

  let hs_cl_ts _ ts acc = Hashcons.combine acc (ts_hash ts)
  let hs_cl_ls _ ls acc = Hashcons.combine acc (ls_hash ls)
  let hs_cl_pr _ pr acc = Hashcons.combine acc (pr_hash pr)

  let hs_ta = function
    | MAty ty -> ty_hash ty
    | MAts ts -> ts_hash ts
    | MAls ls -> ls_hash ls
    | MApr pr -> pr_hash pr
    | MAstr s -> Hashtbl.hash s
    | MAint i -> Hashtbl.hash i

  let hs_smap sm h =
    Mts.fold hs_cl_ts sm.sm_ts
      (Mls.fold hs_cl_ls sm.sm_ls
        (Mpr.fold hs_cl_pr sm.sm_pr h))

  let hash td = match td.td_node with
    | Decl d -> d_hash d
    | Use th -> id_hash th.th_name
    | Clone (th,sm) -> hs_smap sm (id_hash th.th_name)
    | Meta (t,al) -> Hashcons.combine_list hs_ta (Hashtbl.hash t) al

  let tag n td = { td with td_tag = n }

end)

let mk_tdecl n = Hstdecl.hashcons { td_node = n ; td_tag = -1 }

module Tdecl = MakeMSH (struct
  type t = tdecl
  let tag td = td.td_tag
end)

module Stdecl = Tdecl.S
module Mtdecl = Tdecl.M
module Htdecl = Tdecl.H

let td_equal : tdecl -> tdecl -> bool = (==)
let td_hash td = td.td_tag

(** Constructors and utilities *)

type theory_uc = {
  uc_name   : ident;
  uc_path   : string list;
  uc_decls  : tdecl list;
  uc_prefix : string list;
  uc_import : namespace list;
  uc_export : namespace list;
  uc_known  : known_map;
  uc_local  : Sid.t;
  uc_used   : Sid.t;
}

exception CloseTheory
exception NoOpenedNamespace

let empty_theory n p = {
  uc_name   = id_register n;
  uc_path   = p;
  uc_decls  = [];
  uc_prefix = [];
  uc_import = [empty_ns];
  uc_export = [empty_ns];
  uc_known  = Mid.empty;
  uc_local  = Sid.empty;
  uc_used   = Sid.empty;
}

let close_theory uc = match uc.uc_export with
  | [e] -> {
      th_name   = uc.uc_name;
      th_path   = uc.uc_path;
      th_decls  = List.rev uc.uc_decls;
      th_export = e;
      th_known  = uc.uc_known;
      th_local  = uc.uc_local;
      th_used   = uc.uc_used }
  | _ -> raise CloseTheory

let get_namespace uc = List.hd uc.uc_import
let get_known uc = uc.uc_known
let get_rev_decls uc = uc.uc_decls

let open_namespace uc s = match uc.uc_import with
  | ns :: _ -> { uc with
      uc_prefix =        s :: uc.uc_prefix;
      uc_import =       ns :: uc.uc_import;
      uc_export = empty_ns :: uc.uc_export; }
  | [] -> assert false

let close_namespace uc import =
  match uc.uc_prefix, uc.uc_import, uc.uc_export with
  | s :: prf, _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = add_ns false s e0 i1 in
      let e1 = add_ns true  s e0 e1 in
      { uc with uc_prefix = prf; uc_import = i1::sti; uc_export = e1::ste; }
  | [], [_], [_] -> raise NoOpenedNamespace
  | _ -> assert false

(* Base constructors *)

let known_ts kn ts = match ts.ts_def with
  | Alias ty -> ty_s_fold (fun () ts -> known_id kn ts.ts_name) () ty
  | NoDef | Range _ | Float _ -> known_id kn ts.ts_name

let known_clone kn sm =
  Mts.iter (fun _ ts -> known_ts kn ts) sm.sm_ts;
  Mls.iter (fun _ ls -> known_id kn ls.ls_name) sm.sm_ls;
  Mpr.iter (fun _ pr -> known_id kn pr.pr_name) sm.sm_pr

let known_meta kn al =
  let check = function
    | MAty ty -> ty_s_fold (fun () ts -> known_id kn ts.ts_name) () ty
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
  | Clone (_,sm) -> known_clone uc.uc_known sm;
      { uc with uc_decls = td :: uc.uc_decls }
  | Meta (_,al) -> known_meta uc.uc_known al;
      { uc with uc_decls = td :: uc.uc_decls }

(** Declarations *)

let store_path, store_theory, restore_path =
  let id_to_path = Wid.create 17 in
  let store_path uc path id =
    (* this symbol already belongs to some theory *)
    if Wid.mem id_to_path id then () else
    let prefix = List.rev (id.id_string :: path @ uc.uc_prefix) in
    Wid.set id_to_path id (uc.uc_path, uc.uc_name.id_string, prefix)
  in
  let store_theory th =
    let id = th.th_name in
    (* this symbol is already a theory *)
    if Wid.mem id_to_path id then () else
    Wid.set id_to_path id (th.th_path, id.id_string, []) in
  let restore_path id = Wid.find id_to_path id in
  store_path, store_theory, restore_path

let close_theory uc =
  let th = close_theory uc in
  store_theory th;
  th

let add_symbol add id v uc =
  store_path uc [] id;
  match uc.uc_import, uc.uc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      uc_import = add false id.id_string v i0 :: sti;
      uc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_symbol_ts uc ts = add_symbol add_ts ts.ts_name ts uc
let add_symbol_ls uc ls = add_symbol add_ls ls.ls_name ls uc
let add_symbol_pr uc pr = add_symbol add_pr pr.pr_name pr uc

let create_decl d = mk_tdecl (Decl d)

let check_subst_opacity ls ls' sbs =
  (* the definition of ls contains ls' instantiated with sbs *)
  let sbs = Mtv.set_diff sbs ls'.ls_opaque in
  let check () tv = if Stv.mem tv ls.ls_opaque then
    Loc.errorm "type parameter '%s is not opaque in symbol `%s'"
      tv.tv_name.id_string ls.ls_name.id_string in
  Mtv.iter (fun _ ty -> ty_v_fold check () ty) sbs

let check_decl_opacity d = match d.d_node with
  (* All lsymbols declared in Ddata are safe, nothing to check.
     We allow arbitrary ls_opaque in Dparam, but we check that
     cloning in theories preserves opacity, see cl_init below. *)
  | Dtype _ | Ddata _ | Dparam _ | Dprop _ -> ()
  | Dlogic dl ->
      let check (ols,ld) =
        let check () ls args value =
          let sbs = oty_match Mtv.empty ls.ls_value value in
          let sbs = List.fold_left2 ty_match sbs ls.ls_args args in
          check_subst_opacity ols ls sbs in
        if not (Stv.is_empty ols.ls_opaque) then
          t_app_fold check () (snd (open_ls_defn ld))
      in
      List.iter check dl
  | Dind (_, dl) ->
      (* TODO: are there safe classes of inductive predicates? *)
      let check (ls,_) = if not (Stv.is_empty ls.ls_opaque) then
        Loc.errorm ?loc:ls.ls_name.id_loc
          "inductive predicates cannot have opaque type parameters" in
      List.iter check dl

let warn_dubious_axiom uc k p syms =
  match k with
  | Plemma | Pgoal | Pskip -> ()
  | Paxiom ->
    try
      Sid.iter
        (fun id ->
          if Sid.mem id uc.uc_local then
          match (Ident.Mid.find id uc.uc_known).d_node with
          | Dtype { ts_def = NoDef } | Dparam _ -> raise Exit
          | _ -> ())
        syms;
      Warning.emit ?loc:p.id_loc "axiom %s does not contain any local abstract symbol"
        p.id_string
    with Exit -> ()

let lab_w_non_conservative_extension_no =
  Ident.create_label "W:non_conservative_extension:N"

let should_be_conservative id =
  not (Slab.mem lab_w_non_conservative_extension_no id.id_label)

let add_decl ?(warn=true) uc d =
  check_decl_opacity d; (* we don't care about tasks *)
  let uc = add_tdecl uc (create_decl d) in
  match d.d_node with
  | Dtype ts  ->
      add_symbol_ts uc ts
  | Ddata dl  ->
      let add_field uc = function
        | Some pj -> add_symbol_ls uc pj
        | None -> uc in
      let add_constr uc (cs,pl) =
        let uc = add_symbol_ls uc cs in
        List.fold_left add_field uc pl in
      let add_data uc (ts,csl) =
        let uc = add_symbol_ts uc ts in
        List.fold_left add_constr uc csl in
      List.fold_left add_data uc dl
  | Dparam ls ->
      add_symbol_ls uc ls
  | Dlogic dl ->
      let add_logic uc (ls,_) = add_symbol_ls uc ls in
      List.fold_left add_logic uc dl
  | Dind (_, dl) ->
      let add_ind uc (ps,la) =
        let uc = add_symbol_ls uc ps in
        let add uc (pr,_) = add_symbol_pr uc pr in
        List.fold_left add uc la in
      List.fold_left add_ind uc dl
  | Dprop (k,pr,_) ->
      if warn && should_be_conservative uc.uc_name &&
        should_be_conservative pr.pr_name
      then warn_dubious_axiom uc k pr.pr_name d.d_syms;
      add_symbol_pr uc pr

(** Declaration constructors + add_decl *)

let add_ty_decl uc ts = add_decl uc (create_ty_decl ts)
let add_data_decl uc dl = add_decl uc (create_data_decl dl)
let add_param_decl uc ls = add_decl uc (create_param_decl ls)
let add_logic_decl uc dl = add_decl uc (create_logic_decl dl)
let add_ind_decl uc s dl = add_decl uc (create_ind_decl s dl)
let add_prop_decl ?warn uc k p f =
  add_decl ?warn uc (create_prop_decl k p f)

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
  mutable ts_table : tysymbol Mts.t;
  mutable ls_table : lsymbol Mls.t;
  mutable pr_table : prsymbol Mpr.t;
}

let empty_clones s = {
  cl_local = s;
  ts_table = Mts.empty;
  ls_table = Mls.empty;
  pr_table = Mpr.empty;
}

(* populate the clone structure *)

let rec cl_find_ts cl ts =
  if not (Sid.mem ts.ts_name cl.cl_local) then
    match ts.ts_def with
      | Alias ty ->
          let td = cl_trans_ty cl ty in
          if ty_equal td ty then ts else
          let id = id_clone ts.ts_name in
          create_tysymbol id ts.ts_args (Alias td)
      | NoDef | Range _ | Float _ -> ts
  else try Mts.find ts cl.ts_table
  with Not_found ->
    let id' = id_clone ts.ts_name in
    let td' = type_def_map (cl_trans_ty cl) ts.ts_def in
    let ts' = create_tysymbol id' ts.ts_args td' in
    cl.ts_table <- Mts.add ts ts' cl.ts_table;
    ts'

and cl_trans_ty cl ty = ty_s_map (cl_find_ts cl) ty

let cl_find_ls cl ls =
  if not (Sid.mem ls.ls_name cl.cl_local) then ls
  else try Mls.find ls cl.ls_table
  with Not_found ->
    let opaque = ls.ls_opaque in
    let constr = ls.ls_constr in
    let id  = id_clone ls.ls_name in
    let ta' = List.map (cl_trans_ty cl) ls.ls_args in
    let vt' = Opt.map (cl_trans_ty cl) ls.ls_value in
    let stv = Opt.fold ty_freevars Stv.empty vt' in
    let stv = List.fold_left ty_freevars stv ta' in
    let opaque = Stv.inter opaque stv in
    let ls' = create_lsymbol ~opaque ~constr id ta' vt' in
    cl.ls_table <- Mls.add ls ls' cl.ls_table;
    ls'

let cl_trans_fmla cl f = t_s_map (cl_trans_ty cl) (cl_find_ls cl) f

let cl_find_pr cl pr =
  if not (Sid.mem pr.pr_name cl.cl_local) then pr
  else try Mpr.find pr cl.pr_table
  with Not_found ->
    let pr' = create_prsymbol (id_clone pr.pr_name) in
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
  let sb = try List.fold_left2 mtch sb ls.ls_args ls'.ls_args
    with Invalid_argument _ -> raise (BadInstance (id, ls'.ls_name))
  in
  check_subst_opacity ls ls' sb;
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

let cl_type cl inst ts =
  if Mts.mem ts inst.inst_ts then
    if ts.ts_def = NoDef then raise EmptyDecl
    else raise (CannotInstantiate ts.ts_name);
  create_ty_decl (cl_find_ts cl ts)

let cl_data cl inst tdl =
  let add_ls ls =
    if Mls.mem ls inst.inst_ls then
      raise (CannotInstantiate ls.ls_name);
    cl_find_ls cl ls
  in
  let add_constr (ls,pl) =
    add_ls ls, List.map (Opt.map add_ls) pl
  in
  let add_type (ts,csl) =
    if Mts.mem ts inst.inst_ts then
      raise (CannotInstantiate ts.ts_name);
    let ts' = cl_find_ts cl ts in
    let td' = List.map add_constr csl in
    (ts',td')
  in
  create_data_decl (List.map add_type tdl)

let extract_ls_defn f =
  let vl,_,f = match f.t_node with
    | Tquant (Tforall,b) -> t_open_quant b
    | _ -> [],[],f in
  match f.t_node with
    | Tapp (_, [{t_node = Tapp (ls,_)}; f])
    | Tbinop (_, {t_node = Tapp (ls,_)}, f) -> make_ls_defn ls vl f
    | _ -> assert false

let cl_param cl inst ls =
  if Mls.mem ls inst.inst_ls then raise EmptyDecl;
  create_param_decl (cl_find_ls cl ls)

let cl_logic cl inst ldl =
  let add_logic (ls,ld) =
    if Mls.mem ls inst.inst_ls then
      raise (CannotInstantiate ls.ls_name);
    let f = ls_defn_axiom ld in
    extract_ls_defn (cl_trans_fmla cl f)
  in
  create_logic_decl (List.map add_logic ldl)

let cl_ind cl inst (s, idl) =
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
  create_ind_decl s (List.map add_ind idl)

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
  | Dtype ts -> cl_type cl inst ts
  | Ddata tdl -> cl_data cl inst tdl
  | Dparam ls -> cl_param cl inst ls
  | Dlogic ldl -> cl_logic cl inst ldl
  | Dind idl -> cl_ind cl inst idl
  | Dprop p -> cl_prop cl inst p

let cl_marg cl = function
  | MAty ty -> MAty (cl_trans_ty cl ty)
  | MAts ts -> MAts (cl_find_ts cl ts)
  | MAls ls -> MAls (cl_find_ls cl ls)
  | MApr pr -> MApr (cl_find_pr cl pr)
  | a -> a

let cl_smap cl sm = {
  sm_ts = Mts.map (cl_find_ts cl) sm.sm_ts;
  sm_ls = Mls.map (cl_find_ls cl) sm.sm_ls;
  sm_pr = Mpr.map (cl_find_pr cl) sm.sm_pr}

let cl_tdecl cl inst td = match td.td_node with
  | Decl d -> Decl (cl_decl cl inst d)
  | Use th -> Use th
  | Clone (th,sm) -> Clone (th, cl_smap cl sm)
  | Meta (id,al) -> Meta (id, List.map (cl_marg cl) al)

let warn_clone_not_abstract loc th =
  try
    List.iter (fun d -> match d.td_node with
      | Decl d ->
        begin match d.d_node with
        | Dtype { ts_def = NoDef }
        | Dparam _ -> raise Exit
        | Dprop(Paxiom, _,_) -> raise Exit
        | _ -> ()
        end
      | _ -> ()
    ) th.th_decls;
    Warning.emit ~loc "cloned theory %a.%s does not contain \
        any abstract symbol; it should be used instead"
      (Pp.print_list (Pp.constant_string ".") Pp.string) th.th_path
      th.th_name.id_string
  with Exit -> ()

let clone_theory cl add_td acc th inst =
  let add acc td =
    let td =
      try  Some (mk_tdecl (cl_tdecl cl inst td))
      with EmptyDecl -> None
    in
    Opt.fold add_td acc td
  in
  let acc = List.fold_left add acc th.th_decls in
  let sm = {
    sm_ts = cl.ts_table;
    sm_ls = cl.ls_table;
    sm_pr = cl.pr_table}
  in
  add_td acc (mk_tdecl (Clone (th, sm)))

let clone_export uc th inst =
  let cl = cl_init th inst in
  let uc = clone_theory cl add_tdecl uc th inst in

  let g_ts _ ts = not (Mts.mem ts inst.inst_ts) in
  let g_ls _ ls = not (Mls.mem ls inst.inst_ls) in

  let f_ts p ts =
    try let ts = Mts.find ts cl.ts_table in store_path uc p ts.ts_name; ts
    with Not_found -> ts in
  let f_ls p ls =
    try let ls = Mls.find ls cl.ls_table in store_path uc p ls.ls_name; ls
    with Not_found -> ls in
  let f_pr p pr =
    try let pr = Mpr.find pr cl.pr_table in store_path uc p pr.pr_name; pr
    with Not_found -> pr in

  let rec f_ns p ns = {
    ns_ts = Mstr.map (f_ts p) (Mstr.filter g_ts ns.ns_ts);
    ns_ls = Mstr.map (f_ls p) (Mstr.filter g_ls ns.ns_ls);
    ns_pr = Mstr.map (f_pr p) ns.ns_pr;
    ns_ns = Mstr.mapi (fun n -> f_ns (n::p)) ns.ns_ns; } in

  let ns = f_ns [] th.th_export in

  match uc.uc_import, uc.uc_export with
    | i0 :: sti, e0 :: ste -> { uc with
        uc_import = merge_ns false ns i0 :: sti;
        uc_export = merge_ns true  ns e0 :: ste; }
    | _ -> assert false

let clone_theory add_td acc th inst =
  clone_theory (cl_init th inst) add_td acc th inst

let create_null_clone th =
  let sm = {
    sm_ts = Mts.empty;
    sm_ls = Mls.empty;
    sm_pr = Mpr.empty}
  in
  mk_tdecl (Clone (th,sm))

let is_empty_sm sm =
  Mts.is_empty sm.sm_ts &&
  Mls.is_empty sm.sm_ls &&
  Mpr.is_empty sm.sm_pr

(** Meta properties *)

let get_meta_arg_type = function
  | MAty  _ -> MTty
  | MAts  _ -> MTtysymbol
  | MAls  _ -> MTlsymbol
  | MApr  _ -> MTprsymbol
  | MAstr _ -> MTstring
  | MAint _ -> MTint

let create_meta m al =
  let get_meta_arg at a =
    (* we allow "constant tysymbol <=> ty" conversion *)
    let a = match at,a with
      | MTtysymbol, MAty ({ ty_node = Tyapp (ts,[]) }) -> MAts ts
      | MTty, MAts ({ts_args = []} as ts) -> MAty (ty_app ts [])
      | _, _ -> a
    in
    let mt = get_meta_arg_type a in
    if at = mt then a else raise (MetaTypeMismatch (m,at,mt))
  in
  let al = try List.map2 get_meta_arg m.meta_type al with
    | Invalid_argument _ -> raise (BadMetaArity (m, List.length al))
  in
  mk_tdecl (Meta (m,al))

let add_meta uc s al = add_tdecl uc (create_meta s al)

let clone_meta tdt sm = match tdt.td_node with
  | Meta (t,al) ->
      let find_ts ts = Mts.find_def ts ts sm.sm_ts in
      let find_ls ls = Mls.find_def ls ls sm.sm_ls in
      let find_pr pr = Mpr.find_def pr pr sm.sm_pr in
      let cl_marg = function
        | MAty ty -> MAty (ty_s_map find_ts ty)
        | MAts ts -> MAts (find_ts ts)
        | MAls ls -> MAls (find_ls ls)
        | MApr pr -> MApr (find_pr pr)
        | a -> a
      in
      mk_tdecl (Meta (t, List.map cl_marg al))
  | _ -> invalid_arg "clone_meta"

(** access to meta *)

(*
let theory_meta = Opt.fold (fun _ t -> t.task_meta) Mmeta.empty

let find_meta_tds th (t : meta) = mm_find (theory_meta th) t

let on_meta meta fn acc theory =
  let add td acc = match td.td_node with
    | Meta (_,ma) -> fn acc ma
    | _ -> assert false
  in
  let tds = find_meta_tds theory meta in
  Stdecl.fold add tds.tds_set acc
*)

(*
let on_meta _meta fn acc theory =
  let tdecls = theory.th_decls in
  List.fold_left
    (fun acc td ->
       match td.td_node with
         | Meta (_,ma) -> fn acc ma
         | _ -> acc)
    acc tdecls
*)


(** Base theories *)

let builtin_theory =
  let uc = empty_theory (id_fresh "BuiltIn") ["why3";"BuiltIn"] in
  let uc = add_ty_decl uc ts_int in
  let uc = add_ty_decl uc ts_real in
  let uc = add_param_decl uc ps_equ in
  close_theory uc

let create_theory ?(path=[]) n =
  use_export (empty_theory n path) builtin_theory

let bool_theory =
  let uc = empty_theory (id_fresh "Bool") ["why3";"Bool"] in
  let uc = add_data_decl uc [ts_bool, [fs_bool_true,[]; fs_bool_false,[]]] in
  close_theory uc

let highord_theory =
  let uc = empty_theory (id_fresh "HighOrd") ["why3";"HighOrd"] in
  let uc = use_export uc bool_theory in
  let uc = add_ty_decl uc ts_func in
  let uc = add_ty_decl uc ts_pred in
  let uc = add_param_decl uc fs_func_app in
  close_theory uc

let tuple_theory = Hint.memo 17 (fun n ->
  let ts = ts_tuple n and fs = fs_tuple n in
  let pl = List.map (fun _ -> None) ts.ts_args in
  let nm = "Tuple" ^ string_of_int n in
  let uc = empty_theory (id_fresh nm) ["why3";nm] in
  let uc = add_data_decl uc [ts, [fs,pl]] in
  close_theory uc)

let unit_theory =
  let uc = empty_theory (id_fresh "Unit") ["why3";"Unit"] in
  let ts = create_tysymbol (id_fresh "unit") [] (Alias (ty_tuple [])) in
  let uc = use_export uc (tuple_theory 0) in
  let uc = add_ty_decl uc ts in
  close_theory uc

let tuple_theory_name s =
  let l = String.length s in
  if l < 6 then None else
  let p = String.sub s 0 5 in
  if p <> "Tuple" then None else
  let q = String.sub s 5 (l - 5) in
  let i = try int_of_string q with _ -> 0 in
  (* we only accept the decimal notation *)
  if q <> string_of_int i then None else
  Some i

let add_decl_with_tuples uc d =
  let ids = Mid.set_diff d.d_syms uc.uc_known in
  let add id s = match is_ts_tuple_id id with
    | Some n -> Sint.add n s
    | None -> s in
  let ixs = Sid.fold add ids Sint.empty in
  let add n uc = use_export uc (tuple_theory n) in
  add_decl (Sint.fold add ixs uc) d

(* Exception reporting *)

let print_meta_arg_type fmt = function
  | MTty -> fprintf fmt "type"
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
  | BadMetaArity (m,n) ->
      let i = List.length m.meta_type in
      Format.fprintf fmt "Metaproperty %s expects %d argument%s but \
        is applied to %d" m.meta_name i (if i = 1 then "" else "s") n
  | MetaTypeMismatch (m,t1,t2) ->
      Format.fprintf fmt "Metaproperty %s expects a %a argument but \
        is applied to %a"
        m.meta_name print_meta_arg_type t1 print_meta_arg_type t2
  | _ -> raise exn
  end
