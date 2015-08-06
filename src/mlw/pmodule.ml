(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term
open Decl
open Theory
open Ity
open Expr
open Pdecl

(** *)

type prog_symbol =
  | PV of pvsymbol
  | RS of rsymbol

type namespace = {
  ns_ts : itysymbol   Mstr.t;  (* type symbols *)
  ns_ps : prog_symbol Mstr.t;  (* program symbols *)
  ns_xs : xsymbol     Mstr.t;  (* exception symbols *)
  ns_ns : namespace   Mstr.t;  (* inner namespaces *)
}

let empty_ns = {
  ns_ts = Mstr.empty;
  ns_ps = Mstr.empty;
  ns_xs = Mstr.empty;
  ns_ns = Mstr.empty;
}

let ns_replace eq chk x vo vn =
  if not chk then vn else
  if eq vo vn then vn else
  raise (ClashSymbol x)

let psym_equal p1 p2 = match p1,p2 with
  | PV p1, PV p2 -> pv_equal p1 p2
  | RS p1, RS p2 -> rs_equal p1 p2
  | _, _ -> false

let rec merge_ns chk ns1 ns2 =
  if ns1 == ns2 then ns1 else
  let join eq x n o = Some (ns_replace eq chk x o n) in
  let ns_union eq m1 m2 =
    if m1 == m2 then m1 else Mstr.union (join eq) m1 m2 in
  let fusion _ ns1 ns2 = Some (merge_ns chk ns1 ns2) in
  { ns_ts = ns_union its_equal ns1.ns_ts ns2.ns_ts;
    ns_ps = ns_union psym_equal ns1.ns_ps ns2.ns_ps;
    ns_xs = ns_union xs_equal ns1.ns_xs ns2.ns_xs;
    ns_ns = Mstr.union fusion ns1.ns_ns ns2.ns_ns; }

let add_ns chk x ns m = Mstr.change (function
  | Some os -> Some (merge_ns chk ns os)
  | None    -> Some ns) x m

let ns_add eq chk x vn m = Mstr.change (function
  | Some vo -> Some (ns_replace eq chk x vo vn)
  | None    -> Some vn) x m

let add_xs chk x xs ns = { ns with ns_xs = ns_add xs_equal   chk x xs ns.ns_xs }
let add_ts chk x ts ns = { ns with ns_ts = ns_add its_equal  chk x ts ns.ns_ts }
let add_ps chk x ps ns = { ns with ns_ps = ns_add psym_equal chk x ps ns.ns_ps }
let add_ns chk x nn ns = { ns with ns_ns = add_ns            chk x nn ns.ns_ns }

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_prog_symbol = ns_find (fun ns -> ns.ns_ps)
let ns_find_ns          = ns_find (fun ns -> ns.ns_ns)
let ns_find_xs          = ns_find (fun ns -> ns.ns_xs)
let ns_find_its         = ns_find (fun ns -> ns.ns_ts)

let ns_find_pv ns s = match ns_find_prog_symbol ns s with
  | PV pv -> pv | _ -> raise Not_found

let ns_find_rs ns s = match ns_find_prog_symbol ns s with
  | RS rs -> rs | _ -> raise Not_found

(** {2 Module} *)

type pmodule = {
  mod_theory : theory;        (* pure theory *)
  mod_units  : mod_unit list; (* module declarations *)
  mod_export : namespace;     (* exported namespace *)
  mod_known  : known_map;     (* known identifiers *)
  mod_local  : Sid.t;         (* locally declared idents *)
  mod_used   : Sid.t;         (* used modules *)
}

and mod_unit =
  | Udecl  of pdecl
  | Uuse   of pmodule
  | Uinst  of mod_inst
  | Umeta  of meta * meta_arg list
  | Uscope of string * bool * mod_unit list

and mod_inst = private {
  mi_mod : pmodule;
  mi_ts  : itysymbol Mts.t;
  mi_ls  : lsymbol Mls.t;
  mi_pr  : prsymbol Mpr.t;
  mi_pv  : pvsymbol Mpv.t;
  mi_rs  : rsymbol Mrs.t;
  mi_xs  : xsymbol Mexn.t;
}

(** {2 Module under construction} *)

type pmodule_uc = {
  muc_theory : theory_uc;
  muc_units  : mod_unit list;
  muc_import : namespace list;
  muc_export : namespace list;
  muc_known  : known_map;
  muc_local  : Sid.t;
  muc_used   : Sid.t;
  muc_env    : Env.env option;
}

let empty_module env n p = {
  muc_theory = create_theory ~path:p n;
  muc_units  = [];
  muc_import = [empty_ns];
  muc_export = [empty_ns];
  muc_known  = Mid.empty;
  muc_local  = Sid.empty;
  muc_used   = Sid.empty;
  muc_env    = env;
}

let close_module, restore_module =
  let h = Hid.create 17 in
  (fun uc ->
     let th = close_theory uc.muc_theory in (* catches errors *)
     let m = { mod_theory = th;
               mod_units  = List.rev uc.muc_units;
               mod_export = List.hd uc.muc_export;
               mod_known  = uc.muc_known;
               mod_local  = uc.muc_local;
               mod_used   = uc.muc_used; } in
     Hid.add h th.th_name m;
     m),
  (fun th -> Hid.find h th.th_name)

let open_scope uc s = match uc.muc_import with
  | ns :: _ -> { uc with
      muc_theory = Theory.open_scope uc.muc_theory s;
      muc_units  = [Uscope (s, false, uc.muc_units)];
      muc_import =       ns :: uc.muc_import;
      muc_export = empty_ns :: uc.muc_export; }
  | [] -> assert false

let close_scope uc ~import =
  let th = Theory.close_scope uc.muc_theory ~import in
  match List.rev uc.muc_units, uc.muc_import, uc.muc_export with
  | Uscope (s,_,ul1) :: ul0, _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = add_ns false s e0 i1 in
      let e1 = add_ns true  s e0 e1 in
      { uc with
          muc_theory = th;
          muc_units  = Uscope (s, import, ul0) :: ul1;
          muc_import = i1 :: sti;
          muc_export = e1 :: ste; }
  | _ -> assert false

let use_export uc ({mod_theory = mth} as m) =
  let th = Theory.use_export uc.muc_theory mth in
  let uc = if Sid.mem mth.th_name uc.muc_used then uc
    else { uc with
      muc_known = merge_known uc.muc_known m.mod_known;
      muc_used  = Sid.add mth.th_name uc.muc_used } in
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_theory = th;
      muc_units  = Uuse m :: uc.muc_units;
      muc_import = merge_ns false m.mod_export i0 :: sti;
      muc_export = merge_ns true  m.mod_export e0 :: ste; }
  | _ -> assert false

let add_meta uc m al = { uc with
  muc_theory = Theory.add_meta uc.muc_theory m al;
  muc_units  = Umeta (m,al) :: uc.muc_units; }

let store_path, store_module, restore_path =
  let id_to_path = Wid.create 17 in
  let store_path {muc_theory = uc} path id =
    (* this symbol already belongs to some theory *)
    if Wid.mem id_to_path id then () else
    let prefix = List.rev (id.id_string :: path @ uc.uc_prefix) in
    Wid.set id_to_path id (uc.uc_path, uc.uc_name.id_string, prefix) in
  let store_module {mod_theory = {th_name = id} as th} =
    (* this symbol is already a module *)
    if Wid.mem id_to_path id then () else
    Wid.set id_to_path id (th.th_path, id.id_string, []) in
  let restore_path id = Wid.find id_to_path id in
  store_path, store_module, restore_path

let close_module uc =
  let m = close_module uc in
  store_module m;
  m

let count_regions {muc_known = kn} {pv_ity = ity} mr =
  let add_reg r mr = Mreg.change (fun n -> Some (n <> None)) r mr in
  let meet mr1 mr2 = Mreg.union (fun _ x y -> Some (x || y)) mr1 mr2 in
  let join mr1 mr2 = Mreg.union (fun _ _ _ -> Some true) mr1 mr2 in
  let rec down mr ity = if ity.ity_pure then mr else
    match ity.ity_node with
    | Ityreg r -> fields (add_reg r mr) r.reg_its r.reg_args r.reg_regs
    | Ityapp (s,tl,rl) -> fields mr s tl rl
    | Itypur (s,tl) -> fields mr s tl []
    | Ityvar _ -> assert false
  and fields mr s tl rl = if s.its_privmut then mr else
    let add_arg isb v ity = ity_match isb (ity_var v) ity in
    let isb = List.fold_left2 add_arg isb_empty s.its_ts.ts_args tl in
    let isb = List.fold_left2 reg_match isb s.its_regions rl in
    let add_ity mr ity = down mr (ity_full_inst isb ity) in
    let add_proj mr f = add_ity mr f.rs_cty.cty_result in
    let add_field mr v = add_ity mr v.pv_ity in
    let d = find_its_defn kn s in
    if d.itd_constructors = [] then
      List.fold_left add_proj mr d.itd_fields
    else
      join mr (List.fold_left (fun mr c ->
        meet mr (List.fold_left add_field Mreg.empty c.rs_cty.cty_args))
        Mreg.empty d.itd_constructors) in
  down mr ity

let add_symbol add id v uc =
  store_path uc [] id;
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_import = add false id.id_string v i0 :: sti;
      muc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_pdecl uc d =
  let uc = { uc with
    muc_units = Udecl d :: uc.muc_units;
    muc_known = known_add_decl uc.muc_known d;
    muc_local = Sid.union uc.muc_local d.pd_news } in
  let add_rs uc s = add_symbol add_ps s.rs_name (RS s) uc in
  let add_rs_noalias uc s = match s.rs_logic with
    | RLls _ | RLlemma ->
        let sv = s.rs_cty.cty_effect.eff_reads in
        let mr = Spv.fold (count_regions uc) sv Mreg.empty in
        Mreg.iter (fun _ n ->
          if n then Loc.errorm ?loc:s.rs_name.id_loc
            "The type of this function contains an alias") mr;
        add_rs uc s
    | _ -> add_rs uc s in
  let add_rd uc d = add_rs_noalias uc d.rec_sym in
  match d.pd_node with
  | PDtype tdl ->
      let add uc d =
        let uc = List.fold_left add_rs uc d.itd_fields in
        let uc = List.fold_left add_rs uc d.itd_constructors in
        add_symbol add_ts d.itd_its.its_ts.ts_name d.itd_its uc in
      List.fold_left add uc tdl
  | PDlet (LDvar (v,_)) -> add_symbol add_ps v.pv_vs.vs_name (PV v) uc
  | PDlet (LDsym (s,_)) -> add_rs_noalias uc s
  | PDlet (LDrec l) -> List.fold_left add_rd uc l
  | PDexn xs -> add_symbol add_xs xs.xs_name xs uc
  | PDpure -> uc

(** {2 Builtin symbols} *)

let builtin_module =
  let uc = empty_module None (id_fresh "BuiltIn") ["why3";"BuiltIn"] in
  let uc = add_pdecl uc pd_int in
  let uc = add_pdecl uc pd_real in
  let uc = add_pdecl uc pd_equ in
  let m = close_module uc in
  { m with mod_theory = builtin_theory }

let bool_module =
  let uc = empty_module None (id_fresh "Bool") ["why3";"Bool"] in
  let uc = add_pdecl uc pd_bool in
  let m = close_module uc in
  { m with mod_theory = bool_theory }

let highord_module =
  let uc = empty_module None (id_fresh "HighOrd") ["why3";"HighOrd"] in
  let uc = use_export uc bool_module in
  let uc = add_pdecl uc pd_func in
  let uc = add_pdecl uc pd_pred in
  let uc = add_pdecl uc pd_func_app in
  let m = close_module uc in
  { m with mod_theory = highord_theory }

let tuple_module = Hint.memo 17 (fun n ->
  let nm = "Tuple" ^ string_of_int n in
  let uc = empty_module None (id_fresh nm) ["why3";nm] in
  let uc = add_pdecl uc (pd_tuple n) in
  let m = close_module uc in
  { m with mod_theory = tuple_theory n })

let unit_module =
  let uc = empty_module None (id_fresh "Unit") ["why3";"Unit"] in
  let uc = use_export uc (tuple_module 0) in
  let td = create_alias_decl (id_fresh "unit") [] ity_unit in
  let uc = add_pdecl uc (create_type_decl [td]) in
  close_module uc

let create_module env ?(path=[]) n =
  let m = empty_module (Some env) n path in
  let m = use_export m builtin_module in
  let m = use_export m bool_module in
  let m = use_export m unit_module in
  m

let add_pdecl ~vc uc d =
  let ids = Mid.set_diff d.pd_syms uc.muc_known in
  let uc = Sid.fold (fun id uc ->
    if id_equal id ts_func.ts_name then
      use_export uc highord_module
    else match is_ts_tuple_id id with
    | Some n -> use_export uc (tuple_module n)
    | None -> uc) ids uc in
  ignore vc; (* TODO *)
  let uc = add_pdecl uc d in
  let th = List.fold_left add_decl uc.muc_theory d.pd_pure in
  { uc with muc_theory = th }

(** {2 Cloning} *)

type clones = {
  cl_local : Sid.t;
  mutable ts_table : itysymbol Mts.t;
  mutable ls_table : lsymbol Mls.t;
  mutable pr_table : prsymbol Mpr.t;
  mutable rn_table : region Mreg.t;
  mutable pv_table : pvsymbol Mpv.t;
  mutable rs_table : rsymbol Mrs.t;
  mutable xs_table : xsymbol Mexn.t;
}

let empty_clones s = {
  cl_local = s;
  ts_table = Mts.empty;
  ls_table = Mls.empty;
  pr_table = Mpr.empty;
  rn_table = Mreg.empty;
  pv_table = Mpv.empty;
  rs_table = Mrs.empty;
  xs_table = Mexn.empty;
}

(* populate the clone structure *)

let rec cl_find_its cl its =
  if not (Sid.mem its.its_ts.ts_name cl.cl_local) then
    match its.its_def with
    | Some _ -> cl_make_its_alias cl its
    | None -> its
  else try Mts.find its.its_ts cl.ts_table
  with Not_found -> cl_make_its_pure cl its

and cl_find_ts cl ts =
  if not (Sid.mem ts.ts_name cl.cl_local) then
    match ts.ts_def with
    | Some _ -> (cl_make_its_alias cl (restore_its ts)).its_ts
    | None -> ts
  else try (Mts.find ts cl.ts_table).its_ts
  with Not_found -> (cl_make_its_pure cl (restore_its ts)).its_ts

and cl_make_its_pure cl ({its_ts = ts} as its) =
  let id = id_clone ts.ts_name in
  let nts = match its.its_def with
    | Some def -> create_itysymbol_alias id ts.ts_args (cl_trans_ity cl def)
    | None -> create_itysymbol_pure id ts.ts_args in
  cl.ts_table <- Mts.add its.its_ts nts cl.ts_table;
  nts

and cl_make_its_alias cl its =
  let odf = Opt.get its.its_def in
  let ndf = cl_trans_ity cl odf in
  if ity_equal odf ndf then its else
  create_itysymbol_alias (id_clone its.its_ts.ts_name) its.its_ts.ts_args ndf

and cl_trans_ity cl ity = match ity.ity_node with
  | Ityreg r -> ity_reg (cl_trans_reg cl r)
  | Ityapp (s,tl,rl) ->
      ity_app (cl_find_its cl s) (List.map (cl_trans_ity cl) tl)
                                 (List.map (cl_trans_reg cl) rl)
  | Itypur (s,tl) ->
      ity_pur (cl_find_its cl s) (List.map (cl_trans_ity cl) tl)
  | Ityvar _ -> ity

and cl_trans_reg cl reg =
  (* FIXME: what about global non-instantiated regions? *)
  try Mreg.find reg cl.rn_table with Not_found ->
    let r = create_region (id_clone reg.reg_name)
      (cl_find_its cl reg.reg_its) (List.map (cl_trans_ity cl) reg.reg_args)
                                   (List.map (cl_trans_reg cl) reg.reg_regs) in
    cl.rn_table <- Mreg.add reg r cl.rn_table;
    r

and cl_trans_ty cl ty = ty_s_map (cl_find_ts cl) ty

let cl_find_ls cl ls =
  if not (Sid.mem ls.ls_name cl.cl_local) then ls
  else (*try*) Mls.find ls cl.ls_table
(*
  with Not_found ->
    let constr = ls.ls_constr in
    let id  = id_clone ls.ls_name in
    let ta' = List.map (cl_trans_ty cl) ls.ls_args in
    let vt' = Opt.map (cl_trans_ty cl) ls.ls_value in
    let ls' = create_lsymbol ~constr id ta' vt' in
    cl.ls_table <- Mls.add ls ls' cl.ls_table;
    ls'
*)

let _cl_trans_fmla cl f = t_s_map (cl_trans_ty cl) (cl_find_ls cl) f

let _cl_find_pr cl pr =
  if not (Sid.mem pr.pr_name cl.cl_local) then pr
  else (*try*) Mpr.find pr cl.pr_table
(*
  with Not_found ->
    let pr' = create_prsymbol (id_clone pr.pr_name) in
    cl.pr_table <- Mpr.add pr pr' cl.pr_table;
    pr'
*)

let _cl_find_pv cl pv =
  if not (Sid.mem pv.pv_vs.vs_name cl.cl_local) then pv
  else Mpv.find pv cl.pv_table

let _cl_find_rs cl rs =
  if not (Sid.mem rs.rs_name cl.cl_local) then rs
  else Mrs.find rs cl.rs_table

let _cl_find_xs cl xs =
  if not (Sid.mem xs.xs_name cl.cl_local) then xs
  else Mexn.find xs cl.xs_table

(* initialize the clone structure *)

let cl_init_ts cl ({ts_name = id} as ts) ts' =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
(* TODO: check later
  if List.length ts.ts_args <> List.length ts'.ts_args
    then raise (BadInstance (id, ts'.ts_name));
*)
  cl.ts_table <- Mts.add ts (restore_its ts') cl.ts_table

let cl_init_ls cl ({ls_name = id} as ls) ls' =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
(* TODO: check later
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
*)
  cl.ls_table <- Mls.add ls ls' cl.ls_table

let cl_init_pr cl {pr_name = id} =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id)

let _cl_init th inst =
  let cl = empty_clones th.th_local in
  Mts.iter (cl_init_ts cl) inst.inst_ts;
  Mls.iter (cl_init_ls cl) inst.inst_ls;
  Spr.iter (cl_init_pr cl) inst.inst_lemma;
  Spr.iter (cl_init_pr cl) inst.inst_goal;
  cl

(* clone declarations *)

(*
let cl_type cl inst ts =
  if Mts.mem ts inst.inst_ts then
    if ts.ts_def = None then raise EmptyDecl
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

let clone_export muc m inst =
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
*)
let clone_export _muc _m _inst = assert false (* TODO *)

(** {2 WhyML language} *)

type mlw_file = pmodule Mstr.t

let convert mm =
  let convert m = m.mod_theory in
  if Mstr.is_empty mm then Mstr.empty else
  match (snd (Mstr.choose mm)).mod_theory.th_path with
  | "why3" :: path ->
      begin try Env.base_language_builtin path
      with Not_found -> Mstr.map convert mm end
  | _ -> Mstr.map convert mm

let mlw_language = Env.register_language Env.base_language convert

module Hpath = Exthtbl.Make(struct
  type t = Env.pathname
  let hash = Hashtbl.hash
  let equal = (=)
end)

let mlw_language_builtin =
  let builtin s =
    if s = unit_module.mod_theory.th_name.id_string then unit_module else
    if s = builtin_theory.th_name.id_string then builtin_module else
    if s = highord_theory.th_name.id_string then highord_module else
    if s = bool_theory.th_name.id_string then bool_module else
    match tuple_theory_name s with
    | Some n -> tuple_module n
    | None -> raise Not_found in
  Hpath.memo 7 (function
    | [s] -> Mstr.singleton s (builtin s)
    | _   -> raise Not_found)

let () = Env.add_builtin mlw_language mlw_language_builtin

exception ModuleNotFound of Env.pathname * string

let read_module env path s =
  let path = if path = [] then ["why3"; s] else path in
  let mm = Env.read_library mlw_language env path in
  Mstr.find_exn (ModuleNotFound (path,s)) s mm

(* pretty-printing *)

let print_path fmt sl =
  Pp.print_list (Pp.constant_string ".") Format.pp_print_string fmt sl

let print_mname fmt {mod_theory = th} =
  List.iter (fun s ->
    Format.pp_print_string fmt s;
    Format.pp_print_char fmt '.') th.th_path;
  Format.pp_print_string fmt th.th_name.id_string

let rec print_unit fmt = function
  | Udecl d -> Pdecl.print_pdecl fmt d
  | Uuse m -> Format.fprintf fmt "use export %a" print_mname m
  | Uinst mi -> Format.fprintf fmt "clone export %a with ..."
      print_mname mi.mi_mod
  | Umeta (m,al) -> Format.fprintf fmt "@[<hov 2>meta %s %a@]"
      m.meta_name (Pp.print_list Pp.comma Pretty.print_meta_arg) al
  | Uscope (s,i,[Uuse m]) -> Format.fprintf fmt "use%s %a%s"
      (if i then " import" else "") print_mname m
      (if s = m.mod_theory.th_name.id_string then "" else " as " ^ s)
  | Uscope (s,i,[Uinst mi]) -> Format.fprintf fmt "clone%s %a%s with ..."
      (if i then " import" else "") print_mname mi.mi_mod
      (if s = mi.mi_mod.mod_theory.th_name.id_string then "" else " as " ^ s)
  | Uscope (s,i,ul) -> Format.fprintf fmt "@[<hov 2>scope%s %s@\n%a@]@\nend"
      (if i then " import" else "") s (Pp.print_list Pp.newline2 print_unit) ul

let print_module fmt m = Format.fprintf fmt
  "@[<hov 2>module %s@\n%a@]@\nend" m.mod_theory.th_name.id_string
  (Pp.print_list Pp.newline2 print_unit) m.mod_units

let () = Exn_printer.register (fun fmt e -> match e with
  | ModuleNotFound (sl,s) -> Format.fprintf fmt
      "Module %s not found in library %a" s print_path sl
  | _ -> raise e)
