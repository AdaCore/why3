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
  | Uclone of mod_inst
  | Umeta  of meta * meta_arg list
  | Uscope of string * bool * mod_unit list

and mod_inst = {
  mi_mod : pmodule;
  mi_ty  : ity Mts.t;
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
  | [Uscope (_,_,ul1)], _ :: sti, _ :: ste -> (* empty scope *)
      { uc with muc_theory = th;  muc_units  = ul1;
                muc_import = sti; muc_export = ste; }
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
  mutable ty_table : ity Mts.t;
  mutable ts_table : itysymbol Mts.t;
  mutable ls_table : lsymbol Mls.t;
  mutable pr_table : prsymbol Mpr.t;
  mutable rn_table : region Mreg.t;
  mutable pv_table : pvsymbol Mpv.t;
  mutable rs_table : rsymbol Mrs.t;
  mutable xs_table : xsymbol Mexn.t;
}

let empty_clones m = {
  cl_local = m.mod_local;
  ty_table = Mts.empty;
  ts_table = Mts.empty;
  ls_table = Mls.empty;
  pr_table = Mpr.empty;
  rn_table = Mreg.empty;
  pv_table = Mpv.empty;
  rs_table = Mrs.empty;
  xs_table = Mexn.empty;
}

(* populate the clone structure *)

let rec sm_trans_ty tym tsm ty = match ty.ty_node with
  | Tyapp (s, tl) ->
      let tl = List.map (sm_trans_ty tym tsm) tl in
      begin match Mts.find_opt s tsm with
      | Some its -> ty_app its.its_ts tl
      | None -> begin match Mts.find_opt s tym with
      | Some ity -> ty_inst (ts_match_args s tl) (ty_of_ity ity)
      | None -> ty_app s tl
      end end
  | Tyvar _ -> ty

let cl_trans_ty cl ty = sm_trans_ty cl.ty_table cl.ts_table ty

let cl_find_its cl its =
  if not (Sid.mem its.its_ts.ts_name cl.cl_local) then its
  else Mts.find its.its_ts cl.ts_table

let cl_find_ts cl ts =
  if not (Sid.mem ts.ts_name cl.cl_local) then ts
  else (Mts.find ts cl.ts_table).its_ts

let rec cl_trans_ity cl ity = match ity.ity_node with
  | Ityreg r ->
      ity_reg (cl_trans_reg cl r)
  | Ityapp (s, tl, rl) ->
      let tl = List.map (cl_trans_ity cl) tl in
      let rl = List.map (cl_trans_reg cl) rl in
      begin match Mts.find_opt s.its_ts cl.ts_table with
      | Some its -> ity_app its tl rl
      | None -> begin match Mts.find_opt s.its_ts cl.ty_table with
      | Some ity -> ity_full_inst (its_match_regs s tl rl) ity
      | None -> ity_app s tl rl
      end end
  | Itypur (s, tl) ->
      let tl = List.map (cl_trans_ity cl) tl in
      begin match Mts.find_opt s.its_ts cl.ts_table with
      | Some its -> ity_pur its tl
      | None -> begin match Mts.find_opt s.its_ts cl.ty_table with
      | Some ity -> ity_full_inst (its_match_args s tl) (ity_purify ity)
      | None -> ity_pur s tl
      end end
  | Ityvar _ -> ity

and cl_trans_reg cl reg =
  (* FIXME: what about top-level non-instantiated regions?
     We cannot check in cl.cl_local to see if they are there.
     Instead, we should prefill cl.pv_table and cl.rn_table
     with all top-level pvsymbols (local or external) before
     descending into a let_defn. *)
  try Mreg.find reg cl.rn_table with Not_found ->
  let tl = List.map (cl_trans_ity cl) reg.reg_args in
  let rl = List.map (cl_trans_reg cl) reg.reg_regs in
  let r = match Mts.find_opt reg.reg_its.its_ts cl.ts_table with
    | Some its ->
        create_region (id_clone reg.reg_name) its tl rl
    | None -> begin match Mts.find_opt reg.reg_its.its_ts cl.ty_table with
    | Some {ity_node = Ityreg r} ->
        let sbs = its_match_regs reg.reg_its tl rl in
        let tl = List.map (ity_full_inst sbs) r.reg_args in
        let rl = List.map (reg_full_inst sbs) r.reg_regs in
        create_region (id_clone reg.reg_name) r.reg_its tl rl
    | Some _ -> assert false
    | None ->
        create_region (id_clone reg.reg_name) reg.reg_its tl rl
    end in
  cl.rn_table <- Mreg.add reg r cl.rn_table;
  r

let cl_find_ls cl ls =
  if not (Sid.mem ls.ls_name cl.cl_local) then ls
  else Mls.find ls cl.ls_table

let cl_trans_fmla cl f = t_s_map (cl_trans_ty cl) (cl_find_ls cl) f

let cl_find_pr cl pr =
  if not (Sid.mem pr.pr_name cl.cl_local) then pr
  else Mpr.find pr cl.pr_table

let cl_find_pv cl pv =
  if not (Sid.mem pv.pv_vs.vs_name cl.cl_local) then pv
  else Mpv.find pv cl.pv_table

let cl_find_rs cl rs =
  if not (Sid.mem rs.rs_name cl.cl_local) then rs
  else Mrs.find rs cl.rs_table

let cl_find_xs cl xs =
  if not (Sid.mem xs.xs_name cl.cl_local) then xs
  else Mexn.find xs cl.xs_table

let cl_clone_ls inst cl ls =
  if Mls.mem ls inst.inst_ls then raise (CannotInstantiate ls.ls_name);
  let constr = ls.ls_constr in
  let id = id_clone ls.ls_name in
  let at = List.map (cl_trans_ty cl) ls.ls_args in
  let vt = Opt.map (cl_trans_ty cl) ls.ls_value in
  let ls' = create_lsymbol ~constr id at vt in
  cl.ls_table <- Mls.add ls ls' cl.ls_table;
  ls'

let cl_init_ty cl ({ts_name = id} as ts) ty =
  let rec restore_ity ty = match ty.ty_node with
    | Tyapp (s,tl) ->
        ity_app_fresh (restore_its s) (List.map restore_ity tl)
    | Tyvar v -> ity_var v in
  let its = restore_its ts and ity = restore_ity ty in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  let stv = Stv.of_list ts.ts_args in
  if not (Stv.subset (ity_freevars Stv.empty ity) stv) ||
     its_impure its || not ity.ity_pure then raise (BadInstance id);
  cl.ty_table <- Mts.add ts ity cl.ty_table

let cl_init_ts cl ({ts_name = id} as ts) ts' =
  let its = restore_its ts and its' = restore_its ts' in
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  if List.length ts.ts_args <> List.length ts'.ts_args ||
     its_impure its || its_impure its' then raise (BadInstance id);
  cl.ts_table <- Mts.add its.its_ts its' cl.ts_table

let cl_init_ls cl ({ls_name = id} as ls) ls' =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id);
  let mtch sb ty ty' = try ty_match sb ty' (cl_trans_ty cl ty)
    with TypeMismatch _ -> raise (BadInstance id) in
  let sbs = match ls.ls_value,ls'.ls_value with
    | Some ty, Some ty' -> mtch Mtv.empty ty ty'
    | None, None -> Mtv.empty
    | _ -> raise (BadInstance id) in
  ignore (try List.fold_left2 mtch sbs ls.ls_args ls'.ls_args
    with Invalid_argument _ -> raise (BadInstance id));
  cl.ls_table <- Mls.add ls ls' cl.ls_table

let cl_init_pr cl {pr_name = id} _ =
  if not (Sid.mem id cl.cl_local) then raise (NonLocal id)

let cl_init m inst =
  let cl = empty_clones m in
  Mts.iter (cl_init_ty cl) inst.inst_ty;
  Mts.iter (cl_init_ts cl) inst.inst_ts;
  Mls.iter (cl_init_ls cl) inst.inst_ls;
  Mpr.iter (cl_init_pr cl) inst.inst_pr;
  cl

(* clone declarations *)

let clone_decl inst cl uc d = match d.d_node with
  | Dtype _ | Ddata _ -> assert false (* impossible *)
  | Dparam ls ->
      if Mls.mem ls inst.inst_ls then uc else
      let d = create_param_decl (cl_clone_ls inst cl ls) in
      add_pdecl ~vc:false uc (create_pure_decl d)
  | Dlogic ldl ->
      let get_ls (ls,_) = ignore (cl_clone_ls inst cl ls) in
      let get_logic (_,ld) =
        Opt.get (ls_defn_of_axiom (cl_trans_fmla cl (ls_defn_axiom ld))) in
      List.iter get_ls ldl;
      let d = create_logic_decl (List.map get_logic ldl) in
      add_pdecl ~vc:false uc (create_pure_decl d)
  | Dind (s, idl) ->
      let get_ls (ls,_) = cl_clone_ls inst cl ls in
      let get_case (pr,f) =
        if Mpr.mem pr inst.inst_pr then raise (CannotInstantiate pr.pr_name);
        let pr' = create_prsymbol (id_clone pr.pr_name) in
        cl.pr_table <- Mpr.add pr pr' cl.pr_table;
        pr', cl_trans_fmla cl f in
      let get_ind ls (_,la) = ls, List.map get_case la in
      let lls = List.map get_ls idl in
      let d = create_ind_decl s (List.map2 get_ind lls idl) in
      add_pdecl ~vc:false uc (create_pure_decl d)
  | Dprop (k,pr,f) ->
      let skip, k' = match k, Mpr.find_opt pr inst.inst_pr with
        | Pgoal, _ -> true, Pgoal
        | Plemma, Some Pgoal -> true, Pgoal
        | Plemma, _ -> false, Plemma
        | Paxiom, Some k -> false, k
        | Paxiom, None -> false, Paxiom (* TODO: Plemma *) in
      if skip then uc else
      let pr' = create_prsymbol (id_clone pr.pr_name) in
      cl.pr_table <- Mpr.add pr pr' cl.pr_table;
      let d = create_prop_decl k' pr' (cl_trans_fmla cl f) in
      add_pdecl ~vc:false uc (create_pure_decl d)

let clone_type_decl inst cl tdl =
  let def =
    List.fold_left (fun m d -> Mits.add d.itd_its d m) Mits.empty tdl in
  let htd = Hits.create 5 in

  let rec visit alg ({its_ts = {ts_name = id} as ts} as s) d =
    if not (Hits.mem htd s) then
    let alg = Sits.add s alg in
    let id' = id_clone id in
    let cloned = Mts.mem ts inst.inst_ts || Mts.mem ts inst.inst_ty in
    let conv_pj v = create_pvsymbol
      (id_clone v.pv_vs.vs_name) ~ghost:v.pv_ghost (conv_ity alg v.pv_ity) in
    let save_rs o n =
      cl.rs_table <- Mrs.add o n cl.rs_table;
      match o.rs_logic, n.rs_logic with
      | RLls o, RLls n -> cl.ls_table <- Mls.add o n cl.ls_table;
      | RLnone, RLnone -> () (* constructors with invariants *)
      | _ -> assert false in
    let save_itd itd =
      List.iter2 save_rs d.itd_constructors itd.itd_constructors;
      List.iter2 save_rs d.itd_fields itd.itd_fields;
      Hits.add htd s (Some itd) in
    (* alias *)
    if s.its_def <> None then begin
      if cloned then raise (CannotInstantiate id);
      let def = conv_ity alg (Opt.get s.its_def) in
      let itd = create_alias_decl id' ts.ts_args def in
      cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
      save_itd itd
    end else
    (* abstract *)
    if d.itd_fields = [] && d.itd_constructors = [] &&
                            d.itd_invariant = [] then begin
      if cloned then Hits.add htd s None else begin
        let itd = create_abstract_type_decl id' ts.ts_args s.its_privmut in
        cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
        save_itd itd
      end
    end else
    (* variant *)
    if s.its_mfields = [] && d.itd_constructors <> [] &&
                             d.itd_invariant = [] then begin
      if cloned then raise (CannotInstantiate id);
      let conv_fd m fd =
        let v = Opt.get fd.rs_field in Mpv.add v (conv_pj v) m in
      let fldm = List.fold_left conv_fd Mpv.empty d.itd_fields in
      let conv_pj pj = match Mpv.find_opt pj fldm with
        | Some pj' -> true, pj' | None -> false, conv_pj pj in
      let conv_cs cs =
        id_clone cs.rs_name, List.map conv_pj cs.rs_cty.cty_args in
      let csl = List.map conv_cs d.itd_constructors in
      match Mts.find_opt ts cl.ts_table with
      | Some s' ->
          let itd = create_rec_variant_decl s' csl in
          save_itd itd
      | None ->
          let itd = create_flat_variant_decl id' ts.ts_args csl in
          cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
          save_itd itd
    end else begin
    (* flat record *)
      if cloned then raise (CannotInstantiate id);
      let mfld = Spv.of_list s.its_mfields in
      let priv = d.itd_constructors = [] in
      let mut = its_mutable s in
      let pjl = List.map (fun fd -> Opt.get fd.rs_field) d.itd_fields in
      let fdl = List.map (fun v -> Spv.mem v mfld, conv_pj v) pjl in
      let inv =
        if d.itd_invariant = [] then [] else
        if d.itd_fields = [] then
          List.map (cl_trans_fmla cl) d.itd_invariant else
        let ovl = List.map (fun v -> v.pv_vs) pjl in
        let nvl = List.map (fun (_,v) -> t_var v.pv_vs) fdl in
        let conv_inv f =
          let f = t_exists_close ovl [] f in
          match (cl_trans_fmla cl f).t_node with
          | Tquant (Texists, tq) ->
              let xvl,_,f = t_open_quant tq in
              let add s xv nv = Mvs.add xv nv s in
              t_subst (List.fold_left2 add Mvs.empty xvl nvl) f
          | _ -> assert false (* can't be *) in
        List.map conv_inv d.itd_invariant in
      let itd = create_flat_record_decl id' ts.ts_args priv mut fdl inv in
      cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
      save_itd itd
    end

  and conv_ity alg ity =
    let rec down ity = match ity.ity_node with
      | Ityreg {reg_its = s; reg_args = tl}
      | Ityapp (s,tl,_) | Itypur (s,tl) ->
          if Sits.mem s alg then begin
            if not (Mts.mem s.its_ts cl.ts_table) then
            let id = id_clone s.its_ts.ts_name in
            let s = create_itysymbol_pure id s.its_ts.ts_args in
            cl.ts_table <- Mts.add s.its_ts s cl.ts_table
          end else Opt.iter (visit alg s) (Mits.find_opt s def);
          List.iter down tl
      | Ityvar _ -> () in
    down ity;
    cl_trans_ity cl ity in

  Mits.iter (visit Sits.empty) def;
  Lists.map_filter (fun d -> Hits.find htd d.itd_its) tdl

let clone_pdecl inst cl uc d = match d.pd_node with
  | PDtype tdl ->
      let tdl = clone_type_decl inst cl tdl in
      if tdl = [] then uc else
      add_pdecl ~vc:false uc (create_type_decl tdl)
  | PDlet _ld ->
      assert false (* TODO *)
  | PDexn xs ->
      let ity = cl_trans_ity cl xs.xs_ity in
      let xs' = create_xsymbol (id_clone xs.xs_name) ity in
      cl.xs_table <- Mexn.add xs xs' cl.xs_table;
      add_pdecl ~vc:false uc (create_exn_decl xs')
  | PDpure ->
      List.fold_left (clone_decl inst cl) uc d.pd_pure

let theory_add_clone = Theory.add_clone_internal ()

let add_clone uc mi =
  let sm = {
    sm_ty = Mts.map ty_of_ity mi.mi_ty;
    sm_ts = Mts.map (fun s -> s.its_ts) mi.mi_ts;
    sm_ls = mi.mi_ls;
    sm_pr = mi.mi_pr } in
  { uc with
      muc_theory = theory_add_clone uc.muc_theory mi.mi_mod.mod_theory sm;
      muc_units  = Uclone mi :: uc.muc_units }

let clone_export uc m inst =
  let cl = cl_init m inst in
  let rec add_unit uc u = match u with
    | Udecl d -> clone_pdecl inst cl uc d
    | Uuse m -> use_export uc m
    | Uclone mi ->
        begin try add_clone uc { mi_mod = mi.mi_mod;
          mi_ty = Mts.map (cl_trans_ity cl) mi.mi_ty;
          mi_ts = Mts.map (cl_find_its cl) mi.mi_ts;
          mi_ls = Mls.map (cl_find_ls cl) mi.mi_ls;
          mi_pr = Mpr.map (cl_find_pr cl) mi.mi_pr;
          mi_pv = Mpv.map (cl_find_pv cl) mi.mi_pv;
          mi_rs = Mrs.map (cl_find_rs cl) mi.mi_rs;
          mi_xs = Mexn.map (cl_find_xs cl) mi.mi_xs}
        with Not_found -> uc end
    | Umeta (m,al) ->
        begin try add_meta uc m (List.map (function
          | MAty ty -> MAty (cl_trans_ty cl ty)
          | MAts ts -> MAts (cl_find_ts cl ts)
          | MAls ls -> MAls (cl_find_ls cl ls)
          | MApr pr -> MApr (cl_find_pr cl pr)
          | a -> a) al)
        with Not_found -> uc end
    | Uscope (n,import,ul) ->
        let uc = open_scope uc n in
        let uc = List.fold_left add_unit uc ul in
        close_scope ~import uc in
  let uc = List.fold_left add_unit uc m.mod_units in
  let mi = {
    mi_mod = m;
    mi_ty  = cl.ty_table;
    mi_ts  = cl.ts_table;
    mi_ls  = cl.ls_table;
    mi_pr  = cl.pr_table;
    mi_pv  = cl.pv_table;
    mi_rs  = cl.rs_table;
    mi_xs  = cl.xs_table} in
  add_clone uc mi

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
  | Uclone mi -> Format.fprintf fmt "clone export %a with ..."
      print_mname mi.mi_mod
  | Umeta (m,al) -> Format.fprintf fmt "@[<hov 2>meta %s %a@]"
      m.meta_name (Pp.print_list Pp.comma Pretty.print_meta_arg) al
  | Uscope (s,i,[Uuse m]) -> Format.fprintf fmt "use%s %a%s"
      (if i then " import" else "") print_mname m
      (if s = m.mod_theory.th_name.id_string then "" else " as " ^ s)
  | Uscope (s,i,[Uclone mi]) -> Format.fprintf fmt "clone%s %a%s with ..."
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
