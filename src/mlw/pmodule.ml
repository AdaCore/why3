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

open Wstdlib
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
  | OO of Srs.t

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
  if eq vo vn then vo else
  raise (ClashSymbol x)

let merge_ts = ns_replace its_equal
let merge_xs = ns_replace xs_equal

type overload =
  | FixedRes of ity (* t -> t -> ... -> T *)
  | SameType        (* t -> t -> ... -> t *)
  | NoOver          (* neither *)

let overload_of_rs {rs_cty = cty} =
  if cty.cty_effect.eff_ghost then NoOver else
  if cty.cty_mask <> MaskVisible then NoOver else
  let same_type ity a = not a.pv_ghost && ity_equal a.pv_ity ity in
  match cty.cty_args with
  | a::al when not a.pv_ghost && List.for_all (same_type a.pv_ity) al ->
      let res = cty.cty_result in
      if ity_equal res a.pv_ity then SameType else
      if ity_closed res && res.ity_pure then FixedRes res else NoOver
  | _ -> NoOver

let same_overload r1 r2 =
  List.length r1.rs_cty.cty_args = List.length r2.rs_cty.cty_args &&
  match overload_of_rs r1, overload_of_rs r2 with
  | SameType, SameType -> true
  | FixedRes t1, FixedRes t2 -> ity_equal t1 t2
  | _ -> false (* two NoOver's are not the same *)

let ref_attr = Ident.create_attribute "mlw:reference_var"

let has_ref s =
  let has v = Sattr.mem ref_attr v.pv_vs.vs_name.id_attrs in
  List.exists has s.rs_cty.cty_args

exception IncompatibleNotation of string

let merge_ps chk x vo vn =
  let fsty rs = (List.hd rs.rs_cty.cty_args).pv_ity in
  if chk then match vo, vn with (* export namespace *)
    (* currently, we have no way to export notation *)
    | _, OO _ | OO _, _ -> assert false
    | PV v1, PV v2 when pv_equal v1 v2 -> vo
    | RS r1, RS r2 when rs_equal r1 r2 -> vo
    | _ -> raise (ClashSymbol x)
  else match vo, vn with (* import namespace *)
    (* once again, no way to export notation *)
    | _, OO _ -> assert false
    (* but we can merge two compatible symbols *)
    | RS r1, RS r2 ->
        if rs_equal r1 r2 then vo else
        if has_ref r1 || has_ref r2 then vn else
        if not (same_overload r1 r2) then vn else
        if ity_equal (fsty r1) (fsty r2) then vn else
        OO (Srs.add r2 (Srs.singleton r1))
    (* or add a compatible symbol to notation *)
    | OO s1, RS r2 ->
        if Srs.mem r2 s1 then vo else
        if has_ref r2 then vn else
        let r1 = Srs.choose s1 in
        if not (same_overload r1 r2) then vn else
        let ty = fsty r2 in
        let confl r = not (ity_equal (fsty r) ty) in
        let s1 = Srs.filter confl s1 in
        if Srs.is_empty s1 then vn else
        OO (Srs.add r2 s1)
    | _ -> vn

let rec merge_ns chk _ no nn =
  if no == nn then no else
  let union merge o n =
    let merge x vo vn = Some (merge chk x vo vn) in
    if o == n then o else Mstr.union merge o n in
  { ns_ts = union merge_ts no.ns_ts nn.ns_ts;
    ns_ps = union merge_ps no.ns_ps nn.ns_ps;
    ns_xs = union merge_xs no.ns_xs nn.ns_xs;
    ns_ns = union merge_ns no.ns_ns nn.ns_ns }

let ns_add merge chk x vn m = Mstr.change (function
  | Some vo -> Some (merge chk x vo vn)
  | None    -> Some vn) x m

let add_ts chk x ts ns = { ns with ns_ts = ns_add merge_ts chk x ts ns.ns_ts }
let add_ps chk x ps ns = { ns with ns_ps = ns_add merge_ps chk x ps ns.ns_ps }
let add_xs chk x xs ns = { ns with ns_xs = ns_add merge_xs chk x xs ns.ns_xs }
let add_ns chk x nn ns = { ns with ns_ns = ns_add merge_ns chk x nn ns.ns_ns }

let merge_ns chk nn no = merge_ns chk "" no nn (* swap arguments *)

let rec ns_find get_map ns = function
  | []   -> assert false
  | [a]  -> Mstr.find a (get_map ns)
  | a::l -> ns_find get_map (Mstr.find a ns.ns_ns) l

let ns_find_its = ns_find (fun ns -> ns.ns_ts)
let ns_find_xs  = ns_find (fun ns -> ns.ns_xs)
let ns_find_ns  = ns_find (fun ns -> ns.ns_ns)

let ns_find_prog_symbol ns s =
  let ps = ns_find (fun ns -> ns.ns_ps) ns s in
  match ps with
  | RS _ | PV _ -> ps
  | OO ss ->
      let rs1 = Expr.Srs.min_elt ss in
      let rs2 = Expr.Srs.max_elt ss in
      if Expr.rs_equal rs1 rs2 then RS rs1 else ps

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
  | Uscope of string * mod_unit list

and mod_inst = {
  mi_mod : pmodule;
  mi_ty  : ity Mts.t;
  mi_ts  : itysymbol Mts.t;
  mi_ls  : lsymbol Mls.t;
  mi_pr  : prsymbol Mpr.t;
  mi_pk  : prop_kind Mpr.t;
  mi_pv  : pvsymbol Mvs.t;
  mi_rs  : rsymbol Mrs.t;
  mi_xs  : xsymbol Mxs.t;
  mi_df  : prop_kind;
}

let empty_mod_inst m = {
  mi_mod = m;
  mi_ty  = Mts.empty;
  mi_ts  = Mts.empty;
  mi_ls  = Mls.empty;
  mi_pr  = Mpr.empty;
  mi_pk  = Mpr.empty;
  mi_pv  = Mvs.empty;
  mi_rs  = Mrs.empty;
  mi_xs  = Mxs.empty;
  mi_df  = Plemma;
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
  muc_env    : Env.env;
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
      muc_units  = [Uscope (s, uc.muc_units)];
      muc_import =       ns :: uc.muc_import;
      muc_export = empty_ns :: uc.muc_export; }
  | [] -> assert false

let close_scope uc ~import =
  let th = Theory.close_scope uc.muc_theory ~import in
  match List.rev uc.muc_units, uc.muc_import, uc.muc_export with
  | [Uscope (_,ul1)], _ :: sti, _ :: ste -> (* empty scope *)
      { uc with muc_theory = th;  muc_units  = ul1;
                muc_import = sti; muc_export = ste; }
  | Uscope (s,ul1) :: ul0, _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let i1 = add_ns false s e0 i1 in
      let e1 = add_ns true  s e0 e1 in
      { uc with
          muc_theory = th;
          muc_units  = Uscope (s,ul0) :: ul1;
          muc_import = i1 :: sti;
          muc_export = e1 :: ste; }
  | _ -> assert false

let import_scope uc ql = match uc.muc_import with
  | i1 :: sti ->
      let th = Theory.import_scope uc.muc_theory ql in
      let i1 = merge_ns false (ns_find_ns i1 ql) i1 in
      { uc with muc_theory = th; muc_import = i1::sti }
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

(*
let count_regions {muc_known = kn} {pv_ity = ity} mr =
  let add_reg r mr = Mreg.change (fun n -> Some (n <> None)) r mr in
  let meet mr1 mr2 = Mreg.union (fun _ x y -> Some (x || y)) mr1 mr2 in
  let join mr1 mr2 = Mreg.union (fun _ _ _ -> Some true) mr1 mr2 in
  let rec down mr ity = if ity.ity_imm then mr else
    match ity.ity_node with
    | Ityreg r -> fields (add_reg r mr) r.reg_its r.reg_args r.reg_regs
    | Ityapp (s,tl,rl) -> fields mr s tl rl
    | Ityvar _ -> assert false
  and fields mr s tl rl =
    if s.its_private && rl = [] then mr else
    let isb = its_match_regs s tl rl in
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
*)

let add_symbol add id v uc =
  store_path uc [] id;
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_import = add false id.id_string v i0 :: sti;
      muc_export = add true  id.id_string v e0 :: ste }
  | _ -> assert false

let add_pdecl_no_logic uc d =
  let uc = { uc with
    muc_units = Udecl d :: uc.muc_units;
    muc_known = known_add_decl uc.muc_known d;
    muc_local = Sid.union uc.muc_local d.pd_news } in
  let add_rs uc s = add_symbol add_ps s.rs_name (RS s) uc in
  let add_rd uc d = add_rs uc d.rec_sym in
  match d.pd_node with
  | PDtype tdl ->
      let add uc d =
        let uc = List.fold_left add_rs uc d.itd_fields in
        let uc = List.fold_left add_rs uc d.itd_constructors in
        add_symbol add_ts d.itd_its.its_ts.ts_name d.itd_its uc in
      List.fold_left add uc tdl
  | PDlet (LDvar (v,_)) -> add_symbol add_ps v.pv_vs.vs_name (PV v) uc
  | PDlet (LDsym (s,_)) -> add_rs uc s
  | PDlet (LDrec l) -> List.fold_left add_rd uc l
  | PDexn xs -> add_symbol add_xs xs.xs_name xs uc
  | PDpure -> uc

let add_pdecl_raw ?(warn=true) uc d =
  let uc = add_pdecl_no_logic uc d in
  let th = List.fold_left (add_decl ~warn) uc.muc_theory d.pd_pure in
  let add_meta th (m,l) = Theory.add_meta th m l in
  let th = List.fold_left add_meta th d.pd_meta in
  { uc with muc_theory = th }

(** {2 Builtin symbols} *)

let dummy_env = Env.create_env []

let builtin_module =
  let uc = empty_module dummy_env (id_fresh "BuiltIn") ["why3";"BuiltIn"] in
  let uc = add_pdecl_no_logic uc pd_int in
  let uc = add_pdecl_no_logic uc pd_real in
  let uc = add_pdecl_no_logic uc pd_equ in
  let m = close_module uc in
  { m with mod_theory = builtin_theory }

let bool_module =
  let uc = empty_module dummy_env (id_fresh "Bool") ["why3";"Bool"] in
  let uc = add_pdecl_no_logic uc pd_bool in
  let m = close_module uc in
  { m with mod_theory = bool_theory }

let highord_module =
  let uc = empty_module dummy_env (id_fresh "HighOrd") ["why3";"HighOrd"] in
  let uc = add_pdecl_no_logic uc pd_func in
  let uc = add_pdecl_no_logic uc pd_func_app in
  let m = close_module uc in
  { m with mod_theory = highord_theory }

let tuple_module = Hint.memo 17 (fun n ->
  let nm = "Tuple" ^ string_of_int n in
  let uc = empty_module dummy_env (id_fresh nm) ["why3";nm] in
  let uc = add_pdecl_no_logic uc (pd_tuple n) in
  let m = close_module uc in
  { m with mod_theory = tuple_theory n })

let unit_module =
  let uc = empty_module dummy_env (id_fresh "Unit") ["why3";"Unit"] in
  let uc = use_export uc (tuple_module 0) in
  let add uc d = add_pdecl_raw ~warn:false uc d in
  let td = create_alias_decl (id_fresh "unit") [] ity_unit in
  close_module (List.fold_left add uc (create_type_decl [td]))

let itd_ref =
  let tv = create_tvsymbol (id_fresh "a") in
  let pj = create_pvsymbol (id_fresh "contents") (ity_var tv) in
  create_plain_record_decl ~priv:false ~mut:true (id_fresh "ref")
                                            [tv] [true, pj] [] []

let its_ref = itd_ref.itd_its
let rs_ref_cons = List.hd itd_ref.itd_constructors
let rs_ref_proj = List.hd itd_ref.itd_fields

let ts_ref = its_ref.its_ts
let ls_ref_cons = ls_of_rs rs_ref_cons
let ls_ref_proj = ls_of_rs rs_ref_proj

let rs_ref_ld, rs_ref =
  let cty = rs_ref_cons.rs_cty in
  let ityl = List.map (fun v -> v.pv_ity) cty.cty_args in
  let_sym (id_fresh "ref") (c_app rs_ref_cons [] ityl cty.cty_result)

let ref_module =
  let add uc d = add_pdecl_raw ~warn:false uc d in
  let uc = empty_module dummy_env (id_fresh "Ref") ["why3";"Ref"] in
  let uc = List.fold_left add uc (create_type_decl [itd_ref]) in
  let uc = use_export uc builtin_module (* needed for "=" *) in
  close_module (add uc (create_let_decl rs_ref_ld))

let create_module env ?(path=[]) n =
  let m = empty_module env n path in
  let m = use_export m builtin_module in
  let m = use_export m bool_module in
  let m = use_export m unit_module in
  m

let add_use uc d = Sid.fold (fun id uc ->
  if id_equal id ts_func.ts_name then
    use_export uc highord_module
  else if id_equal id ts_ref.ts_name then
    use_export uc ref_module
  else match is_ts_tuple_id id with
  | Some n -> use_export uc (tuple_module n)
  | None -> uc) (Mid.set_diff d.pd_syms uc.muc_known) uc

let mk_vc uc d = Vc.vc uc.muc_env uc.muc_known uc.muc_theory d

let add_pdecl ?(warn=true) ~vc uc d =
  let uc = add_use uc d in
  let dl = if vc then mk_vc uc d else [] in
  (* verification conditions must not add additional dependencies
     on built-in theories like TupleN or HighOrd. Also, we expect
     int.Int or any other library theory to be in the context:
     importing them automatically seems to be too invasive. *)
  add_pdecl_raw ~warn (List.fold_left (add_pdecl_raw ~warn) uc dl) d

(** {2 Cloning} *)

type clones = {
  cl_local : Sid.t;
  mutable ty_table : ity Mts.t;
  mutable ts_table : itysymbol Mts.t;
  mutable ls_table : lsymbol Mls.t;
  mutable pr_table : prsymbol Mpr.t;
  mutable rn_table : region Mreg.t;
  mutable fd_table : pvsymbol Mpv.t;
  mutable pv_table : pvsymbol Mvs.t;
  mutable rs_table : rsymbol Mrs.t;
  mutable xs_table : xsymbol Mxs.t;
}

let empty_clones m = {
  cl_local = m.mod_local;
  ty_table = Mts.empty;
  ts_table = Mts.empty;
  ls_table = Mls.empty;
  pr_table = Mpr.empty;
  rn_table = Mreg.empty;
  fd_table = Mpv.empty;
  pv_table = Mvs.empty;
  rs_table = Mrs.empty;
  xs_table = Mxs.empty;
}

exception CloneDivergence of ident * ident

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

let clone_ty cl ty = sm_trans_ty cl.ty_table cl.ts_table ty

let cl_find_its cl its =
  if not (Sid.mem its.its_ts.ts_name cl.cl_local) then its
  else Mts.find its.its_ts cl.ts_table

let cl_find_ts cl ts =
  if not (Sid.mem ts.ts_name cl.cl_local) then ts
  else (Mts.find ts cl.ts_table).its_ts

let rec clone_ity cl ity = match ity.ity_node with
  | Ityreg r ->
      ity_reg (clone_reg cl r)
  | Ityapp (s, tl, rl) ->
      let tl = List.map (clone_ity cl) tl in
      let rl = List.map (clone_ity cl) rl in
      begin match Mts.find_opt s.its_ts cl.ts_table with
      | Some its -> ity_app_pure its tl rl
      | None -> (* creative indentation *)
      begin match Mts.find_opt s.its_ts cl.ty_table with
      | Some ity -> ity_full_inst (its_match_regs s tl rl) ity
      | None -> ity_app_pure s tl rl
      end end
  | Ityvar _ -> ity

and clone_reg cl reg =
  (* FIXME: what about top-level non-instantiated regions?
     We cannot check in cl.cl_local to see if they are there.
     Instead, we should prefill cl.pv_table and cl.rn_table
     with all top-level pvsymbols (local or external) before
     descending into a let_defn.
     TODO: add to module/uc a list of locally-defined toplevel
     variables, as well as a set of imported toplevel variables. *)
  try Mreg.find reg cl.rn_table with Not_found ->
  let tl = List.map (clone_ity cl) reg.reg_args in
  let rl = List.map (clone_ity cl) reg.reg_regs in
  let r = match Mts.find_opt reg.reg_its.its_ts cl.ts_table with
    | Some its ->
        create_region (id_clone reg.reg_name) its tl rl
    | None -> (* creative indentation *)
    begin match Mts.find_opt reg.reg_its.its_ts cl.ty_table with
    | Some {ity_node = Ityreg r} ->
        let sbs = its_match_regs reg.reg_its tl rl in
        let tl = List.map (ity_full_inst sbs) r.reg_args in
        let rl = List.map (ity_full_inst sbs) r.reg_regs in
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

let clone_term cl mv t = t_gen_map (clone_ty cl) (cl_find_ls cl) mv t

let clone_fmla cl f = clone_term cl Mvs.empty f (* for closed terms *)

let cl_find_pr cl pr =
  if not (Sid.mem pr.pr_name cl.cl_local) then pr
  else Mpr.find pr cl.pr_table

let cl_find_pv cl pv =
  if not (Sid.mem pv.pv_vs.vs_name cl.cl_local) then pv
  else Mvs.find pv.pv_vs cl.pv_table

let cl_find_rs cl rs =
  if not (Sid.mem rs.rs_name cl.cl_local) then rs
  else Mrs.find rs cl.rs_table

let cl_find_xs cl xs =
  if not (Sid.mem xs.xs_name cl.cl_local) then xs
  else Mxs.find xs cl.xs_table

let cl_init m inst =
  let cl = empty_clones m in
  let non_local id =
    if not (Sid.mem id cl.cl_local) then raise (NonLocal id) in
  Mts.iter (fun ts _ -> non_local ts.ts_name) inst.mi_ts;
  Mts.iter (fun ts _ -> non_local ts.ts_name) inst.mi_ty;
  let check_ls ls _ =
    non_local ls.ls_name;
    try  ignore (restore_rs ls); raise (BadInstance ls.ls_name)
    with Not_found -> () in
  Mls.iter check_ls inst.mi_ls;
  let check_rs rs _ =
    non_local rs.rs_name;
    match (Mid.find rs.rs_name m.mod_known).pd_node with
    | PDtype _ -> raise (BadInstance rs.rs_name)
    | PDlet  _ | PDexn  _ | PDpure -> () in
  Mrs.iter check_rs inst.mi_rs;
  Mvs.iter (fun vs _ -> non_local vs.vs_name) inst.mi_pv;
  Mxs.iter (fun xs _ -> non_local xs.xs_name) inst.mi_xs;
  let check_pk pr _ =
    non_local pr.pr_name;
    match (Mid.find pr.pr_name m.mod_known).pd_node with
    | PDtype _ | PDlet  _ | PDexn  _ -> raise (BadInstance pr.pr_name)
    | PDpure -> () in
  Mpr.iter check_pk inst.mi_pk;
  Mpr.iter (fun pr _ -> raise (BadInstance pr.pr_name)) inst.mi_pr;
  cl

(* clone declarations *)

let clone_ls cl ls =
  let constr = ls.ls_constr in
  let id = id_clone ls.ls_name in
  let at = List.map (clone_ty cl) ls.ls_args in
  let vt = Opt.map (clone_ty cl) ls.ls_value in
  let ls' = create_lsymbol ~constr id at vt in
  cl.ls_table <- Mls.add ls ls' cl.ls_table;
  ls'

let clone_decl inst cl uc d = match d.d_node with
  | Dtype _ | Ddata _ -> assert false (* impossible *)
  | Dparam ({ls_name = id} as ls) when Mls.mem ls inst.mi_ls ->
      let ls' = Mls.find ls inst.mi_ls in
      let mtch sb ty ty' = try ty_match sb ty' (clone_ty cl ty)
        with TypeMismatch _ -> raise (BadInstance id) in
      let sbs = match ls.ls_value,ls'.ls_value with
        | Some ty, Some ty' -> mtch Mtv.empty ty ty'
        | None, None -> Mtv.empty
        | _ -> raise (BadInstance id) in
      ignore (try List.fold_left2 mtch sbs ls.ls_args ls'.ls_args
        with Invalid_argument _ -> raise (BadInstance id));
      cl.ls_table <- Mls.add ls ls' cl.ls_table;
      uc
  | Dparam ls ->
      let d = create_param_decl (clone_ls cl ls) in
      add_pdecl ~warn:false ~vc:false uc (create_pure_decl d)
  | Dlogic ldl ->
      List.iter (fun (ls,_) ->
        if Mls.mem ls inst.mi_ls then raise (CannotInstantiate ls.ls_name);
        ignore (clone_ls cl ls)) ldl;
      let get_logic (_,ld) =
        Opt.get (ls_defn_of_axiom (clone_fmla cl (ls_defn_axiom ld))) in
      let d = create_logic_decl (List.map get_logic ldl) in
      add_pdecl ~warn:false ~vc:false uc (create_pure_decl d)
  | Dind (s, idl) ->
      let lls = List.map (fun (ls,_) ->
        if Mls.mem ls inst.mi_ls then raise (CannotInstantiate ls.ls_name);
        clone_ls cl ls) idl in
      let get_case (pr,f) =
        if Mpr.mem pr inst.mi_pk then raise (CannotInstantiate pr.pr_name);
        let pr' = create_prsymbol (id_clone pr.pr_name) in
        cl.pr_table <- Mpr.add pr pr' cl.pr_table;
        pr', clone_fmla cl f in
      let get_ind ls (_,la) = ls, List.map get_case la in
      let d = create_ind_decl s (List.map2 get_ind lls idl) in
      add_pdecl ~warn:false ~vc:false uc (create_pure_decl d)
  | Dprop (k,pr,f) ->
      let skip, k' = match k, Mpr.find_opt pr inst.mi_pk with
        | Pgoal, _ -> true, Pgoal
        | Plemma, Some Pgoal -> true, Pgoal
        | Plemma, _ -> false, Plemma
        | Paxiom, Some k -> false, k
        | Paxiom, None -> false, inst.mi_df in
      if skip then uc else
      let pr' = create_prsymbol (id_clone pr.pr_name) in
      cl.pr_table <- Mpr.add pr pr' cl.pr_table;
      let d = create_prop_decl k' pr' (clone_fmla cl f) in
      add_pdecl ~warn:false ~vc:false uc (create_pure_decl d)

let cl_save_ls cl s s' =
  cl.ls_table <- Mls.add_new (CannotInstantiate s.ls_name) s s' cl.ls_table

let cl_save_rs cl s s' =
  cl.rs_table <- Mrs.add s s' cl.rs_table;
  begin match s.rs_field, s'.rs_field with
  | Some v, Some v' -> cl.fd_table <- Mpv.add v v' cl.fd_table
  | None, _ -> () (* can instantiate a non-field with a field *)
  | _ -> assert false (* but not vice versa *)
  end;
  match s.rs_logic, s'.rs_logic with
  | RLls s, RLls s' -> cl_save_ls cl s s'
  | RLlemma, RLlemma -> () (* TODO: update cl.pr_table? *)
  | RLnone, RLnone -> ()
  | _ -> assert false

type smap = {
  sm_vs : vsymbol Mvs.t;
  sm_pv : pvsymbol Mvs.t;
  sm_xs : xsymbol Mxs.t;
  sm_rs : rsymbol Mrs.t;
}

let sm_of_cl cl = {
  sm_vs = Mvs.map (fun v -> v.pv_vs) cl.pv_table;
  sm_pv = cl.pv_table;
  sm_xs = cl.xs_table;
  sm_rs = cl.rs_table }

let sm_save_vs sm v v' = {
  sm_vs = Mvs.add v v'.pv_vs sm.sm_vs;
  sm_pv = Mvs.add v v' sm.sm_pv;
  sm_xs = sm.sm_xs;
  sm_rs = sm.sm_rs }

let sm_save_pv sm v v' = {
  sm_vs = Mvs.add v.pv_vs v'.pv_vs sm.sm_vs;
  sm_pv = Mvs.add v.pv_vs v' sm.sm_pv;
  sm_xs = sm.sm_xs;
  sm_rs = sm.sm_rs }

let sm_save_xs sm s s' =
  { sm with sm_xs = Mxs.add s s' sm.sm_xs }

let sm_save_rs cl sm s s' =
  let sm = { sm with sm_rs = Mrs.add s s' sm.sm_rs } in
  match s.rs_logic, s'.rs_logic with
  | RLls s, RLls s' -> cl_save_ls cl s s'; sm
  | RLpv v, RLpv v' -> sm_save_pv sm v v'
  | _ -> sm

let sm_find_pv sm v = Mvs.find_def v v.pv_vs sm.sm_pv
  (* non-instantiated global variables are not in sm *)

let sm_find_xs sm xs = Mxs.find_def xs xs sm.sm_xs

let sm_find_rs sm rs = Mrs.find_def rs rs sm.sm_rs

let clone_pv cl {pv_vs = vs; pv_ity = ity; pv_ghost = ghost} =
  create_pvsymbol (id_clone vs.vs_name) ~ghost (clone_ity cl ity)

let clone_invl cl sm invl =
  List.map (fun t -> clone_term cl sm.sm_vs t) invl

let clone_varl cl sm varl = List.map (fun (t,r) ->
  clone_term cl sm.sm_vs t, Opt.map (cl_find_ls cl) r) varl

let clone_cty cl sm ?(drop_decr=false) cty =
  let res = clone_ity cl cty.cty_result in
  let args = List.map (clone_pv cl) cty.cty_args in
  let sm_args = List.fold_left2 sm_save_pv sm cty.cty_args args in
  let add_old o n (sm, olds) = let o' = clone_pv cl o in
    sm_save_pv sm o o', Mpv.add o' (sm_find_pv sm_args n) olds in
  let sm_olds, olds = Mpv.fold add_old cty.cty_oldies (sm_args, Mpv.empty) in
  let pre = if drop_decr then List.tl cty.cty_pre else cty.cty_pre in
  let pre = clone_invl cl sm_args pre in
  let post = clone_invl cl sm_olds cty.cty_post in
  let xpost = Mxs.fold (fun xs fl q ->
    let xs = sm_find_xs sm xs in
    let fl = clone_invl cl sm_olds fl in
    Mxs.add xs fl q) cty.cty_xpost Mxs.empty in
  let add_read v s = Spv.add (sm_find_pv sm_args v) s in
  let reads = Spv.fold add_read (cty_reads cty) Spv.empty in
  let reads = List.fold_right add_read cty.cty_args reads in
  let reads = Spv.union reads (Mpv.domain olds) in
  let add_write reg fs m = (* add new mutable fields to functions effect *)
    let add_fd fd s = Spv.add (Mpv.find_def fd fd cl.fd_table) s in
    let reg' = clone_reg cl reg in
    let smf_reg' = Spv.of_list reg'.reg_its.its_mfields in
    let smf_reg = Spv.of_list reg.reg_its.its_mfields in
    let smf_ref = Spv.fold add_fd smf_reg Spv.empty in
    let smf_new = Spv.diff smf_reg' smf_ref in
    let fs = Spv.fold add_fd fs Spv.empty in
    Mreg.add reg' (Spv.union fs smf_new) m in
  let writes = Mreg.fold add_write cty.cty_effect.eff_writes Mreg.empty in
  let add_reset reg s = Sreg.add (clone_reg cl reg) s in
  let resets = Sreg.fold add_reset cty.cty_effect.eff_resets Sreg.empty in
  let eff = eff_reset (eff_write reads writes) resets in
  let add_raise xs eff = eff_raise eff (sm_find_xs sm xs) in
  let eff = Sxs.fold add_raise cty.cty_effect.eff_raises eff in
  let eff = if partial cty.cty_effect.eff_oneway then eff_partial eff else eff in
  let eff = if diverges cty.cty_effect.eff_oneway then eff_diverge eff else eff in
  let cty = create_cty ~mask:cty.cty_mask args pre post xpost olds eff res in
  cty_ghostify (cty_ghost cty) cty

let sm_save_args sm c c' =
  List.fold_left2 sm_save_pv sm c.cty_args c'.cty_args

let sm_save_olds sm c c' =
  let revs = Mpv.fold (fun o n m -> Mpv.add n o m) c'.cty_oldies Mpv.empty in
  let add_old o n sm = sm_save_pv sm o (Mpv.find (sm_find_pv sm n) revs) in
  Mpv.fold add_old c.cty_oldies sm

let clone_ppat cl sm pp mask =
  let rec conv_pat p = match p.pat_node with
    | Term.Pwild -> PPwild
    | Term.Pvar v -> PPvar (id_clone v.vs_name, (restore_pv v).pv_ghost)
    | Term.Pas (p,v) ->
        PPas (conv_pat p, id_clone v.vs_name, (restore_pv v).pv_ghost)
    | Term.Por (p1,p2) -> PPor (conv_pat p1, conv_pat p2)
    | Term.Papp (s,pl) ->
        PPapp (restore_rs (cl_find_ls cl s), List.map conv_pat pl) in
  let pre = conv_pat pp.pp_pat in
  let vm, pp' = create_prog_pattern pre (clone_ity cl pp.pp_ity) mask in
  let save v sm = sm_save_vs sm v (Mstr.find v.vs_name.id_string vm) in
  Svs.fold save pp.pp_pat.pat_vars sm, pp'

let rec clone_expr cl sm e = e_attr_copy e (match e.e_node with
  | Evar v -> e_var (sm_find_pv sm v)
  | Econst c -> e_const c (clone_ity cl e.e_ity)
  | Eexec (c,_) -> e_exec (clone_cexp cl sm c)
  | Eassign asl ->
      let conv (r,f,v) =
        e_var (sm_find_pv sm r), cl_find_rs cl f, e_var (sm_find_pv sm v) in
      e_assign (List.map conv asl)
  | Elet (ld, e) ->
      let sm, ld = clone_let_defn cl sm ld in
      e_let ld (clone_expr cl sm e)
  | Eif (e1, e2, e3) ->
      e_if (clone_expr cl sm e1) (clone_expr cl sm e2) (clone_expr cl sm e3)
  | Ematch (d, bl, xl) ->
      let d = clone_expr cl sm d in
      let conv_rbr (pp, e) =
        let sm, pp = clone_ppat cl sm pp d.e_mask in
        pp, clone_expr cl sm e in
      let conv_xbr xs (vl, e) m =
        let vl' = List.map (clone_pv cl) vl in
        let sm = List.fold_left2 sm_save_pv sm vl vl' in
        Mxs.add (sm_find_xs sm xs) (vl', clone_expr cl sm e) m in
      e_match d (List.map conv_rbr bl) (Mxs.fold conv_xbr xl Mxs.empty)
  | Ewhile (c,invl,varl,e) ->
      e_while (clone_expr cl sm c) (clone_invl cl sm invl)
              (clone_varl cl sm varl) (clone_expr cl sm e)
  | Efor (v, (f,dir,t), i, invl, e) ->
      let v' = clone_pv cl v in
      let ism = sm_save_pv sm v v' in
      let i' = if pv_equal v i then v' else clone_pv cl i in
      let ism = if pv_equal v i then ism else sm_save_pv ism i i' in
      e_for v'
        (e_var (sm_find_pv sm f)) dir (e_var (sm_find_pv sm t))
        i' (clone_invl cl ism invl) (clone_expr cl ism e)
  | Eraise (xs, e1) ->
      e_raise (sm_find_xs sm xs) (clone_expr cl sm e1) (clone_ity cl e.e_ity)
  | Eexn ({xs_name = id; xs_mask = mask; xs_ity = ity} as xs, e) ->
      let xs' = create_xsymbol (id_clone id) ~mask (clone_ity cl ity) in
      e_exn xs' (clone_expr cl (sm_save_xs sm xs xs') e)
  | Eassert (k, f) ->
      e_assert k (clone_term cl sm.sm_vs f)
  | Eghost e ->
      e_ghostify true (clone_expr cl sm e)
  | Epure t ->
      e_pure (clone_term cl sm.sm_vs t)
  | Eabsurd -> e_absurd (clone_ity cl e.e_ity))

and clone_cexp cl sm c = match c.c_node with
  | Capp (s,vl) ->
      let vl = List.map (fun v -> sm_find_pv sm v) vl in
      let al = List.map (fun v -> clone_ity cl v.pv_ity) c.c_cty.cty_args in
      let res = clone_ity cl c.c_cty.cty_result in
      c_app (sm_find_rs sm s) vl al res
  | Cpur (s,vl) ->
      let vl = List.map (fun v -> sm_find_pv sm v) vl in
      let al = List.map (fun v -> clone_ity cl v.pv_ity) c.c_cty.cty_args in
      let res = clone_ity cl c.c_cty.cty_result in
      c_pur (cl_find_ls cl s) vl al res
  | Cfun e ->
      let cty = clone_cty cl sm c.c_cty in
      let sm = sm_save_args sm c.c_cty cty in
      let sm = sm_save_olds sm c.c_cty cty in
      c_fun ~mask:cty.cty_mask cty.cty_args cty.cty_pre
        cty.cty_post cty.cty_xpost cty.cty_oldies (clone_expr cl sm e)
  | Cany ->
      c_any (clone_cty cl sm c.c_cty)

and clone_let_defn cl sm ld = match ld with
  | LDvar (v,e) ->
      let e' = clone_expr cl sm e in
      let id = id_clone v.pv_vs.vs_name in
      let ld, v' = let_var id ~ghost:v.pv_ghost e' in
      sm_save_pv sm v v', ld
  | LDsym (s,c) ->
      let c' = clone_cexp cl sm c in
      let ld, s' = let_sym (id_clone s.rs_name)
        ~ghost:(rs_ghost s) ~kind:(rs_kind s) c' in
      sm_save_rs cl sm s s', ld
  | LDrec rdl ->
      let conv_rs mrs {rec_rsym = {rs_name = id} as rs} =
        let cty = clone_cty cl sm ~drop_decr:true rs.rs_cty in
        let rs' = create_rsymbol (id_clone id) ~ghost:(rs_ghost rs) cty in
        Mrs.add rs rs' mrs, rs' in
      let mrs, rsyml = Lists.map_fold_left conv_rs sm.sm_rs rdl in
      let rsm = { sm with sm_rs = mrs } in
      let conv_rd ({rec_fun = c} as rd) ({rs_cty = cty} as rs) =
        let rsm = sm_save_args rsm c.c_cty cty in
        let varl = clone_varl cl rsm rd.rec_varl in
        let rsm = sm_save_olds rsm c.c_cty cty in
        let e = match c.c_node with
          | Cfun e -> clone_expr cl rsm e
          | _ -> assert false (* can't be *) in
        let c = c_fun ~mask:c.c_cty.cty_mask cty.cty_args
          cty.cty_pre cty.cty_post cty.cty_xpost cty.cty_oldies e in
        rs, c, varl, rs_kind rd.rec_sym in
      let ld, rdl' = let_rec (List.map2 conv_rd rdl rsyml) in
      let sm = List.fold_left2 (fun sm d d' ->
        sm_save_rs cl sm d.rec_sym d'.rec_sym) sm rdl rdl' in
      sm, ld

let clone_type_record cl s d s' d' =
  let id = s.its_ts.ts_name in
  let fields' = Hstr.create 16 in
  let add_field' rs' = let pj' = fd_of_rs rs' in
    Hstr.add fields' pj'.pv_vs.vs_name.id_string rs' in
  List.iter add_field' d'.itd_fields;
  (* check if fields from former type are also declared in the new type *)
  let match_pj rs = let pj = fd_of_rs rs in
    let pj_str = pj.pv_vs.vs_name.id_string in
    let pj_ity = clone_ity cl pj.pv_ity in
    let pj_ght = pj.pv_ghost in
    let rs' = try Hstr.find fields' pj_str with Not_found ->
      raise (BadInstance id) in
    let pj' = fd_of_rs rs' in
    let pj'_ity = pj'.pv_ity in
    let pj'_ght = pj'.pv_ghost in
    if not (ity_equal pj_ity pj'_ity && (pj_ght || not pj'_ght)) then
      raise (BadInstance id);
    let ls, ls' = ls_of_rs rs, ls_of_rs rs' in
    cl.ls_table <- Mls.add ls ls' cl.ls_table;
    cl.rs_table <- Mrs.add rs rs' cl.rs_table;
    cl.fd_table <- Mpv.add pj pj' cl.fd_table in
  List.iter match_pj d.itd_fields;
  cl.ts_table <- Mts.add s.its_ts s' cl.ts_table

let clone_type_decl inst cl tdl kn =
  let def =
    List.fold_left (fun m d -> Mits.add d.itd_its d m) Mits.empty tdl in
  let htd = Hits.create 5 in
  let vcs = ref ([] : (itysymbol * term) list) in
  let rec visit alg ({its_ts = {ts_name = id} as ts} as s) d =
    if not (Hits.mem htd s) then
    let alg = Sits.add s alg in
    let id' = id_clone id in
    let cloned = Mts.mem ts inst.mi_ts || Mts.mem ts inst.mi_ty in
    let conv_pj v = create_pvsymbol
      (id_clone v.pv_vs.vs_name) ~ghost:v.pv_ghost (conv_ity alg v.pv_ity) in
    let save_itd itd =
      List.iter2 (cl_save_rs cl) d.itd_constructors itd.itd_constructors;
      List.iter2 (cl_save_rs cl) d.itd_fields itd.itd_fields;
      Hits.add htd s (Some itd) in
    (* alias *)
    if s.its_def <> NoDef then begin
      if cloned then raise (CannotInstantiate id);
      let itd = match s.its_def with
        | Alias ty -> create_alias_decl id' ts.ts_args (conv_ity alg ty)
        | Range ir -> create_range_decl id' ir
        | Float ff -> create_float_decl id' ff
        | NoDef -> assert false (* never *) in
      cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
      save_itd itd
    end else
    (* abstract *)
    if s.its_private && cloned then begin
      begin match Mts.find_opt ts inst.mi_ts with
      | Some s' ->
          if not (List.length ts.ts_args = List.length s'.its_ts.ts_args) then
            raise (BadInstance id);
          let pd' = Mid.find s'.its_ts.ts_name kn in
          let d' = match pd'.pd_node with
            | PDtype [d'] -> d'
            (* FIXME: we could refine with mutual types *)
            | PDtype _ -> raise (BadInstance id)
            | PDlet _ | PDexn _ | PDpure -> raise (BadInstance id) in
          clone_type_record cl s d s' d'; (* clone record fields *)
          (* generate and add VC for type invariant implication *)
          if d.itd_invariant <> [] then begin
            let inv = axiom_of_invariant d in
            let invl = clone_invl cl (sm_of_cl cl) [inv] in
            let add_vc inv = vcs := (d.itd_its, inv) :: !vcs in
            List.iter add_vc invl end
      | None -> begin match Mts.find_opt ts inst.mi_ty with
      | Some ity -> (* creative indentation *)
          (* TODO: clone_type_record, axiom_of_invariant *)
          (* TODO: should we only allow cloning into ity for
             private types with no fields and no invariant? *)
          let stv = Stv.of_list ts.ts_args in
          if not (Stv.subset (ity_freevars Stv.empty ity) stv &&
                  its_pure s && ity.ity_pure) then raise (BadInstance id);
          cl.ty_table <- Mts.add ts ity cl.ty_table
      | None -> assert false end end;
      Hits.add htd s None;
      (* TODO: check typing conditions for refined record type *)
    end else
    (* variant *)
    if not s.its_mutable && d.itd_constructors <> [] &&
                            d.itd_invariant = [] then begin
      if cloned then raise (CannotInstantiate id);
      let conv_fd m fd =
        let v = fd_of_rs fd in Mpv.add v (conv_pj v) m in
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
          let itd = create_plain_variant_decl id' ts.ts_args csl in
          cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
          save_itd itd
    end else begin
    (* flat record *)
      if cloned then raise (CannotInstantiate id);
      let mfld = Spv.of_list s.its_mfields in
      let pjl = List.map fd_of_rs d.itd_fields in
      let fdl = List.map (fun v -> Spv.mem v mfld, conv_pj v) pjl in
      let inv =
        if d.itd_invariant = [] then [] else
        let add mv u (_,v) = Mvs.add u.pv_vs v.pv_vs mv in
        let mv = List.fold_left2 add Mvs.empty pjl fdl in
        List.map (clone_term cl mv) d.itd_invariant in
      let clone_wit = clone_expr cl (sm_of_cl cl) in
      let wit = List.map clone_wit d.itd_witness in
      let itd = create_plain_record_decl id' ts.ts_args
        ~priv:s.its_private ~mut:s.its_mutable fdl inv wit in
      cl.ts_table <- Mts.add ts itd.itd_its cl.ts_table;
      save_itd itd
    end

  and conv_ity alg ity =
    let rec down ity = match ity.ity_node with
      | Ityreg {reg_its = s; reg_args = tl}
      | Ityapp (s,tl,_) ->
          if Sits.mem s alg then begin
            if not (Mts.mem s.its_ts cl.ts_table) then
            let id = id_clone s.its_ts.ts_name in
            let s' = create_rec_itysymbol id s.its_ts.ts_args in
            cl.ts_table <- Mts.add s.its_ts s' cl.ts_table
          end else Opt.iter (visit alg s) (Mits.find_opt s def);
          List.iter down tl
      | Ityvar _ -> () in
    down ity;
    clone_ity cl ity in

  Mits.iter (visit Sits.empty) def;
  Lists.map_filter (fun d -> Hits.find htd d.itd_its) tdl,
  !vcs

let add_vc uc (its, f) =
  let {id_string = nm; id_loc = loc} = its.its_ts.ts_name in
  let attrs = Sattr.singleton (Ident.create_attribute ("expl:VC for " ^ nm)) in
  let pr = create_prsymbol (id_fresh ~attrs ?loc ("VC " ^ nm)) in
  let d = create_pure_decl (create_prop_decl Pgoal pr f) in
  add_pdecl ~warn:false ~vc:false uc d

let freeze_foreign cl reads =
  let frz = Spv.fold (fun v isb ->
    if Sid.mem v.pv_vs.vs_name cl.cl_local then isb
    else ity_freeze isb v.pv_ity) reads isb_empty in
  let frz = Mreg.map (fun ity -> match ity.ity_node with
    | Ityreg r -> r | _ -> assert false) frz.isb_reg in
  cl.rn_table <- Mreg.set_union cl.rn_table frz

let clone_pdecl inst cl uc d = match d.pd_node with
  | PDtype tdl ->
      let add_e spv e = Spv.union spv e.e_effect.eff_reads in
      let add_d spv d = List.fold_left add_e spv d.itd_witness in
      freeze_foreign cl (List.fold_left add_d Spv.empty tdl);
      let ndl, vcl = clone_type_decl inst cl tdl uc.muc_known in
      let uc = List.fold_left add_vc uc vcl in
      let dl = if ndl <> [] then create_type_decl ndl else [] in
      let save_special_ls d d' = match d.d_node, d'.d_node with
        | Dparam ls, Dparam ls' | Dlogic [ls,_], Dlogic [ls',_] ->
            cl.ls_table <- Mls.add ls ls' cl.ls_table;
        | Dtype _, Dtype _ -> ()
        | _ -> assert false in
      begin match tdl, dl with
      | [{itd_its = {its_def = (Range _|Float _)}}], [d'] ->
          List.iter2 save_special_ls d.pd_pure d'.pd_pure
      | _ -> () end;
      let add uc d = add_pdecl ~warn:false ~vc:false uc d in
      List.fold_left add uc dl
  | PDlet (LDsym (rs, c)) when Mrs.mem rs inst.mi_rs ->
      (* refine only [val] symbols *)
      let cty = match c.c_node with (* cty for [val constant] is not c.c_cty *)
        | Cany -> c.c_cty
        | Cfun {e_node = Eexec ({c_node = Cany}, cty)} -> cty
        | _ -> raise (BadInstance rs.rs_name) in
      let kind = match rs.rs_logic with
        | RLnone -> RKnone
        | RLpv _ -> raise (BadInstance rs.rs_name)
        | RLls ls when ls.ls_value = None -> RKpred
        | RLls _ -> RKfunc
        | RLlemma -> RKlemma in
      let cty = clone_cty cl (sm_of_cl cl) cty in
      let rs' = Mrs.find rs inst.mi_rs in
      (* arity and types will be checked when refinement VC is generated *)
      begin match rs.rs_logic, rs'.rs_logic with
      | RLnone, (RLnone | RLls _ | RLlemma) | RLlemma, RLlemma -> ()
      | RLls ls, RLls ls' -> cl.ls_table <- Mls.add ls ls' cl.ls_table
      | _ -> raise (BadInstance rs.rs_name)
      end;
      begin
        match cty.cty_effect.eff_oneway, rs'.rs_cty.cty_effect.eff_oneway with
        | _, Total | Diverges, _ | Partial, Partial -> ()
        | _ -> raise (CloneDivergence (rs.rs_name, rs'.rs_name))
      end;
      cl.rs_table <- Mrs.add rs rs' cl.rs_table;
      let e = e_exec (c_app rs' cty.cty_args [] cty.cty_result) in
      let cexp = c_fun ~mask:cty.cty_mask cty.cty_args cty.cty_pre
        cty.cty_post cty.cty_xpost cty.cty_oldies e in
      let id = id_clone rs.rs_name in (* FIXME better name *)
      let ld, _ = let_sym id ~ghost:(rs_ghost rs) ~kind cexp in
      (* FIXME check ghost status and mask of cexp/ld wrt rs *)
      (* FIXME check effects of cexp/ld wrt rs *)
      (* FIXME add correspondance for "let lemma" to cl.pr_table *)
      let dl = mk_vc uc (create_let_decl ld) in
      List.fold_left (add_pdecl_raw ~warn:false) uc dl
  | PDlet ld ->
      begin match ld with
        | LDvar ({pv_vs=vs}, _) when Mvs.mem vs inst.mi_pv ->
            raise (BadInstance vs.vs_name)
        | LDrec rdl ->
            let no_inst { rec_sym = rs } =
              if Mrs.mem rs inst.mi_rs then raise (BadInstance rs.rs_name) in
            List.iter no_inst rdl
        | _ -> () end;
      let reads = match ld with
        | LDvar (_,e) -> e.e_effect.eff_reads
        | LDsym (_,c) -> cty_reads c.c_cty
        | LDrec rdl -> List.fold_left (fun spv {rec_rsym = s} ->
            Spv.union spv (cty_reads s.rs_cty)) Spv.empty rdl in
      freeze_foreign cl reads;
      let sm, ld = clone_let_defn cl (sm_of_cl cl) ld in
      cl.pv_table <- sm.sm_pv; cl.rs_table <- sm.sm_rs;
      add_pdecl ~warn:false ~vc:false uc (create_let_decl ld)
  | PDexn ({xs_name = id} as xs) when Mxs.mem xs inst.mi_xs ->
      let xs' = Mxs.find xs inst.mi_xs in
      begin try let ity = clone_ity cl xs.xs_ity in
                ignore (ity_match isb_empty xs'.xs_ity ity)
        with TypeMismatch _ -> raise (BadInstance id) end;
      if mask_spill xs'.xs_mask xs.xs_mask then raise (BadInstance id);
      cl.xs_table <- Mxs.add xs xs' cl.xs_table;
      uc
  | PDexn xs ->
      let id = id_clone xs.xs_name in
      let ity = clone_ity cl xs.xs_ity in
      let xs' = create_xsymbol id ~mask:xs.xs_mask ity in
      cl.xs_table <- Mxs.add xs xs' cl.xs_table;
      add_pdecl ~warn:false ~vc:false uc (create_exn_decl xs')
  | PDpure ->
      let uc = List.fold_left (clone_decl inst cl) uc d.pd_pure in
      assert (d.pd_meta = []); (* pure decls do not produce metas *)
      uc

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
          mi_ty = Mts.map (clone_ity cl) mi.mi_ty;
          mi_ts = Mts.map (cl_find_its cl) mi.mi_ts;
          mi_ls = Mls.map (cl_find_ls cl) mi.mi_ls;
          mi_pr = Mpr.map (cl_find_pr cl) mi.mi_pr;
          mi_pk = mi.mi_pk;
          mi_pv = Mvs.map (cl_find_pv cl) mi.mi_pv;
          mi_rs = Mrs.map (cl_find_rs cl) mi.mi_rs;
          mi_xs = Mxs.map (cl_find_xs cl) mi.mi_xs;
          mi_df = mi.mi_df}
        with Not_found -> uc end
    | Umeta (m,al) ->
        begin try add_meta uc m (List.map (function
          | MAty ty -> MAty (clone_ty cl ty)
          | MAts ts -> MAts (cl_find_ts cl ts)
          | MAls ls -> MAls (cl_find_ls cl ls)
          | MApr pr -> MApr (cl_find_pr cl pr)
          | a -> a) al)
        with Not_found -> uc end
    | Uscope (n,ul) ->
        let uc = open_scope uc n in
        let uc = List.fold_left add_unit uc ul in
        close_scope ~import:false uc in
  let uc = List.fold_left add_unit uc m.mod_units in
  let mi = {
    mi_mod = m;
    mi_ty  = cl.ty_table;
    mi_ts  = cl.ts_table;
    mi_ls  = cl.ls_table;
    mi_pr  = cl.pr_table;
    mi_pk  = inst.mi_pk;
    mi_pv  = cl.pv_table;
    mi_rs  = cl.rs_table;
    mi_xs  = cl.xs_table;
    mi_df  = inst.mi_df} in
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
    if s = ref_module.mod_theory.th_name.id_string then ref_module else
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
  | Uscope (s,[Uuse m]) -> Format.fprintf fmt "use %a%s" print_mname m
      (if s = m.mod_theory.th_name.id_string then "" else " as " ^ s)
  | Uscope (s,[Uclone mi]) -> Format.fprintf fmt "clone %a%s with ..."
      print_mname mi.mi_mod
      (if s = mi.mi_mod.mod_theory.th_name.id_string then "" else " as " ^ s)
  | Uscope (s,ul) -> Format.fprintf fmt "@[<hov 2>scope %s@\n%a@]@\nend"
      s (Pp.print_list Pp.newline2 print_unit) ul

let print_module fmt m = Format.fprintf fmt
  "@[<hov 2>module %s@\n%a@]@\nend" m.mod_theory.th_name.id_string
  (Pp.print_list Pp.newline2 print_unit) m.mod_units

let print_id fmt id = Ident.print_decoded fmt id.id_string

let () = Exn_printer.register (fun fmt e -> match e with
  | IncompatibleNotation nm -> Format.fprintf fmt
      "Incombatible type signatures for notation '%a'" Ident.print_decoded nm
  | ModuleNotFound (sl,s) -> Format.fprintf fmt
      "Module %s not found in library %a" s print_path sl
  | CloneDivergence (iv, il) -> Format.fprintf fmt
      "Cannot instantiate symbol %a with symbol %a \
       that has worse termination status"
      print_id iv print_id il
  | _ -> raise e)
