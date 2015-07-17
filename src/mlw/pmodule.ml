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
  mod_theory : theory;      (* pure theory *)
  mod_decls  : pdecl list;  (* module declarations *)
  mod_export : namespace;   (* exported namespace *)
  mod_known  : known_map;   (* known identifiers *)
  mod_local  : Sid.t;       (* locally declared idents *)
  mod_used   : Sid.t;       (* used modules *)
}

(** {2 Module under construction} *)

type pmodule_uc = {
  muc_theory : theory_uc;
  muc_name   : string;
  muc_path   : string list;
  muc_decls  : pdecl list;
  muc_prefix : string list;
  muc_import : namespace list;
  muc_export : namespace list;
  muc_known  : known_map;
  muc_local  : Sid.t;
  muc_used   : Sid.t;
  muc_env    : Env.env option;
}

(* FIXME? We wouldn't need to store muc_name, muc_path,
   and muc_prefix if theory_uc was exported *)

let empty_module env n p = {
  muc_theory = create_theory ~path:p n;
  muc_name   = n.Ident.pre_name;
  muc_path   = p;
  muc_decls  = [];
  muc_prefix = [];
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
               mod_decls  = List.rev uc.muc_decls;
               mod_export = List.hd uc.muc_export;
               mod_known  = uc.muc_known;
               mod_local  = uc.muc_local;
               mod_used   = uc.muc_used; } in
     Hid.add h th.th_name m;
     m),
  (fun th -> Hid.find h th.th_name)

let open_namespace uc s = match uc.muc_import with
  | ns :: _ -> { uc with
      muc_theory = Theory.open_namespace uc.muc_theory s;
      muc_prefix =        s :: uc.muc_prefix;
      muc_import =       ns :: uc.muc_import;
      muc_export = empty_ns :: uc.muc_export; }
  | [] -> assert false

let close_namespace uc ~import =
  let th = Theory.close_namespace uc.muc_theory import in (* catches errors *)
  match uc.muc_prefix, uc.muc_import, uc.muc_export with
  | s :: prf, _ :: i1 :: sti, e0 :: e1 :: ste ->
      let i1 = if import then merge_ns false e0 i1 else i1 in
      let _  = if import then merge_ns true  e0 e1 else e1 in
      let i1 = add_ns false s e0 i1 in
      let e1 = add_ns true  s e0 e1 in
      { uc with
          muc_theory = th;
          muc_prefix = prf;
          muc_import = i1 :: sti;
          muc_export = e1 :: ste; }
  | _ ->
      assert false

let add_to_module uc th ns =
  match uc.muc_import, uc.muc_export with
  | i0 :: sti, e0 :: ste -> { uc with
      muc_theory = th;
      muc_import = merge_ns false ns i0 :: sti;
      muc_export = merge_ns true  ns e0 :: ste; }
  | _ -> assert false

let use_export uc m =
  let mth = m.mod_theory in
  let id = mth.th_name in
  let uc =
    if Sid.mem id uc.muc_used then uc else { uc with
      muc_known = merge_known uc.muc_known m.mod_known;
      muc_used  = Sid.add id uc.muc_used } in
  let th = Theory.use_export uc.muc_theory mth in
  add_to_module uc th m.mod_export

let add_meta uc m al =
  { uc with muc_theory = Theory.add_meta uc.muc_theory m al }

let store_path, store_module, restore_path =
  let id_to_path = Wid.create 17 in
  let store_path uc path id =
    (* this symbol already belongs to some theory *)
    if Wid.mem id_to_path id then () else
    let prefix = List.rev (id.id_string :: path @ uc.muc_prefix) in
    Wid.set id_to_path id (uc.muc_path, uc.muc_name, prefix)
  in
  let store_module m =
    let id = m.mod_theory.th_name in
    (* this symbol is already a module *)
    if Wid.mem id_to_path id then () else
    Wid.set id_to_path id (m.mod_theory.th_path, id.id_string, []) in
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
    | Ityvar _ -> mr
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
    muc_decls = d :: uc.muc_decls;
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
  let th = List.fold_left Theory.add_decl uc.muc_theory d.pd_pure in
  { uc with muc_theory = th }

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

open Theory

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

let print_path fmt sl =
  Pp.print_list (Pp.constant_string ".") Format.pp_print_string fmt sl

let () = Exn_printer.register (fun fmt e -> match e with
  | ModuleNotFound (sl,s) -> Format.fprintf fmt
      "Module %s not found in library %a" s print_path sl
  | _ -> raise e)
