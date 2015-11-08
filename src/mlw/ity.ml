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

(** {2 Individual types (first-order types without effects)} *)

type itysymbol = {
  its_ts      : tysymbol;       (** logical type symbol *)
  its_privmut : bool;           (** private mutable type *)
  its_mfields : pvsymbol list;  (** mutable record fields *)
  its_regions : region list;    (** shareable components *)
  its_arg_imm : bool list;      (** non-updatable parameters *)
  its_arg_exp : bool list;      (** exposed type parameters *)
  its_arg_vis : bool list;      (** non-ghost type parameters *)
  its_arg_frz : bool list;      (** irreplaceable type parameters *)
  its_reg_exp : bool list;      (** exposed shareable components *)
  its_reg_vis : bool list;      (** non-ghost shareable components *)
  its_reg_frz : bool list;      (** irreplaceable shareable components *)
  its_def     : ity option;     (** type alias *)
}

and ity = {
  ity_node : ity_node;
  ity_imm  : bool;
  ity_tag  : Weakhtbl.tag;
}

and ity_node =
  | Ityreg of region
    (** record with mutable fields and shareable components *)
  | Ityapp of itysymbol * ity list * ity list
    (** immutable type with shareable components *)
  | Ityvar of tvsymbol * bool
    (** type variable and its purity status *)

and region = {
  reg_name : ident;
  reg_its  : itysymbol;
  reg_args : ity list;
  reg_regs : ity list;
}

and pvsymbol = {
  pv_vs    : vsymbol;
  pv_ity   : ity;
  pv_ghost : bool;
}

module Itsym = MakeMSHW (struct
  type t = itysymbol
  let tag its = its.its_ts.ts_name.id_tag
end)

module Ity = MakeMSHW (struct
  type t = ity
  let tag ity = ity.ity_tag
end)

module Reg = MakeMSHW (struct
  type t = region
  let tag reg = reg.reg_name.id_tag
end)

module PVsym = MakeMSHW (struct
  type t = pvsymbol
  let tag pv = pv.pv_vs.vs_name.id_tag
end)

module Sits = Itsym.S
module Mits = Itsym.M
module Hits = Itsym.H
module Wits = Itsym.W

module Sity = Ity.S
module Mity = Ity.M
module Hity = Ity.H
module Wity = Ity.W

module Sreg = Reg.S
module Mreg = Reg.M
module Hreg = Reg.H
module Wreg = Reg.W

module Spv = PVsym.S
module Mpv = PVsym.M
module Hpv = PVsym.H
module Wpv = PVsym.W

(* value type symbols *)

let its_equal : itysymbol -> itysymbol -> bool = (==)
let ity_equal : ity       -> ity       -> bool = (==)
let reg_equal : region    -> region    -> bool = (==)
let pv_equal  : pvsymbol  -> pvsymbol  -> bool = (==)

let its_hash its = id_hash its.its_ts.ts_name
let ity_hash ity = Weakhtbl.tag_hash ity.ity_tag
let reg_hash reg = id_hash reg.reg_name
let pv_hash  pv  = id_hash pv.pv_vs.vs_name

let its_compare its1 its2 = id_compare its1.its_ts.ts_name its2.its_ts.ts_name
let ity_compare ity1 ity2 = Pervasives.compare (ity_hash ity1) (ity_hash ity2)
let reg_compare reg1 reg2 = id_compare reg1.reg_name reg2.reg_name
let pv_compare  pv1  pv2  = id_compare pv1.pv_vs.vs_name pv2.pv_vs.vs_name

exception NonUpdatable of itysymbol * ity

let check_its_args s tl =
  assert (s.its_def = None);
  let check imm ity =
    if imm && not ity.ity_imm then raise (NonUpdatable (s,ity)) in
  List.iter2 check s.its_arg_imm tl

module Hsity = Hashcons.Make (struct
  type t = ity

  let equal ity1 ity2 = match ity1.ity_node, ity2.ity_node with
    | Ityvar (v1,p1), Ityvar (v2,p2) -> tv_equal v1 v2 && p1 = p2
    | Ityreg r1, Ityreg r2 -> reg_equal r1 r2
    | Ityapp (s1,l1,r1), Ityapp (s2,l2,r2) ->
        its_equal s1 s2 &&
        List.for_all2 ity_equal l1 l2 &&
        List.for_all2 ity_equal r1 r2
    | _ -> false

  let hash ity = match ity.ity_node with
    | Ityvar (v,p) ->
        Hashcons.combine (tv_hash v) (Hashtbl.hash p)
    | Ityreg r -> reg_hash r
    | Ityapp (s,tl,rl) ->
        Hashcons.combine_list ity_hash
          (Hashcons.combine_list ity_hash (its_hash s) tl) rl

  let immutable ity = match ity.ity_node with
    | Ityvar _ -> true
    | Ityreg _ -> false
    | Ityapp (s,tl,rl) ->
        check_its_args s tl;
        let imm ity = ity.ity_imm in
        List.for_all imm tl && List.for_all imm rl

  let tag n ity = { ity with
    ity_imm = immutable ity;
    ity_tag = Weakhtbl.create_tag n }
end)

let mk_ity node = {
  ity_node = node;
  ity_imm  = true;
  ity_tag  = Weakhtbl.dummy_tag;
}

let mk_reg name s tl rl = {
  reg_name = id_register name;
  reg_its  = s;
  reg_args = (check_its_args s tl; tl);
  reg_regs = rl;
}

let ity_reg r              = Hsity.hashcons (mk_ity (Ityreg r))
let ity_var v              = Hsity.hashcons (mk_ity (Ityvar (v,false)))
let ity_var_pure v         = Hsity.hashcons (mk_ity (Ityvar (v,true)))
let ity_app_unsafe s tl rl = Hsity.hashcons (mk_ity (Ityapp (s,tl,rl)))

(* immutability and purity *)

let its_immutable s = not s.its_privmut && s.its_mfields = [] &&
  match s.its_def with Some {ity_node = Ityreg _} -> false | _ -> true

let its_pure s = its_immutable s && s.its_regions = [] &&
  match s.its_def with Some ity -> ity.ity_imm | None -> true

let ity_immutable ity = ity.ity_imm

let rec ity_pure ity = match ity.ity_node with
  | Ityreg _ -> false
  | Ityapp (_,tl,rl) -> List.for_all ity_pure tl && List.for_all ity_pure rl
  | Ityvar (_,p) -> p

let ity_pure ity = ity_immutable ity && ity_pure ity

let rec ity_purify ity = match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl} | Ityapp (s,tl,rl) ->
      ity_app_unsafe s (List.map ity_purify tl) (List.map ity_purify rl)
  | Ityvar (v,_) -> ity_var_pure v

let rec ty_of_ity ity = match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl} | Ityapp (s,tl,_) ->
      ty_app s.its_ts (List.map ty_of_ity tl)
  | Ityvar (v,_) -> ty_var v

(* generic traversal functions *)

let dfold fn acc l1 l2 =
  List.fold_left fn (List.fold_left fn acc l1) l2

let dfold2 fn acc l1 r1 l2 r2 =
  List.fold_left2 fn (List.fold_left2 fn acc l1 r1) l2 r2

let ity_fold fn acc ity = match ity.ity_node with
  | Ityreg {reg_args = tl; reg_regs = rl}
  | Ityapp (_,tl,rl) -> dfold fn acc tl rl
  | Ityvar _ -> acc

let reg_fold fn acc reg = dfold fn acc reg.reg_args reg.reg_regs

(* symbol-wise fold *)

let rec ity_s_fold fn acc ity = match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl}
  | Ityapp (s,tl,rl) -> dfold (ity_s_fold fn) (fn acc s) tl rl
  | Ityvar _ -> acc

let reg_s_fold fn acc r = reg_fold (ity_s_fold fn) (fn acc r.reg_its) r

(* traversal functions on type variables *)

let rec ity_v_fold fn acc ity = match ity.ity_node with
  | Ityreg {reg_args = tl} | Ityapp (_,tl,_) ->
      List.fold_left (ity_v_fold fn) acc tl
  | Ityvar (v,_) -> fn acc v

let reg_v_fold fn acc r = List.fold_left (ity_v_fold fn) acc r.reg_args

let ity_freevars s ity = ity_v_fold Stv.add_left s ity
let reg_freevars s reg = reg_v_fold Stv.add_left s reg

let ity_v_occurs v ity = Util.any ity_v_fold (tv_equal v) ity
let reg_v_occurs v reg = Util.any reg_v_fold (tv_equal v) reg

let ity_closed ity = Util.all ity_v_fold Util.ffalse ity

(* traversal functions on top regions *)

let rec ity_r_fold fn acc ity =
  if ity.ity_imm then acc else
  match ity.ity_node with
  | Ityapp (_,tl,rl) -> dfold (ity_r_fold fn) acc tl rl
  | Ityreg r -> fn acc r
  | Ityvar _ -> acc

let reg_r_fold fn acc reg = reg_fold (ity_r_fold fn) acc reg

let ity_top_regs regs ity = ity_r_fold Sreg.add_left regs ity

let rec reg_freeregs s reg = reg_r_fold reg_freeregs (Sreg.add reg s) reg
let     ity_freeregs s ity = ity_r_fold reg_freeregs s ity

let rec reg_r_occurs r reg = reg_equal r reg ||
                             Util.any reg_r_fold (reg_r_occurs r) reg
let     ity_r_occurs r ity = Util.any ity_r_fold (reg_r_occurs r) ity

(* traversal functions on exposed regions *)

let rec ity_exp_fold fn acc ity =
  if ity.ity_imm then acc else
  match ity.ity_node with
  | Ityapp (s,tl,rl) -> its_exp_fold fn acc s tl rl
  | Ityreg r -> fn acc r
  | Ityvar _ -> acc

and its_exp_fold fn acc s tl rl =
  let fn a x t = if x then ity_exp_fold fn a t else a in
  dfold2 fn acc s.its_arg_exp tl s.its_reg_exp rl

let reg_exp_fold fn acc reg =
  its_exp_fold fn acc reg.reg_its reg.reg_args reg.reg_regs

let ity_exp_regs regs ity = ity_exp_fold Sreg.add_left regs ity

let rec reg_rch_regs s reg = reg_exp_fold reg_rch_regs (Sreg.add reg s) reg
let     ity_rch_regs s ity = ity_exp_fold reg_rch_regs s ity

let rec reg_r_reachable r reg = reg_equal r reg ||
                                Util.any reg_exp_fold (reg_r_reachable r) reg
let     ity_r_reachable r ity = Util.any ity_exp_fold (reg_r_reachable r) ity

let rec reg_r_stale rs cv reg = Sreg.mem reg rs || not (Mreg.mem reg cv) &&
                                Util.any reg_exp_fold (reg_r_stale rs cv) reg
let     ity_r_stale rs cv ity = Util.any ity_exp_fold (reg_r_stale rs cv) ity

(* traversal functions on non-ghost regions *)

let rec ity_vis_fold fn acc ity =
  if ity.ity_imm then acc else
  match ity.ity_node with
  | Ityapp (s,tl,rl) -> its_vis_fold fn acc s tl rl
  | Ityreg r -> reg_vis_fold fn acc r
  | Ityvar _ -> acc

and its_vis_fold fn acc s tl rl =
  let fn a v t = if v then ity_vis_fold fn a t else a in
  dfold2 fn acc s.its_arg_vis tl s.its_reg_vis rl

and reg_vis_fold fn acc reg =
  its_exp_fold fn (fn acc reg) reg.reg_its reg.reg_args reg.reg_regs

let ity_vis_regs regs ity = ity_vis_fold Sreg.add_left regs ity

(* collect exposed type variables *)

let rec ity_exp_vars vars ity = match ity.ity_node with
  | Ityapp (s,tl,rl) ->
      let fn a x t = if x then ity_exp_vars a t else a in
      dfold2 fn vars s.its_arg_exp tl s.its_reg_exp rl
  | Ityvar (v,false) -> Stv.add v vars
  | Ityvar (_,true) | Ityreg _ -> vars

(* collect non-ghost type variables *)

let rec ity_vis_vars vars ity = match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl} | Ityapp (s,tl,_) ->
      let fn a v t = if v then ity_vis_vars a t else a in
      List.fold_left2 fn vars s.its_arg_vis tl
  | Ityvar (v,false) -> Stv.add v vars
  | Ityvar (_,true) -> vars

(* collect non-updatable type variables *)

let rec ity_realvars vars ity = match ity.ity_node with
  | Ityreg {reg_args = tl} | Ityapp (_,tl,_) ->
      List.fold_left ity_realvars vars tl
  | Ityvar (v,false) -> Stv.add v vars
  | Ityvar (_,true) -> vars

let rec ity_imm_vars vars ity = match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl} | Ityapp (s,tl,_) ->
      let fn a i t = if i then ity_realvars a t
                          else ity_imm_vars a t in
      List.fold_left2 fn vars s.its_arg_imm tl
  | Ityvar _ -> vars

(* type matching *)

exception BadItyArity of itysymbol * int
exception BadRegArity of itysymbol * int

exception DuplicateRegion of region
exception UnboundRegion of region

exception ImpureType of tvsymbol * ity

type ity_subst = {
  isb_var : ity Mtv.t;
  isb_pur : ity Mtv.t;
  isb_reg : ity Mreg.t;
}

let isb_empty = {
  isb_var = Mtv.empty;
  isb_pur = Mtv.empty;
  isb_reg = Mreg.empty;
}

exception TypeMismatch of ity * ity * ity_subst

let ity_equal_check t1 t2 = if not (ity_equal t1 t2) then
  raise (TypeMismatch (t1, t2, isb_empty))

let reg_equal_check r1 r2 = if not (reg_equal r1 r2) then
  raise (TypeMismatch (ity_reg r1, ity_reg r2, isb_empty))

let ity_full_inst sbs ity =
  let rec inst ity = match ity.ity_node with
    | Ityreg r -> Mreg.find r sbs.isb_reg
    | Ityapp (s,tl,rl) ->
        ity_app_unsafe s (List.map inst tl) (List.map inst rl)
    | Ityvar (v,false) -> Mtv.find v sbs.isb_var
    | Ityvar (v,true) ->
        try Mtv.find v sbs.isb_pur with Not_found ->
        ity_purify (Mtv.find v sbs.isb_var) in
  if ity.ity_imm && ity_closed ity then ity else inst ity

let reg_full_inst sbs reg = Mreg.find reg sbs.isb_reg

let add_or_keep eq n = function
  | None -> Some n
  | Some o as r when eq o n -> r
  | _ -> raise Exit

let rec ity_match sbs ity1 ity2 =
  let set = add_or_keep ity_equal ity2 in
  match ity1.ity_node, ity2.ity_node with
  | Ityapp (s1,l1,r1), Ityapp (s2,l2,r2) when its_equal s1 s2 ->
      dfold2 ity_match sbs l1 l2 r1 r2
  | Ityreg r1, _ ->
      reg_match sbs r1 ity2
  | Ityvar (v1, false), _ ->
      if Mtv.mem v1 sbs.isb_pur &&
         not (ity_equal (ity_purify ity2) (Mtv.find v1 sbs.isb_pur))
      then raise Exit;
      { sbs with isb_var = Mtv.change set v1 sbs.isb_var }
  | Ityvar (v1, true), _ when ity_pure ity2 ->
      if Mtv.mem v1 sbs.isb_var &&
         not (ity_equal ity2 (ity_purify (Mtv.find v1 sbs.isb_var)))
      then raise Exit;
      { sbs with isb_pur = Mtv.change set v1 sbs.isb_pur }
  | Ityvar (v1, true), _ -> raise (ImpureType (v1, ity2))
  | _ -> raise Exit

and reg_match sbs reg1 ity2 =
  let seen = ref false in
  let set = add_or_keep (fun o n -> seen := true; ity_equal o n) ity2 in
  let sbs = { sbs with isb_reg = Mreg.change set reg1 sbs.isb_reg } in
  if !seen then sbs else
  match ity2.ity_node with
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl} | Ityapp (s,tl,rl)
    when its_equal reg1.reg_its s ->
      dfold2 ity_match sbs reg1.reg_args tl reg1.reg_regs rl
  | _ -> raise Exit

let ity_match sbs ity1 ity2 = try ity_match sbs ity1 ity2
  with Exit -> raise (TypeMismatch (ity1, ity2, sbs))

let reg_match sbs reg1 ity2 = try reg_match sbs reg1 ity2
  with Exit -> raise (TypeMismatch (ity_reg reg1, ity2, sbs))

let ity_freeze sbs ity = ity_match sbs ity ity
let reg_freeze sbs reg = reg_match sbs reg (ity_reg reg)

(* raw type constructors *)

let ity_app_raw sbs id s tl rl = match s.its_def with
  | Some { ity_node = Ityreg r } ->
      let tl = List.map (ity_full_inst sbs) r.reg_args in
      let rl = List.map (ity_full_inst sbs) r.reg_regs in
      ity_reg (mk_reg id r.reg_its tl rl)
  | None when s.its_privmut || s.its_mfields <> [] ->
      ity_reg (mk_reg id s tl rl)
  | Some ity -> ity_full_inst sbs ity
  | None -> ity_app_unsafe s tl rl

let create_region_raw sbs id s tl rl =
  match (ity_app_raw sbs id s tl rl).ity_node with
  | Ityreg r -> r
  | _ -> invalid_arg "Ity.create_region"

let ity_app_pure_raw sbs s tl rl = match s.its_def with
  | Some { ity_node = Ityreg r } ->
      let tl = List.map (ity_full_inst sbs) r.reg_args in
      let rl = List.map (ity_full_inst sbs) r.reg_regs in
      ity_app_unsafe r.reg_its tl rl
  | Some ity -> ity_full_inst sbs ity
  | None -> ity_app_unsafe s tl rl

(* smart type constructors *)

let its_check_args s tl =
  if List.length s.its_ts.ts_args <> List.length tl
  then raise (BadItyArity (s, List.length tl))

let its_match_args s tl =
  try {
    isb_var = List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty;
    isb_pur = Mtv.empty;
    isb_reg = Mreg.empty }
  with Invalid_argument _ -> raise (BadItyArity (s, List.length tl))

let its_match_regs s tl rl =
  try List.fold_left2 reg_match (its_match_args s tl) s.its_regions rl
  with Invalid_argument _ -> raise (BadRegArity (s, List.length rl))

let its_inst_regs fresh_reg s tl =
  let rec ity_inst sbs ity = match ity.ity_node with
    | Ityreg r ->
        reg_inst sbs r
    | Ityapp (s,tl,rl) ->
        let sbs, tl = Lists.map_fold_left ity_inst sbs tl in
        let sbs, rl = Lists.map_fold_left ity_inst sbs rl in
        sbs, ity_app_unsafe s tl rl
    | Ityvar (v, false) ->
        sbs, Mtv.find v sbs.isb_var
    | Ityvar (v,true) ->
        try sbs, Mtv.find v sbs.isb_pur with Not_found ->
        sbs, ity_purify (Mtv.find v sbs.isb_var)
  and reg_inst sbs r =
    try sbs, Mreg.find r sbs.isb_reg with Not_found ->
    let sbs, tl = Lists.map_fold_left ity_inst sbs r.reg_args in
    let sbs, rl = Lists.map_fold_left ity_inst sbs r.reg_regs in
    let ity = fresh_reg (id_clone r.reg_name) r.reg_its tl rl in
    { sbs with isb_reg = Mreg.add r ity sbs.isb_reg }, ity in
  Lists.map_fold_left reg_inst (its_match_args s tl) s.its_regions

let its_match_smart fresh_reg s tl rl =
  if rl <> [] then its_match_regs s tl rl, rl else
  if s.its_regions = [] && s.its_def = None
  then (its_check_args s tl; isb_empty, [])
  else its_inst_regs fresh_reg s tl

let create_region id s tl rl =
  let fresh id s tl rl = ity_reg (mk_reg id s tl rl) in
  let sbs, rl = its_match_smart fresh s tl rl in
  create_region_raw sbs id s tl rl

let ity_app s tl rl =
  let fresh id s tl rl = ity_reg (mk_reg id s tl rl) in
  let sbs, rl = its_match_smart fresh s tl rl in
  ity_app_raw sbs (id_fresh "rho") s tl rl

let ity_app_pure s tl rl =
  let pure _ s tl rl = ity_app_unsafe s tl rl in
  let sbs, rl = its_match_smart pure s tl rl in
  ity_app_pure_raw sbs s tl rl

(* itysymbol creation *)

let create_its, restore_its =
  let ts_to_its = Wts.create 17 in
  (fun ~ts ~pm ~mfld ~regs ~aimm ~aexp ~avis ~afrz ~rexp ~rvis ~rfrz ~def ->
    let its = {
      its_ts      = ts;
      its_privmut = pm;
      its_mfields = mfld;
      its_regions = regs;
      its_arg_imm = aimm;
      its_arg_exp = aexp;
      its_arg_vis = avis;
      its_arg_frz = afrz;
      its_reg_exp = rexp;
      its_reg_vis = rvis;
      its_reg_frz = rfrz;
      its_def     = def;
    } in
    Wts.set ts_to_its ts its;
    its),
  (fun ts -> Wts.find ts_to_its ts)

let rec ity_of_ty ty = match ty.ty_node with
  | Tyvar v -> ity_var v
  | Tyapp (s,tl) ->
      let s = try restore_its s with Not_found ->
        invalid_arg "Ity.ity_of_ty" in
      ity_app s (List.map ity_of_ty tl) []

let rec ity_of_ty_pure ty = match ty.ty_node with
  | Tyvar v -> ity_var_pure v
  | Tyapp (s,tl) ->
      let s = try restore_its s with Not_found ->
        invalid_arg "Ity.ity_of_ty_pure" in
      ity_app_pure s (List.map ity_of_ty_pure tl) []

let its_of_ts ts imm =
  let tl = List.map Util.ttrue ts.ts_args in
  let il = if imm then tl else List.map Util.ffalse ts.ts_args in
  let def = match ts.ts_def with None -> None | Some def ->
    let def = ity_of_ty def in assert def.ity_imm; Some def in
  create_its ~ts ~pm:false ~mfld:[] ~regs:[] ~aimm:il ~aexp:tl
    ~avis:tl ~afrz:tl ~rexp:[] ~rvis:[] ~rfrz:[] ~def

let create_itysymbol_pure id args =
  its_of_ts (create_tysymbol id args None) true

let create_itysymbol_alias id args def =
  let ts = create_tysymbol id args (Some (ty_of_ity def)) in
  let ity = match def.ity_node with (* ignore the top region *)
    | Ityreg r -> ity_app_pure r.reg_its r.reg_args r.reg_regs
    | _ -> def in
  let regs = Sreg.elements (ity_top_regs Sreg.empty ity) in
  let tl = List.map Util.ttrue args in
  let rl = List.map Util.ttrue regs in
  create_its ~ts ~pm:false ~mfld:[] ~regs ~aimm:tl ~aexp:tl
    ~avis:tl ~afrz:tl ~rexp:rl ~rvis:rl ~rfrz:rl ~def:(Some def)

exception ImpureField of ity

let create_itysymbol_rich id args pm flds =
  let ts = create_tysymbol id args None in
  let collect_vis fn acc =
    Mpv.fold (fun f _ a -> if f.pv_ghost then a else fn a f.pv_ity) flds acc in
  let collect_imm fn acc =
    Mpv.fold (fun f m a -> if m then a else fn a f.pv_ity) flds acc in
  let collect_all fn acc =
    Mpv.fold (fun f _ a -> fn a f.pv_ity) flds acc in
  let sargs = Stv.of_list args in
  let dargs = collect_all ity_freevars Stv.empty in
  if not (Stv.subset dargs sargs) then
    raise (Ty.UnboundTypeVar (Stv.choose (Stv.diff dargs sargs)));
  let mfld = Mpv.fold (fun f m l -> if m then f::l else l) flds [] in
  if pm then begin (* private mutable record *)
    let tl = List.map Util.ttrue args in
    Mpv.iter (fun {pv_vs = v; pv_ity = i} _ -> if not i.ity_imm
      then Loc.error ?loc:v.vs_name.id_loc (ImpureField i)) flds;
    create_its ~ts ~pm ~mfld ~regs:[] ~aimm:tl ~aexp:tl ~avis:tl
      ~afrz:tl ~rexp:[] ~rvis:[] ~rfrz:[] ~def:None
  end else (* non-private updatable type *)
    let regs = Sreg.elements (collect_all ity_top_regs Sreg.empty) in
    let check_args s = List.map (Stv.contains s) args in
    let check_regs s = List.map (Sreg.contains s) regs in
    let aimm = check_args (collect_all ity_imm_vars Stv.empty) in
    let aexp = check_args (collect_all ity_exp_vars Stv.empty) in
    let rexp = check_regs (collect_all ity_exp_regs Sreg.empty) in
    let avis = check_args (collect_vis ity_vis_vars Stv.empty) in
    let rvis = check_regs (collect_vis ity_vis_regs Sreg.empty) in
    let afrz = check_args (collect_imm ity_exp_vars Stv.empty) in
    let rfrz = check_regs (collect_imm ity_exp_regs Sreg.empty) in
    create_its ~ts ~pm ~mfld ~regs ~aimm ~aexp ~avis ~afrz ~rexp
      ~rvis ~rfrz ~def:None

(** pvsymbol creation *)

let create_pvsymbol id ghost ity = {
  pv_vs    = create_vsymbol id (ty_of_ity ity);
  pv_ity   = ity;
  pv_ghost = ghost;
}

let create_pvsymbol, restore_pv =
  let vs_to_pv = Wvs.create 17 in
  (fun id ?(ghost=false) ity ->
    let pv = create_pvsymbol id ghost ity in
    Wvs.set vs_to_pv pv.pv_vs pv;
    pv),
  (fun vs -> Wvs.find vs_to_pv vs)

let freeze_pv v s = ity_freeze s v.pv_ity

let pvs_of_vss pvs vss =
  Mvs.fold (fun vs _ s -> Spv.add (restore_pv vs) s) vss pvs

let t_freepvs pvs t = pvs_of_vss pvs (t_vars t)

(** builtin symbols *)

let its_int  = its_of_ts ts_int  true
let its_real = its_of_ts ts_real true
let its_bool = its_of_ts ts_bool true
let its_func = its_of_ts ts_func true

let ity_int  = ity_app its_int  [] []
let ity_real = ity_app its_real [] []
let ity_bool = ity_app its_bool [] []

let ity_func a b = ity_app its_func [a;b] []
let ity_pred a   = ity_app its_func [a;ity_bool] []

let its_tuple = Hint.memo 17 (fun n -> its_of_ts (ts_tuple n) false)

let ity_tuple tl = ity_app (its_tuple (List.length tl)) tl []

let ts_unit  = ts_tuple  0
let its_unit = its_tuple 0

let ty_unit  = ty_tuple  []
let ity_unit = ity_tuple []

(* exception symbols *)

type xsymbol = {
  xs_name : ident;
  xs_ity  : ity; (* closed and pure *)
}

let xs_equal : xsymbol -> xsymbol -> bool = (==)
let xs_hash xs = id_hash xs.xs_name
let xs_compare xs1 xs2 = id_compare xs1.xs_name xs2.xs_name

let create_xsymbol id ity =
  if not (ity_closed ity) then Loc.errorm ?loc:id.pre_loc
    "Exception %s has a polymorphic type" id.pre_name;
  if not ity.ity_imm then Loc.errorm ?loc:id.pre_loc
    "The type of exception %s has mutable components" id.pre_name;
  { xs_name = id_register id; xs_ity = ity; }

module Exn = MakeMSH (struct
  type t = xsymbol
  let tag xs = Weakhtbl.tag_hash xs.xs_name.id_tag
end)

module Sexn = Exn.S
module Mexn = Exn.M

(* effects *)

exception IllegalSnapshot of ity
exception IllegalAlias of region
exception AssignPrivate of region
exception BadGhostWrite of pvsymbol * region
exception StaleVariable of pvsymbol * region
exception DuplicateField of region * pvsymbol
exception GhostDivergence

type effect = {
  eff_reads  : Spv.t;         (* known variables *)
  eff_writes : Spv.t Mreg.t;  (* modifications to specific fields *)
  eff_taints : Sreg.t;        (* ghost modifications *)
  eff_covers : Sreg.t;        (* surviving writes *)
  eff_resets : Sreg.t;        (* locked by covers *)
  eff_raises : Sexn.t;        (* raised exceptions *)
  eff_oneway : bool;          (* non-termination *)
  eff_ghost  : bool;          (* ghost status *)
}

let eff_empty = {
  eff_reads  = Spv.empty;
  eff_writes = Mreg.empty;
  eff_taints = Sreg.empty;
  eff_covers = Sreg.empty;
  eff_resets = Sreg.empty;
  eff_raises = Sexn.empty;
  eff_oneway = false;
  eff_ghost  = false;
}

let eff_equal e1 e2 =
  Spv.equal e1.eff_reads e2.eff_reads &&
  Mreg.equal Spv.equal e1.eff_writes e2.eff_writes &&
  Sreg.equal e1.eff_taints e2.eff_taints &&
  Sreg.equal e1.eff_covers e2.eff_covers &&
  Sreg.equal e1.eff_resets e2.eff_resets &&
  Sexn.equal e1.eff_raises e2.eff_raises &&
  e1.eff_oneway = e2.eff_oneway &&
  e1.eff_ghost = e2.eff_ghost

let eff_pure e =
  Mreg.is_empty e.eff_writes &&
  Sexn.is_empty e.eff_raises &&
  not e.eff_oneway

let check_covers {eff_resets = rst; eff_covers = cvr} pvs =
  if not (Mreg.is_empty rst) then Spv.iter (fun v ->
    if ity_r_stale rst cvr v.pv_ity then Sreg.iter (fun r ->
      if ity_r_stale (Sreg.singleton r) cvr v.pv_ity then
        raise (StaleVariable (v,r))) rst) pvs

let check_taints tnt pvs =
  if not (Sreg.is_empty tnt) then Spv.iter (fun v ->
    if not v.pv_ghost then ity_vis_fold (fun () r ->
      if Sreg.mem r tnt then raise (BadGhostWrite (v,r))) () v.pv_ity) pvs

let visible_writes e =
  Mreg.subdomain (fun {reg_its = {its_privmut = priv}} fs ->
    priv || Spv.exists (fun fd -> not fd.pv_ghost) fs) e.eff_writes

let visible_reads e =
  Spv.fold (fun {pv_ghost = gh; pv_ity = ity} s ->
    if gh then s else ity_vis_regs s ity) e.eff_reads Sreg.empty

let reset_taints e =
  let tnt = if e.eff_ghost then visible_writes e else
    Sreg.diff (visible_writes e) (visible_reads e) in
  if e.eff_ghost then check_taints tnt e.eff_reads;
  { e with eff_taints = tnt }

let eff_ghostify gh e =
  if e.eff_ghost || not gh then e else
  if e.eff_oneway then raise GhostDivergence else
  reset_taints { e with eff_ghost = true }

let eff_diverge e = if e.eff_oneway then e else
  if e.eff_ghost then raise GhostDivergence else
  { e with eff_oneway = true }

let eff_read_pre rd e =
  if Spv.is_empty rd then e else
  let _ = check_taints e.eff_taints rd in
  { e with eff_reads = Spv.union e.eff_reads rd }

let eff_read_post e rd =
  if Spv.is_empty rd then e else
  let _ = check_covers e rd in
  let _ = check_taints e.eff_taints rd in
  { e with eff_reads = Spv.union e.eff_reads rd }

let eff_bind rd e = if Mpv.is_empty rd then e else
  { e with eff_reads = Mpv.set_diff e.eff_reads rd }

let eff_read rd =
  if Spv.is_empty rd then eff_empty else
  { eff_empty with eff_reads = rd }

let eff_read_single v = eff_read (Spv.singleton v)
let eff_read_single_pre v e = eff_read_pre (Spv.singleton v) e
let eff_read_single_post e v = eff_read_post e (Spv.singleton v)
let eff_bind_single v e = eff_bind (Spv.singleton v) e

let check_mutable_field fn r f =
  if not (List.memq f r.reg_its.its_mfields) then invalid_arg fn

let read_regs rd =
  Spv.fold (fun v s -> ity_rch_regs s v.pv_ity) rd Sreg.empty

(*TODO? add the third arg (resets) and check the invariants *)
let eff_write rd wr =
  if Mreg.is_empty wr then { eff_empty with eff_reads = rd } else
  let kn = read_regs rd in
  let wr = Mreg.filter (fun ({reg_its = {its_privmut = p}} as r) fs ->
    if not p && Spv.is_empty fs then invalid_arg "Ity.eff_write";
    Spv.iter (check_mutable_field "Ity.eff_write" r) fs;
    Sreg.mem r kn) wr in
  reset_taints { eff_empty with eff_reads = rd; eff_writes = wr;
                                eff_covers = Mreg.domain wr }

(*TODO: should we use it and what semantics to give? *)
let eff_reset ({eff_writes = wr} as e) rs =
  if not (Mreg.set_disjoint wr rs) then invalid_arg "Ity.eff_reset";
  { e with eff_resets = Sreg.union rs e.eff_resets }

exception IllegalAssign of region * region * region

let rec ity_skel_check t1 t2 =
  if not (ity_equal t1 t2) then
  match t1.ity_node, t2.ity_node with
  | Ityreg {reg_its = s1; reg_args = tl1; reg_regs = rl1},
    Ityreg {reg_its = s2; reg_args = tl2; reg_regs = rl2}
  | Ityapp (s1,tl1,rl1), Ityapp (s2,tl2,rl2)
    when its_equal s1 s2 ->
      List.iter2 ity_skel_check tl1 tl2;
      List.iter2 ity_skel_check rl1 rl2
  | Ityvar (v1,p1), Ityvar (v2,p2)
    when tv_equal v1 v2 && p1 = p2 -> ()
  | _ -> raise (TypeMismatch (t1,t2,isb_empty))

let eff_assign asl =
  (* compute all effects except eff_resets *)
  let get_reg = function
    | {pv_ity = {ity_node = Ityreg r}} -> r
    | _ -> invalid_arg "Ity.eff_assign" in
  let writes = List.fold_left (fun wr (r,f,v) ->
    let r = get_reg r and ity = v.pv_ity in
    check_mutable_field "Ity.eff_assign" r f;
    if r.reg_its.its_privmut then raise (AssignPrivate r);
    Mreg.change (fun fs -> Some (match fs with
      | Some fs -> Mpv.add_new (DuplicateField (r,f)) f ity fs
      | None    -> Mpv.singleton f ity)) r wr) Mreg.empty asl in
  let ghost = List.for_all (fun (r,f,v) ->
    r.pv_ghost || f.pv_ghost || v.pv_ghost) asl in
  let taint = List.fold_left (fun s (r,f,v) ->
    if (r.pv_ghost || v.pv_ghost) && not f.pv_ghost then
      Sreg.add (get_reg r) s else s) Sreg.empty asl in
  let reads = List.fold_left (fun s (r,_,v) ->
    Spv.add r (Spv.add v s)) Spv.empty asl in
  check_taints taint reads;
  (* compute the region transitions under writes *)
  let reg_rexp {reg_its = s; reg_args = tl; reg_regs = rl} fs =
    let ity_rexp xl t = ity_exp_fold (fun l r -> r :: l) xl t in
    let sbs = its_match_regs s tl rl in
    let mfield xl f =
      let tf = ity_full_inst sbs f.pv_ity in
      let tt = Mpv.find_def tf f fs in
      ity_skel_check tf tt; ity_rexp xl tt in
    let xl = List.fold_left mfield [] s.its_mfields in
    let frozen xl frz t = if frz then ity_rexp xl t else xl in
    dfold2 frozen xl s.its_arg_frz tl s.its_reg_frz rl in
  let rec stitch pl rf rt fs =
    let link pl rf rt =
      stitch ((rf,rt)::pl) rf rt (Mreg.find_def Mpv.empty rt writes) in
    List.fold_left2 link pl (reg_rexp rf Mpv.empty) (reg_rexp rt fs) in
  let add_write r fs m =
    let pl = stitch [] r r fs in
    let fit m = Some (match m with
      | Some m -> Mreg.add r pl m
      | None -> Mreg.singleton r pl) in
    Mint.change fit (- List.length pl) m in
  let m = Mreg.fold add_write writes Mint.empty in
  (* compute resets as non-identity region transitions *)
  let add_bind r1 r2 m = Mreg.change (function
    | (Some r3) as v when reg_equal r2 r3 -> v
    | Some r3 -> raise (IllegalAssign (r1,r2,r3))
    | None -> Some r2) r1 m in
  let add_pair (rst, mt, mf) (r1,r2) =
    let rst = if reg_equal r1 r2 then rst
    else Sreg.add r1 (Sreg.add r2 rst) in
    rst, add_bind r1 r2 mt, add_bind r2 r1 mf in
  let add_write r pl ((rst,_,_) as acc) =
    if Sreg.mem r rst then acc else
    List.fold_left add_pair acc pl in
  let add_level _ mpl acc =
    Mreg.fold add_write mpl acc in
  let resets,_,_ = Mint.fold add_level m (Sreg.empty,Mreg.empty,Mreg.empty) in
  (* construct the effect *)
  { eff_reads  = reads;
    eff_writes = Mreg.map Mpv.domain writes;
    eff_taints = taint;
    eff_covers = Mreg.domain (Mreg.set_diff writes resets);
    eff_resets = resets;
    eff_raises = Sexn.empty;
    eff_oneway = false;
    eff_ghost  = ghost }

let eff_reset_overwritten ({eff_writes = wr} as e) =
  if not (Sreg.is_empty e.eff_resets) then
    invalid_arg "Ity.eff_reset_overwritten";
  let rec reg2 regs reg =
    if Mreg.mem reg wr then regs else
    reg_exp_fold reg2 (Sreg.add reg regs) reg in
  let ity2 regs ity = ity_exp_fold reg2 regs ity in
  let add_write ({reg_its = s} as r) fs (svv, rst) =
    let frozen svv frz t = if frz then ity2 svv t else svv in
    let svv = dfold2 frozen (Sreg.add r svv)
      s.its_arg_frz r.reg_args s.its_reg_frz r.reg_regs in
    let sbs = its_match_regs s r.reg_args r.reg_regs in
    let add_mfld (svv,rst) f =
      let t = ity_full_inst sbs f.pv_ity in
      if Spv.mem f fs then svv, ity2 rst t else ity2 svv t, rst in
    List.fold_left add_mfld (svv,rst) s.its_mfields in
  let svv, rst = Mreg.fold add_write wr (Sreg.empty,Sreg.empty) in
  { e with eff_resets = Sreg.diff rst svv }

let eff_raise e x = { e with eff_raises = Sexn.add x e.eff_raises }
let eff_catch e x = { e with eff_raises = Sexn.remove x e.eff_raises }

let merge_fields _ f1 f2 = Some (Spv.union f1 f2)

let remove_stale e srg =
  Mreg.filter (fun r _ -> not (reg_r_stale e.eff_resets e.eff_covers r)) srg

let eff_union e1 e2 = {
  eff_reads  = Spv.union e1.eff_reads e2.eff_reads;
  eff_writes = Mreg.union merge_fields e1.eff_writes e2.eff_writes;
  eff_taints = Sreg.union e1.eff_taints e2.eff_taints;
  eff_covers = Sreg.union (remove_stale e2 e1.eff_covers)
                          (remove_stale e1 e2.eff_covers);
  eff_resets = Sreg.union e1.eff_resets e2.eff_resets;
  eff_raises = Sexn.union e1.eff_raises e2.eff_raises;
  eff_oneway = e1.eff_oneway || e2.eff_oneway;
  eff_ghost  = e2.eff_ghost }

(* TODO: remove later *)
let eff_union e1 e2 =
  let e = eff_union e1 e2 in
  assert (Sreg.disjoint e.eff_covers e.eff_resets);
  assert (Mreg.for_all (fun r _ -> reg_r_stale e.eff_resets e.eff_covers r)
            (Mreg.set_diff e.eff_writes e.eff_covers) );
  e

let eff_contagious e = e.eff_ghost &&
  not (Sexn.is_empty e.eff_raises (* && no local exceptions *))

let eff_union_par e1 e2 =
  let e1 = eff_ghostify e2.eff_ghost e1 in
  let e2 = eff_ghostify e1.eff_ghost e2 in
  check_taints e1.eff_taints e2.eff_reads;
  check_taints e2.eff_taints e1.eff_reads;
  eff_union e1 e2

let eff_union_seq e1 e2 =
  let e1 = eff_ghostify e2.eff_ghost e1 in
  let e2 = eff_ghostify (eff_contagious e1) e2 in
  check_taints e1.eff_taints e2.eff_reads;
  check_taints e2.eff_taints e1.eff_reads;
  check_covers e1 e2.eff_reads;
  eff_union e1 e2

(* NOTE: do not export this function *)
let eff_inst sbs e =
  (* all modified or reset regions in e must be instantiated into
     distinct regions. We allow regions that are not affected directly
     to be aliased, even if they contain modified or reset subregions:
     the values are still updated at the same program points and with
     the same postconditions, as in the initial verified code. *)
  let inst src = Mreg.fold (fun r v acc ->
    let t = reg_full_inst sbs r in match t.ity_node with
      | Ityreg r -> Mreg.add_new (IllegalAlias r) r v acc
      | _ -> raise (IllegalSnapshot t)) src Mreg.empty in
  let writes = inst e.eff_writes in
  let resets = inst e.eff_resets in
  let taints = inst e.eff_taints in
  let covers = inst e.eff_covers in
  let impact = Mreg.merge (fun r fld void -> match fld, void with
    | Some _, Some _ -> raise (IllegalAlias r)
    | _ -> Some ()) writes resets in
  (* all type variables and unaffected regions must be instantiated
     outside [impact]. Every region in the instantiated execution
     is either brought in by the type substitution or instantiates
     one of the original regions. *)
  let sreg = Mreg.set_diff sbs.isb_reg e.eff_writes in
  let sreg = Mreg.set_diff sreg e.eff_resets in
  let dst = Mreg.fold (fun _ i s -> match i.ity_node with
    | Ityreg r -> Sreg.add r s | _ -> s) sreg Sreg.empty in
  let dst = Mtv.fold (fun _ i s -> ity_freeregs s i) sbs.isb_var dst in
  ignore (Mreg.inter (fun r _ _ -> raise (IllegalAlias r)) dst impact);
  { e with eff_writes = writes; eff_taints = taints;
           eff_covers = covers; eff_resets = resets }

(** specification *)

type pre = term   (* precondition: pre_fmla *)
type post = term  (* postcondition: eps result . post_fmla *)

let create_post vs f = t_eps_close vs f

let open_post f = match f.t_node with
  | Teps bf -> t_open_bound bf
  | _ -> invalid_arg "Ity.open_post"

type cty = {
  cty_args   : pvsymbol list;
  cty_pre    : pre list;
  cty_post   : post list;
  cty_xpost  : post list Mexn.t;
  cty_oldies : pvsymbol Mpv.t;
  cty_effect : effect;
  cty_result : ity;
  cty_freeze : ity_subst;
}

let cty_unsafe args pre post xpost oldies effect result freeze = {
  cty_args   = args;
  cty_pre    = pre;
  cty_post   = post;
  cty_xpost  = xpost;
  cty_oldies = oldies;
  cty_effect = effect;
  cty_result = result;
  cty_freeze = freeze;
}

let cty_reads c =
  List.fold_right Spv.remove c.cty_args c.cty_effect.eff_reads

let cty_ghost c = c.cty_effect.eff_ghost

let cty_ghostify gh ({cty_effect = eff} as c) =
  if eff.eff_ghost || not gh then c else
  { c with cty_effect = eff_ghostify gh eff }

let spec_t_fold fn_t acc pre post xpost =
  let fn_l a fl = List.fold_left fn_t a fl in
  let acc = fn_l (fn_l acc pre) post in
  Mexn.fold (fun _ l a -> fn_l a l) xpost acc

let check_tvs reads result pre post xpost =
  (* every type variable in spec comes either from a known vsymbol
     or from the result type. We need this to ensure that we always
     can do a full instantiation. TODO: do we really need this? *)
  let add_pv v s = ity_freevars s v.pv_ity in
  let tvs = ity_freevars Stv.empty result in
  let tvs = Spv.fold add_pv reads tvs in
  let check_tvs () t =
    let ttv = t_ty_freevars Stv.empty t in
    if not (Stv.subset ttv tvs) then Loc.error ?loc:t.t_loc
      (UnboundTypeVar (Stv.choose (Stv.diff ttv tvs))) in
  spec_t_fold check_tvs () pre post xpost

let check_pre pre = List.iter (fun p -> if p.t_ty <> None
  then Loc.error ?loc:p.t_loc (Term.FmlaExpected p)) pre

let check_post exn ity post =
  let ty = ty_of_ity ity in
  List.iter (fun q -> match q.t_node with
    | Teps _ -> Ty.ty_equal_check ty (t_type q)
    | _ -> raise exn) post

let create_cty args pre post xpost oldies effect result =
  let exn = Invalid_argument "Ity.create_cty" in
  (* pre, post, and xpost are well-typed *)
  check_pre pre; check_post exn result post;
  Mexn.iter (fun xs xq -> check_post exn xs.xs_ity xq) xpost;
  (* the arguments must be pairwise distinct *)
  let sarg = List.fold_right (Spv.add_new exn) args Spv.empty in
  (* complete the reads and freeze the external context.
     oldies must be fresh: collisions with args and external
     reads are forbidden, to simplify instantiation later. *)
  let preads = spec_t_fold t_freepvs sarg pre [] Mexn.empty in
  let qreads = spec_t_fold t_freepvs Spv.empty [] post xpost in
  let effect = eff_read_post effect qreads in
  Mpv.iter (fun {pv_ghost = gh; pv_ity = o} {pv_ity = t} ->
    if not (gh && o == ity_purify t) then raise exn) oldies;
  let oldies = Mpv.set_inter oldies effect.eff_reads in
  let effect = eff_bind oldies effect in
  let preads = Mpv.fold (Util.const Spv.add) oldies preads in
  if not (Mpv.set_disjoint preads oldies) then raise exn;
  let effect = eff_read_pre preads effect in
  let freeze = Spv.diff effect.eff_reads sarg in
  let freeze = Spv.fold freeze_pv freeze isb_empty in
  check_tvs effect.eff_reads result pre post xpost;
  (* remove exceptions whose postcondition is False *)
  let filter _ xq () =
    let is_false q = t_equal (snd (open_post q)) t_false in
    if List.exists is_false xq then None else Some xq in
  let xpost = Mexn.inter filter xpost effect.eff_raises in
  let raises = Mexn.set_inter effect.eff_raises xpost in
  let effect = { effect with eff_raises = raises } in
  (* remove effects on unknown regions. We reset eff_taints
     instead of simply filtering the existing set in order
     to get rid of non-ghost writes into ghost regions.
     These writes can occur when a bound regular variable
     aliases an external ghost region:
        let (* non-ghost *) x = None in
        let ghost y = if true then x else Some ghost_ref in
        match x with Some r -> r := 0 | None -> () end
     The write is regular here, but the only path to it, via
     ghost_ref is ghost. Strictly speaking, such writes can
     be removed (we cannot create a real regular alias to a
     ghost location), but it is simpler to just recast them
     as ghost, to keep the type signature consistent. *)
  let rknown = read_regs effect.eff_reads in
  let vknown = ity_rch_regs rknown result in
  let effect = reset_taints { effect with
    eff_writes = Mreg.set_inter effect.eff_writes rknown;
    eff_covers = Mreg.set_inter effect.eff_covers rknown;
    eff_resets = Mreg.set_inter effect.eff_resets vknown} in
  cty_unsafe args pre post xpost oldies effect result freeze

let cty_apply c vl args res =
  let vsb_add vsb {pv_vs = u} v =
    if vs_equal u v.pv_vs then vsb else Mvs.add u v vsb in
  let match_v isb u v = ity_match isb u.pv_ity v.pv_ity in
  (* stage 1: apply c to vl *)
  let rec apply gh same isb vsb ul vl = match ul, vl with
    | u::ul, v::vl ->
        let gh = gh || (v.pv_ghost && not u.pv_ghost) in
        let same = same && ity_equal u.pv_ity v.pv_ity in
        apply gh same (match_v isb u v) (vsb_add vsb u v) ul vl
    | ul, [] ->
        gh, same, isb, vsb, ul
    | _ -> invalid_arg "Ity.cty_apply" in
  let ghost, same, isb, vsb, cargs =
    apply c.cty_effect.eff_ghost true
      c.cty_freeze Mvs.empty c.cty_args vl in
  let freeze = if same then isb else
    List.fold_right freeze_pv vl c.cty_freeze in
  (* stage 2: compute the substitutions *)
  let rec cut same rul rvl vsb ul tl = match ul, tl with
    | u::ul, vt::tl ->
        let same = same && ity_equal u.pv_ity vt in
        let v = if same && Mvs.is_empty vsb then u else
          let id = id_clone u.pv_vs.vs_name in
          create_pvsymbol id ~ghost:u.pv_ghost vt in
        cut same (u::rul) (v::rvl) (vsb_add vsb u v) ul tl
    | [], [] -> same, rul, rvl, vsb
    | _ -> invalid_arg "Ity.cty_apply" in
  let same, rcargs, rargs, vsb = cut same [] [] vsb cargs args in
  let vsb, oldies = if Mvs.is_empty vsb then vsb, c.cty_oldies else
    Mpv.fold (fun {pv_vs = o} v (s,m) ->
      let id = id_clone o.vs_name in
      let v = Mvs.find_def v v.pv_vs vsb in
      let n = create_pvsymbol id ~ghost:true (ity_purify v.pv_ity) in
      Mvs.add o n s, Mpv.add n v m) c.cty_oldies (vsb, Mpv.empty) in
  let vsb = Mvs.map (fun v -> t_var v.pv_vs) vsb in
  let same = same && ity_equal c.cty_result res in
  if same && vl = [] then (* trivial *) c else
  let isb = if same then isb_empty else
    let isb = ity_match isb c.cty_result res in
    List.fold_left2 match_v isb rcargs rargs in
  (* stage 3: instantiate the effect *)
  let effect =
    if same then c.cty_effect else eff_inst isb c.cty_effect in
  let binds = List.fold_right Spv.add c.cty_args Spv.empty in
  let effect = eff_ghostify ghost (eff_bind binds effect) in
  let reads = List.fold_right Spv.add vl Spv.empty in
  let reads = List.fold_right Spv.add rargs reads in
  let effect = eff_read_pre reads effect in
  (* stage 4: instantiate the specification *)
  let tsb = Mtv.map ty_of_ity
    (Mtv.set_union isb.isb_var isb.isb_pur) in
  let same = same || Mtv.for_all (fun v {ty_node = n} ->
    match n with Tyvar u -> tv_equal u v | _ -> false) tsb in
  let subst_t = if same then (fun t -> t_subst vsb t) else
                      (fun t -> t_ty_subst tsb vsb t) in
  let subst_l l = List.map subst_t l in
  cty_unsafe (List.rev rargs) (subst_l c.cty_pre)
    (subst_l c.cty_post) (Mexn.map subst_l c.cty_xpost)
    oldies effect res freeze

let cty_add_reads c pvs =
  (* the external reads are already frozen and
     the arguments should stay instantiable *)
  let pvs = Spv.diff pvs c.cty_effect.eff_reads in
  { c with cty_effect = eff_read_pre pvs c.cty_effect;
           cty_freeze = Spv.fold freeze_pv pvs c.cty_freeze }

let cty_add_pre pre c = if pre = [] then c else begin check_pre pre;
  let c = cty_add_reads c (List.fold_left t_freepvs Spv.empty pre) in
  check_tvs c.cty_effect.eff_reads c.cty_result pre [] Mexn.empty;
  { c with cty_pre = pre @ c.cty_pre } end

let cty_add_post c post = if post = [] then c else begin
  check_post (Invalid_argument "Ity.cty_add_post") c.cty_result post;
  let c = cty_add_reads c (List.fold_left t_freepvs Spv.empty post) in
  check_tvs c.cty_effect.eff_reads c.cty_result [] post Mexn.empty;
  { c with cty_post = post @ c.cty_post } end

(** pretty-printing *)

open Format
open Pretty

let rprinter = create_ident_printer []
  ~sanitizer:(sanitizer char_to_alpha char_to_alnumus)

let xprinter = create_ident_printer []
  ~sanitizer:(sanitizer char_to_ualpha char_to_alnumus)

let forget_reg r = forget_id rprinter r.reg_name

let print_reg_name fmt r =
  fprintf fmt "@@%s" (id_unique rprinter r.reg_name)

let print_args pr fmt tl = if tl <> [] then
  fprintf fmt "@ %a" (Pp.print_list Pp.space pr) tl

let print_regs pr fmt rl = if rl <> [] then
  fprintf fmt "@ <%a>" (Pp.print_list Pp.comma pr) rl

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let print_its fmt s = print_ts fmt s.its_ts

let rec print_ity pur pri fmt ity = match ity.ity_node with
  | Ityvar (v,p) when pur || not p -> print_tv fmt v
  | Ityvar (v,_) -> fprintf fmt "{%a}" print_tv v
  | Ityapp (s,[t1;t2],[]) when its_equal s its_func ->
      fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_ity pur 1) t1 (print_ity pur 0) t2
  | Ityapp (s,tl,[]) when is_ts_tuple s.its_ts ->
      fprintf fmt "(%a)" (Pp.print_list Pp.comma (print_ity pur 0)) tl
  | Ityapp (s,tl,_) when not (pur || its_immutable s) && ity_pure ity ->
      fprintf fmt "{%a%a}" print_its s (print_args (print_ity true 2)) tl
  | Ityapp (s,tl,_) when not (pur || its_immutable s) ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "{%a}%a")
        print_its s (print_args (print_ity pur 2)) tl
  | Ityapp (s,tl,_) | Ityreg {reg_its = s; reg_args = tl} ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "%a%a")
        print_its s (print_args (print_ity pur 2)) tl

let print_ity fmt ity = print_ity false 0 fmt ity

let rec print_ity_node sb pur pri fmt ity = match ity.ity_node with
  | Ityvar (v,false) ->
      begin match Mtv.find_opt v sb.isb_var with
        | Some ity -> print_ity_node isb_empty pur pri fmt ity
        | None -> print_tv fmt v
      end
  | Ityvar (v,true) ->
      begin match Mtv.find_opt v sb.isb_pur with
        | Some ity -> print_ity_node isb_empty pur pri fmt ity
        | None -> (* creative indentation *)
      begin match Mtv.find_opt v sb.isb_var with
        | Some ity -> print_ity_node isb_empty pur pri fmt (ity_purify ity)
        | None when not pur -> fprintf fmt "{%a}" print_tv v
        | None -> print_tv fmt v
      end end
  | Ityapp (s,[t1;t2],[]) when its_equal s its_func ->
      fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_ity_node sb pur 1) t1 (print_ity_node sb pur 0) t2
  | Ityapp (s,tl,[]) when is_ts_tuple s.its_ts ->
      fprintf fmt "(%a)" (Pp.print_list Pp.comma (print_ity_node sb pur 0)) tl
  | Ityapp (s,tl,_) when pur ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "%a%a")
        print_its s (print_args (print_ity_node sb pur 2)) tl
  | Ityapp (s,tl,rl) when its_immutable s ->
      fprintf fmt (protect_on (pri > 1 && (tl <> [] || rl <> [])) "%a%a%a")
        print_its s (print_args (print_ity_node sb pur 2)) tl
        (print_regs (print_ity_node sb pur 0)) rl
  | Ityapp (s,tl,_) when ity_pure ity ->
      fprintf fmt "{%a%a}"
        print_its s (print_args (print_ity_node sb true 2)) tl
  | Ityapp (s,tl,rl) ->
      fprintf fmt (protect_on (pri > 1 && (tl <> [] || rl <> [])) "{%a}%a%a")
        print_its s (print_args (print_ity_node sb pur 2)) tl
        (print_regs (print_ity_node sb pur 0)) rl
  | Ityreg r ->
      begin match Mreg.find_opt r sb.isb_reg with
        | Some ity -> print_ity_node isb_empty pur pri fmt ity
        | None -> fprintf fmt (protect_on (pri > 1) "%a") (print_reg_node sb) r
      end

and print_reg_node sb fmt r = fprintf fmt "%a%a%a@ %a" print_its r.reg_its
  (print_args (print_ity_node sb false 2)) r.reg_args
  (print_regs (print_ity_node sb false 0)) r.reg_regs print_reg_name r

and print_reg fmt r = fprintf fmt "%a%a%a@ %a" print_its r.reg_its
  (print_args (print_ity_node isb_empty false 2)) r.reg_args
  (print_regs (print_ity_node isb_empty false 0)) r.reg_regs print_reg_name r

let print_ity_full fmt ity = print_ity_node isb_empty false 0 fmt ity

let print_pv fmt v = print_vs fmt v.pv_vs

let print_pvty fmt v = fprintf fmt "@[(%s%a%a:@,%a)@]"
  (if v.pv_ghost then "ghost " else "")
  print_pv v print_id_labels v.pv_vs.vs_name
  print_ity v.pv_ity

let forget_pv v = forget_var v.pv_vs

let print_xs fmt xs = pp_print_string fmt (id_unique xprinter xs.xs_name)

exception FoundPrefix of pvsymbol list

let unknown = create_pvsymbol (id_fresh "?") ity_unit

let print_spec args pre post xpost oldies eff fmt ity =
  let dot fmt () = pp_print_char fmt '.' in
  let print_pfx reg fmt pfx = fprintf fmt "@[%a:@,%a@]"
    (Pp.print_list dot print_pv) pfx print_reg reg in
  let rec find_prefix pfx reg ity = match ity.ity_node with
    | Ityreg r when reg_equal reg r -> raise (FoundPrefix pfx)
    | Ityreg r when reg_r_reachable reg r ->
        let sbs = its_match_regs r.reg_its r.reg_args r.reg_regs in
        List.iter (fun fd -> let ity = ity_full_inst sbs fd.pv_ity in
          find_prefix (fd::pfx) reg ity) r.reg_its.its_mfields;
        raise (FoundPrefix (unknown::pfx))
    | _ when ity_r_reachable reg ity ->
        raise (FoundPrefix (unknown::pfx))
    | _ -> () in
  let find_prefix reg = try
    List.iter (fun v -> find_prefix [v] reg v.pv_ity) args;
    Spv.iter (fun v -> find_prefix [v] reg v.pv_ity) eff.eff_reads;
    [unknown] with FoundPrefix pfx -> List.rev pfx in
  let print_write fmt (reg,fds) =
    let pfx = find_prefix reg in
    let print_fld fmt {pv_vs = {vs_name = id}} =
      fprintf fmt "(%a).%s" (print_pfx reg) pfx id.id_string in
    if Spv.is_empty fds then print_pfx reg fmt pfx else
      Pp.print_list Pp.comma print_fld fmt (Spv.elements fds) in
  let print_region fmt reg = print_pfx reg fmt (find_prefix reg) in
  let print_result fmt ity = fprintf fmt " :@ %a" print_ity ity in
  let print_pre fmt p = fprintf fmt "@\nrequires { @[%a@] }" print_term p in
  let print_old fmt (o,v) =
    fprintf fmt "@\nold { %a -> %a }" print_pv o print_pv v in
  let print_post fmt q =
    let v, q = open_post q in
    fprintf str_formatter "%a" print_vs v;
    let n = flush_str_formatter () in
    if n = "result" || t_v_occurs v q = 0 then
      fprintf fmt "@\nensures  { @[%a@] }" print_term q else
      fprintf fmt "@\nreturns  { %s ->@ @[%a@] }" n print_term q;
    forget_var v in
  let print_xpost xs fmt q =
    let v, q = open_post q in
    fprintf fmt "@\nraises   { %a%a ->@ @[%a@] }" print_xs xs
      (fun fmt v -> if not (ty_equal v.vs_ty ty_unit && t_v_occurs v q = 0)
        then fprintf fmt " %a" print_vs v) v print_term q;
    forget_var v in
  let print_xpost fmt (xs,ql) =
    Pp.print_list Pp.nothing (print_xpost xs) fmt ql in
  Pp.print_list_pre Pp.space print_pvty fmt args;
  Pp.print_option print_result fmt ity;
  if eff.eff_oneway then pp_print_string fmt " diverges";
  let reads = List.fold_right Spv.remove args eff.eff_reads in
  if not (Spv.is_empty reads) then fprintf fmt "@\nreads  { %a }"
    (Pp.print_list Pp.comma print_pv) (Spv.elements reads);
  if not (Mreg.is_empty eff.eff_writes) then fprintf fmt "@\nwrites { %a }"
    (Pp.print_list Pp.comma print_write) (Mreg.bindings eff.eff_writes);
  if not (Mreg.is_empty eff.eff_covers) then fprintf fmt "@\ncovers { %a }"
    (Pp.print_list Pp.comma print_region) (Sreg.elements eff.eff_covers);
  if not (Mreg.is_empty eff.eff_resets) then fprintf fmt "@\nresets { %a }"
    (Pp.print_list Pp.comma print_region) (Sreg.elements eff.eff_resets);
  Pp.print_list Pp.nothing print_pre fmt pre;
  Pp.print_list Pp.nothing print_old fmt (Mpv.bindings oldies);
  Pp.print_list Pp.nothing print_post fmt post;
  Pp.print_list Pp.nothing print_xpost fmt (Mexn.bindings xpost)

let print_cty fmt c = print_spec c.cty_args c.cty_pre c.cty_post
  c.cty_xpost c.cty_oldies c.cty_effect fmt (Some c.cty_result)

let forget_cty c =
  List.iter forget_pv c.cty_args;
  Mpv.iter (fun v _ -> forget_pv v) c.cty_oldies

(** exception handling *)

let () = Exn_printer.register (fun fmt e -> match e with
  | NonUpdatable (s,ity) -> fprintf fmt
      "Type symbol %a cannot take mutable type %a \
        as an argument in this position" print_its s print_ity ity
  | BadItyArity ({its_ts = {ts_args = []}} as s, _) -> fprintf fmt
      "Type symbol %a expects no arguments" print_its s
  | BadItyArity (s, app_arg) ->
      let i = List.length s.its_ts.ts_args in fprintf fmt
      "Type symbol %a expects %i argument%s but is applied to %i"
        print_its s i (if i = 1 then "" else "s") app_arg
  | BadRegArity (s, app_arg) ->
      let i = List.length s.its_regions in fprintf fmt
      "Type symbol %a expects %i region argument%s but is applied to %i"
        print_its s i (if i = 1 then "" else "s") app_arg
  | DuplicateRegion r -> fprintf fmt
      "Region %a is used twice" print_reg r
  | UnboundRegion r -> fprintf fmt
      "Unbound region %a" print_reg r
  | ImpureType (v,ity) -> fprintf fmt
      "Cannot instantiate pure type variable %a with type %a"
        print_tv v print_ity ity
  | ImpureField ity -> fprintf fmt
      "Field type %a is mutable, it cannot be used in a type which is \
        private, recursive, or has an invariant" print_ity ity
(*
  | UnboundException xs -> fprintf fmt
      "This function raises %a but does not specify a post-condition for it"
        print_xs xs
*)
  | TypeMismatch (t1,t2,s) -> fprintf fmt
      "Type mismatch between %a and %a"
        (print_ity_node s false 0) t1 print_ity_full t2
  | StaleVariable (v, _r) -> fprintf fmt
      "This expression prohibits further usage of the variable %a \
        or any function that depends on it" print_pv v
  | BadGhostWrite (v, _r) -> fprintf fmt
      "This expression makes a ghost modification in the non-ghost variable %a"
        print_pv v
  | AssignPrivate r -> fprintf fmt
      "This assignment modifies a value of the private type %a" print_reg r
(*
  | WriteImmutable (r, v) -> fprintf fmt
      "In the type constructor %a, the field %s is immutable"
        print_its r.reg_its v.pv_vs.vs_name.id_string
*)
  | DuplicateField (_r, v) -> fprintf fmt
      "In this assignment, the field %s is modified twice"
        v.pv_vs.vs_name.id_string
  | GhostDivergence -> fprintf fmt
      "This ghost expression may not terminate"
  | IllegalSnapshot t -> fprintf fmt
      "This application expects a mutable type but receives %a"
        print_ity t
  | IllegalAlias _reg -> fprintf fmt
      "This application creates an illegal alias"
  | IllegalAssign (r1,r2,r3) -> fprintf fmt
      "This assignment mismatches regions (%a: %a - %a)"
        print_reg r1 print_reg r2 print_reg r3
  | _ -> raise e)
