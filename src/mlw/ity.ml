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

(** {2 Individual types (first-order types without effects)} *)

type itysymbol = {
  its_ts      : tysymbol;       (** logical type symbol *)
  its_nonfree : bool;           (** has no constructors *)
  its_private : bool;           (** private type *)
  its_mutable : bool;           (** mutable type *)
  its_fragile : bool;           (** breakable invariant *)
  its_mfields : pvsymbol list;  (** mutable record fields *)
  its_regions : region list;    (** shareable components *)
  its_arg_flg : its_flag list;  (** flags for type args *)
  its_reg_flg : its_flag list;  (** flags for regions *)
  its_def     : ity type_def;   (** type definition *)
}

and its_flag = {
  its_frozen  : bool;   (** cannot be updated *)
  its_exposed : bool;   (** directly reachable from a field *)
  its_liable  : bool;   (** exposed in the type invariant *)
  its_fixed   : bool;   (** exposed in a non-mutable field *)
  its_visible : bool;   (** visible from the non-ghost code *)
}

and ity = {
  ity_node : ity_node;
  ity_pure : bool;
  ity_tag  : Weakhtbl.tag;
}

and ity_node =
  | Ityreg of region
    (** record with mutable fields and shareable components *)
  | Ityapp of itysymbol * ity list * ity list
    (** immutable type with shareable components *)
  | Ityvar of tvsymbol
    (** type variable *)

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

module Hsity = Hashcons.Make (struct
  type t = ity

  let equal ity1 ity2 = match ity1.ity_node, ity2.ity_node with
    | Ityvar v1, Ityvar v2 -> tv_equal v1 v2
    | Ityreg r1, Ityreg r2 -> reg_equal r1 r2
    | Ityapp (s1,l1,r1), Ityapp (s2,l2,r2) ->
        its_equal s1 s2 &&
        List.for_all2 ity_equal l1 l2 &&
        List.for_all2 ity_equal r1 r2
    | _ -> false

  let hash ity = match ity.ity_node with
    | Ityvar v -> tv_hash v
    | Ityreg r -> reg_hash r
    | Ityapp (s,tl,rl) ->
        Hashcons.combine_list ity_hash
          (Hashcons.combine_list ity_hash (its_hash s) tl) rl

  let pure ity = match ity.ity_node with
    | Ityvar _ -> true
    | Ityreg _ -> false
    | Ityapp (_,tl,rl) ->
        let pure ity = ity.ity_pure in
        List.for_all pure tl && List.for_all pure rl

  let tag n ity = { ity with
    ity_pure = pure ity;
    ity_tag = Weakhtbl.create_tag n }
end)

let mk_ity node = {
  ity_node = node;
  ity_pure = true;
  ity_tag  = Weakhtbl.dummy_tag;
}

let mk_reg name s tl rl = {
  reg_name = id_register name;
  reg_its  = s;
  reg_args = tl;
  reg_regs = rl;
}

let ity_reg r              = Hsity.hashcons (mk_ity (Ityreg r))
let ity_var v              = Hsity.hashcons (mk_ity (Ityvar v))
let ity_app_unsafe s tl rl = Hsity.hashcons (mk_ity (Ityapp (s,tl,rl)))

(* purity *)

let its_pure s = not s.its_mutable && s.its_regions = []

let rec ity_purify ity = match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl} | Ityapp (s,tl,rl) ->
      ity_app_unsafe s (List.map ity_purify tl) (List.map ity_purify rl)
  | Ityvar _ -> ity

let rec ty_of_ity ity = match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl} | Ityapp (s,tl,_) ->
      ty_app s.its_ts (List.map ty_of_ity tl)
  | Ityvar v -> ty_var v

(* generic traversal functions *)

let dfold fn acc tl rl =
  List.fold_left fn (List.fold_left fn acc tl) rl

let dfold2 fn acc tl1 tl2 rl1 rl2 =
  List.fold_left2 fn (List.fold_left2 fn acc tl1 tl2) rl1 rl2

let its_arg_fold fn acc s tl =
  List.fold_left2 fn acc s.its_arg_flg tl

let its_reg_fold fn acc s rl =
  List.fold_left2 fn acc s.its_reg_flg rl

let its_fold fn acc s tl rl =
  its_reg_fold fn (its_arg_fold fn acc s tl) s rl

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
  | Ityvar v -> fn acc v

let reg_v_fold fn acc r = List.fold_left (ity_v_fold fn) acc r.reg_args

let ity_freevars s ity = ity_v_fold Stv.add_left s ity
let reg_freevars s reg = reg_v_fold Stv.add_left s reg

let ity_v_occurs v ity = Util.any ity_v_fold (tv_equal v) ity
let reg_v_occurs v reg = Util.any reg_v_fold (tv_equal v) reg

let ity_closed ity = Util.all ity_v_fold Util.ffalse ity

(* traversal functions on top regions *)

let rec ity_r_fold fn acc ity =
  if ity.ity_pure then acc else
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
  if ity.ity_pure then acc else
  match ity.ity_node with
  | Ityapp (s,tl,rl) -> its_exp_fold fn acc s tl rl
  | Ityreg r -> fn acc r
  | Ityvar _ -> acc

and its_exp_fold fn acc s tl rl =
  let fn a x t = if x.its_exposed then ity_exp_fold fn a t else a in
  its_fold fn acc s tl rl

let reg_exp_fold fn acc reg =
  its_exp_fold fn acc reg.reg_its reg.reg_args reg.reg_regs

let ity_exp_regs regs ity = ity_exp_fold Sreg.add_left regs ity

let rec reg_rch_regs s reg = reg_exp_fold reg_rch_regs (Sreg.add reg s) reg
let     ity_rch_regs s ity = ity_exp_fold reg_rch_regs s ity

let rec reg_rch_fold fn a reg = reg_exp_fold (reg_rch_fold fn) (fn a reg) reg
let     ity_rch_fold fn a ity = ity_exp_fold (reg_rch_fold fn) a ity

let reg_r_reachable r reg = Util.any reg_rch_fold (reg_equal r) reg
let ity_r_reachable r ity = Util.any ity_rch_fold (reg_equal r) ity

let rec reg_unc_fold cv fn a r = if Sreg.mem r cv then a else
                                 reg_exp_fold (reg_unc_fold cv fn) (fn a r) r
let     ity_unc_fold cv fn a t = ity_exp_fold (reg_unc_fold cv fn) a t

let reg_r_stale rs cv reg = Util.any (reg_unc_fold cv) (Sreg.contains rs) reg
let ity_r_stale rs cv ity = Util.any (ity_unc_fold cv) (Sreg.contains rs) ity

(* collect exposed and reachable type variables *)

let rec ity_exp_vars vars ity = match ity.ity_node with
  | Ityapp (s,tl,rl) ->
      let fn a x t = if x.its_exposed then ity_exp_vars a t else a in
      its_fold fn vars s tl rl
  | Ityvar v -> Stv.add v vars
  | Ityreg _ -> vars

let rec ity_rch_vars vars ity = match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl}
  | Ityapp (s,tl,rl) ->
      let fn a x t = if x.its_exposed then ity_rch_vars a t else a in
      its_fold fn vars s tl rl
  | Ityvar v -> Stv.add v vars

(* traversal functions on non-updatable regions *)

let fold_on_frz fn_frz fn_rch acc ity = match ity.ity_node with
  | Ityapp (s,_,_) when s.its_nonfree && s.its_mutable ->
      fn_rch acc ity
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl}
  | Ityapp (s,tl,rl) ->
      let fn a f t = if not f.its_exposed then a else
        if f.its_frozen then fn_rch a t else fn_frz a t in
      its_fold fn acc s tl rl
  | Ityvar _ -> acc

let rec ity_frz_vars vars ity =
  fold_on_frz ity_frz_vars ity_rch_vars vars ity

let rec ity_frz_regs regs ity =
  if ity.ity_pure then regs else
  fold_on_frz ity_frz_regs ity_rch_regs regs ity

let rec ity_frz_fold fn acc ity =
  if ity.ity_pure then acc else
  fold_on_frz (ity_frz_fold fn) (ity_rch_fold fn) acc ity

let ity_r_frozen s ity =
  Util.any ity_frz_fold (Mreg.contains s) ity

(** detect fragile types *)

let rec ity_fragile liquid_vars liable () ity =
  match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl}
  | Ityapp (s,tl,rl) ->
      (* can we be broken? *)
      if s.its_fragile then raise Exit else
      (* can we break an outer invariant? *)
      if liable && s.its_mutable then raise Exit else
      (* can we have broken reachable components? *)
      if s.its_nonfree && not s.its_mutable then () else
      (* reachable frozen components cannot be broken *)
      let fn () x t =
        if x.its_exposed && not x.its_frozen then
          ity_fragile liquid_vars (liable || x.its_liable) () t in
      its_fold fn () s tl rl
  | Ityvar _ ->
      if liable && liquid_vars then raise Exit

let ity_liquid liquid_vars ity =
  try ity_fragile liquid_vars true () ity; false with Exit -> true

let ity_fragile liquid_vars ity =
  try ity_fragile liquid_vars false () ity; false with Exit -> true

(* traversal functions on non-ghost regions *)

let rec ity_vis_fold fn acc ity =
  if ity.ity_pure then acc else
  match ity.ity_node with
  | Ityapp (s,tl,rl) -> its_vis_fold fn acc s tl rl
  | Ityreg r -> reg_vis_fold fn acc r
  | Ityvar _ -> acc

and its_vis_fold fn acc s tl rl =
  let fn a v t = if v.its_visible then ity_vis_fold fn a t else a in
  its_fold fn acc s tl rl

and reg_vis_fold fn acc reg =
  its_vis_fold fn (fn acc reg) reg.reg_its reg.reg_args reg.reg_regs

let ity_vis_regs regs ity = ity_vis_fold Sreg.add_left regs ity

(* collect non-ghost type variables *)

let rec ity_vis_vars vars ity = match ity.ity_node with
  | Ityreg {reg_its = s; reg_args = tl} | Ityapp (s,tl,_) ->
      let fn a v t = if v.its_visible then ity_vis_vars a t else a in
      its_arg_fold fn vars s tl
  | Ityvar v -> Stv.add v vars

(* type matching *)

exception BadItyArity of itysymbol * int
exception BadRegArity of itysymbol * int

exception DuplicateRegion of region
exception UnboundRegion of region

type ity_subst = {
  isb_var : ity Mtv.t;
  isb_reg : ity Mreg.t;
}

let isb_empty = {
  isb_var = Mtv.empty;
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
    | Ityvar v -> Mtv.find v sbs.isb_var in
  if ity.ity_pure && ity_closed ity then ity else inst ity

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
  | Ityvar v1, _ ->
      { sbs with isb_var = Mtv.change set v1 sbs.isb_var }
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
  | Alias { ity_node = Ityreg r } ->
      let tl = List.map (ity_full_inst sbs) r.reg_args in
      let rl = List.map (ity_full_inst sbs) r.reg_regs in
      ity_reg (mk_reg id r.reg_its tl rl)
  | NoDef when s.its_mutable ->
      ity_reg (mk_reg id s tl rl)
  | Alias ity -> ity_full_inst sbs ity
  | NoDef -> ity_app_unsafe s tl rl
  | Range _ -> ity_app_unsafe s tl rl
  | Float _ -> ity_app_unsafe s tl rl

let create_region_raw sbs id s tl rl =
  match (ity_app_raw sbs id s tl rl).ity_node with
  | Ityreg r -> r
  | _ -> invalid_arg "Ity.create_region"

let ity_app_pure_raw sbs s tl rl = match s.its_def with
  | Alias { ity_node = Ityreg r } ->
      let tl = List.map (ity_full_inst sbs) r.reg_args in
      let rl = List.map (ity_full_inst sbs) r.reg_regs in
      ity_app_unsafe r.reg_its tl rl
  | Alias ity -> ity_full_inst sbs ity
  | NoDef -> ity_app_unsafe s tl rl
  | Range _ -> assert (tl = [] && rl = []); ity_app_unsafe s tl rl
  | Float _ -> assert (tl = [] && rl = []); ity_app_unsafe s tl rl

(* smart type constructors *)

let its_check_args s tl =
  if List.length s.its_ts.ts_args <> List.length tl
  then raise (BadItyArity (s, List.length tl))

let its_match_args s tl =
  try {
    isb_var = List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty;
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
    | Ityvar v ->
        sbs, Mtv.find v sbs.isb_var
  and reg_inst sbs r =
    try sbs, Mreg.find r sbs.isb_reg with Not_found ->
    let sbs, tl = Lists.map_fold_left ity_inst sbs r.reg_args in
    let sbs, rl = Lists.map_fold_left ity_inst sbs r.reg_regs in
    let ity = fresh_reg (id_clone r.reg_name) r.reg_its tl rl in
    { sbs with isb_reg = Mreg.add r ity sbs.isb_reg }, ity in
  Lists.map_fold_left reg_inst (its_match_args s tl) s.its_regions

let its_match_smart fresh_reg s tl rl =
  if rl <> [] then its_match_regs s tl rl, rl else
  if s.its_regions = [] && s.its_def = NoDef
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

let mk_its, restore_its =
  let ts_to_its = Wts.create 17 in
  (fun ~ts ~nfr ~priv ~mut ~frg ~mfld ~regs ~aflg ~rflg ~def ->
    let its = {
      its_ts      = ts;
      its_nonfree = nfr;
      its_private = priv;
      its_mutable = mut;
      its_fragile = frg;
      its_mfields = mfld;
      its_regions = regs;
      its_arg_flg = aflg;
      its_reg_flg = rflg;
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
  | Tyvar v -> ity_var v
  | Tyapp (s,tl) ->
      let s = try restore_its s with Not_found ->
        invalid_arg "Ity.ity_of_ty_pure" in
      ity_app_pure s (List.map ity_of_ty_pure tl) []

let mk_flg ~frz ~exp ~lbl ~fxd ~vis = {
  its_frozen = frz; its_exposed = exp; its_liable = lbl;
  its_fixed  = fxd; its_visible = vis }

let its_of_ts ts priv =
  assert (ts.ts_def = NoDef);
  let flg = mk_flg ~frz:priv ~exp:true ~lbl:priv ~fxd:true ~vis:true in
  mk_its ~ts ~nfr:priv ~priv ~mut:false ~frg:false ~mfld:[] ~regs:[]
    ~aflg:(List.map (fun _ -> flg) ts.ts_args) ~rflg:[] ~def:NoDef

let create_rec_itysymbol id args =
  let ts = create_tysymbol id args NoDef in
  let flg = mk_flg ~frz:true ~exp:true ~lbl:false ~fxd:true ~vis:true in
  mk_its ~ts ~nfr:false ~priv:false ~mut:false ~frg:false ~mfld:[] ~regs:[]
    ~aflg:(List.map (fun _ -> flg) ts.ts_args) ~rflg:[] ~def:NoDef

let create_alias_itysymbol id args def =
  let ts = create_tysymbol id args (Alias (ty_of_ity def)) in
  let mut, ity = match def.ity_node with (* ignore the top region *)
    | Ityreg r -> true, ity_app_pure r.reg_its r.reg_args r.reg_regs
    | _ -> false, def in
  let regs = Sreg.elements (ity_top_regs Sreg.empty ity) in
  let flg = mk_flg ~frz:true ~exp:true ~lbl:false ~fxd:true ~vis:true in
  mk_its ~ts ~nfr:false ~priv:false ~mut ~frg:false ~mfld:[] ~regs
    ~aflg:(List.map (fun _ -> flg) args)
    ~rflg:(List.map (fun _ -> flg) regs) ~def:(Alias def)

let create_range_itysymbol id ir =
  let ts = create_tysymbol id [] (Range ir) in
  mk_its ~ts ~nfr:false ~priv:false ~mut:false ~frg:false ~mfld:[] ~regs:[]
    ~aflg:[] ~rflg:[] ~def:(Range ir)

let create_float_itysymbol id fp =
  let ts = create_tysymbol id [] (Float fp) in
  mk_its ~ts ~nfr:false ~priv:false ~mut:false ~frg:false ~mfld:[] ~regs:[]
    ~aflg:[] ~rflg:[] ~def:(Float fp)

let fields_of_invariant ftv flds invl =
  if invl = [] then Mpv.empty, flds else
  let fvs = Mpv.fold (fun v _ s -> Svs.add v.pv_vs s) flds Svs.empty in
  let check_invariant acc p =
    let ivs = t_freevars Mvs.empty p in
    let itv = t_ty_freevars Stv.empty p in
    if not (Mvs.set_submap ivs fvs) then Loc.error ?loc:p.t_loc
      (Decl.UnboundVar (fst (Mvs.choose (Mvs.set_diff ivs fvs))));
    if not (Stv.subset itv ftv) then Loc.error ?loc:p.t_loc
      (Ty.UnboundTypeVar (Stv.choose (Stv.diff itv ftv)));
    Mvs.set_union acc ivs in
  let fvs = List.fold_left check_invariant Mvs.empty invl in
  Mpv.partition (fun v _ -> Mvs.mem v.pv_vs fvs) flds

(*  private immutable:
      all arguments are frozen, exposed, liable, fixed, visible
      all reachable regions are frozen, otherwise we lose unicity [!]
      rexp, rlbl, rfxd, rvis are computed from the known fields
        => known regions cannot appear in the added fields
           in a refining type (no field aliases)
      cannot have its own invariant broken
      commits fields on construction and freezes them
        => not fragile and cannot have broken components

    private mutable:
      all arguments are frozen, exposed, liable, fixed, visible
      all regions frozen in the fields or reachable from
        the invariant are frozen, the rest are mutable
        => mutable regions cannot appear in the strengthened
           invariant in a refining type
      rexp, rlbl, rfxd, rvis are computed from the known fields
        => known regions cannot appear in the added fields
           in a refining type (no field aliases)
      cannot have its own invariant broken
      commits fields on construction and freezes the liable fields
      cannot have broken type parameters or broken liable fields
      however, a mutable region can break a non-liable field
        => not fragile, but can have fragile non-liable fields

    nonfree immutable:
      all reachable arguments are frozen, otherwise we lose unicity
      all reachable regions are frozen, otherwise we lose unicity [!]
      aexp, albl, afxd, avis are computed from the known fields
      rexp, rlbl, rfxd, rvis are computed from the known fields
      cannot have its own invariant broken
      commits fields on construction and freezes them
        => not fragile and cannot have broken components

    nonfree mutable:
      afrz, aexp, albl, afxd, avis are computed from the known fields
      rfrz, rexp, rlbl, rfxd, rvis are computed from the known fields
      commits fields on construction but does not freeze them
      can be broken from a liable reachable non-frozen component
      can have broken compontents (reachable and non-frozen)
        => fragile if has a liable mutable/liquid field
      can have a mutable fragile snapshot field, undetectable
        from type parameters or regions, breakable by assignment
        => fragile if has a non-liable mutable fragile field

    free mutable, free immutable non-recursive:
      afrz, aexp, albl, afxd, avis are computed from the known fields
      rfrz, rexp, rlbl, rfxd, rvis are computed from the known fields
      does not have a proper invariant
      does not commit fields on construction, and can have a broken
        snapshot field, undetectable from type parameters or regions
        => fragile if has a fragile field
      can have broken compontents (reachable and non-frozen)

    recursive (free, immutable, no known fields, no regions):
      all arguments are frozen, exposed, non-liable, fixed, visible
      commits fields on construction and freezes them
        => not fragile and cannot have broken components
        (can treat it as free immutable, since all paths are frozen)

  [!] if this rule makes an exposed region frozen, we declare
      the type mutable to preserve mutability. *)

let create_plain_record_itysymbol ~priv ~mut id args flds invl =
  let sargs = Stv.of_list args in
  let ts = create_tysymbol id args NoDef in
  let fmut, ffix = Mpv.partition (fun _ m -> m) flds in
  let flbl, fout = fields_of_invariant sargs flds invl in
  let fvis = if priv then flds else
    Mpv.filter (fun f _ -> not f.pv_ghost) flds in
  let collect fn = Mpv.fold (fun f _ a -> fn a f.pv_ity) in
  let dargs = collect ity_freevars flds Stv.empty in
  if not (Stv.subset dargs sargs) then raise
    (Ty.UnboundTypeVar (Stv.choose (Stv.diff dargs sargs)));
  let rfrz = if priv (* [!] compute rfrz ignoring mut *)
        then collect ity_rch_regs flbl
            (collect ity_frz_regs fout Sreg.empty)
        else collect ity_frz_regs flds Sreg.empty in
  let rexp = collect ity_exp_regs flds Sreg.empty in
  let rlbl = collect ity_exp_regs flbl Sreg.empty in
  let rfxd = collect ity_exp_regs ffix Sreg.empty in
  let rvis = collect ity_vis_regs fvis Sreg.empty in
  let rtop = collect ity_top_regs flds Sreg.empty in
  let regs = Mreg.keys rtop in
  let nfr = priv || invl <> [] in
  let mut = mut || not (Mpv.is_empty fmut) || (* [!] *)
      (nfr && not (Sreg.subset rexp rfrz)) in
  let frg = if priv || (nfr && not mut) then false else
    if nfr && mut then (* non-free mutable *)
      Mpv.exists (fun f m -> m || ity_liquid true f.pv_ity) flbl ||
      Mpv.exists (fun f m -> m && ity_fragile true f.pv_ity) fout
    else (* free: can have undetectable broken fields *)
      Mpv.exists (fun f _ -> ity_fragile true f.pv_ity) flds in
  let afrz = if priv then sargs else if nfr && not mut
                                then collect ity_rch_vars flds Stv.empty
                                else collect ity_frz_vars flds Stv.empty in
  let aexp = if priv then sargs else collect ity_exp_vars flds Stv.empty in
  let albl = if priv then sargs else collect ity_exp_vars flbl Stv.empty in
  let afxd = if priv then sargs else collect ity_exp_vars ffix Stv.empty in
  let avis = if priv then sargs else collect ity_vis_vars fvis Stv.empty in
  let arg_flag v = mk_flg ~frz:(Stv.mem v afrz) ~exp:(Stv.mem v aexp)
    ~lbl:(Stv.mem v albl) ~fxd:(Stv.mem v afxd) ~vis:(Stv.mem v avis) in
  let reg_flag r = mk_flg  ~frz:(Sreg.mem r rfrz) ~exp:(Sreg.mem r rexp)
    ~lbl:(Sreg.mem r rlbl) ~fxd:(Sreg.mem r rfxd) ~vis:(Sreg.mem r rvis) in
  mk_its ~ts ~nfr ~priv ~mut ~frg ~mfld:(Mpv.keys fmut) ~regs ~def:NoDef
    ~aflg:(List.map arg_flag args) ~rflg:(List.map reg_flag regs)

let create_plain_variant_itysymbol id args flds =
  let flds = List.fold_left (fun acc flds ->
    Mpv.set_union acc (Mpv.map Util.ffalse flds)) Mpv.empty flds in
  create_plain_record_itysymbol ~priv:false ~mut:false id args flds []

let ity_fragile ity = ity_fragile false ity

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

type mask =
  | MaskVisible
  | MaskTuple of mask list
  | MaskGhost

let mask_of_pv v = if v.pv_ghost then MaskGhost else MaskVisible

let rec mask_reduce mask = match mask with
  | MaskVisible | MaskGhost -> mask
  | MaskTuple l ->
      let l = List.map mask_reduce l in
      if List.for_all ((=) MaskVisible) l then MaskVisible else
      if List.for_all ((=) MaskGhost) l then MaskGhost else
      MaskTuple l

let rec mask_check exn ity mask = match ity.ity_node, mask with
  | _, (MaskVisible | MaskGhost) -> ()
  | Ityapp ({its_ts = s},tl,_), MaskTuple l
    when is_ts_tuple s && List.length tl = List.length l ->
      List.iter2 (mask_check exn) tl l
  | _ -> raise exn

let rec mask_ghost = function
  | MaskVisible -> false
  | MaskTuple l -> List.exists mask_ghost l
  | MaskGhost   -> true

let rec mask_union mask1 mask2 = match mask1, mask2 with
  | MaskVisible, _ | _, MaskGhost -> mask2
  | _, MaskVisible | MaskGhost, _ -> mask1
  | MaskTuple l1, MaskTuple l2 -> MaskTuple (List.map2 mask_union l1 l2)

let mask_equal : mask -> mask -> bool = (=)

let rec mask_sub mask1 mask2 = match mask1, mask2 with
  | MaskVisible, _ | _, MaskGhost -> true
  | MaskGhost, _ -> mask_reduce mask2 = MaskGhost
  | _, MaskVisible -> mask_reduce mask1 = MaskVisible
  | MaskTuple l1, MaskTuple l2 -> Lists.equal mask_sub l1 l2

let mask_spill mask1 mask2 = not (mask_sub mask1 mask2)

type xsymbol = {
  xs_name : ident;
  xs_ity  : ity; (* closed and pure *)
  xs_mask : mask;
}

let xs_equal : xsymbol -> xsymbol -> bool = (==)
let xs_hash xs = id_hash xs.xs_name
let xs_compare xs1 xs2 = id_compare xs1.xs_name xs2.xs_name

let freeze_xs xs s = ity_freeze s xs.xs_ity

let create_xsymbol id ?(mask=MaskVisible) ity =
  mask_check (Invalid_argument "Ity.create_xsymbol") ity mask;
  let mask = if ity_equal ity ity_unit then MaskVisible else mask in
  { xs_name = id_register id; xs_ity = ity; xs_mask = mask_reduce mask }

module Exn = MakeMSH (struct
  type t = xsymbol
  let tag xs = Weakhtbl.tag_hash xs.xs_name.id_tag
end)

module Sxs = Exn.S
module Mxs = Exn.M

(* effects *)

exception IllegalSnapshot of ity
exception IllegalAlias of region
exception AssignPrivate of region
exception AssignSnapshot of ity
exception WriteImmutable of region * pvsymbol
exception IllegalUpdate of pvsymbol * region
exception StaleVariable of pvsymbol * region
exception BadGhostWrite of pvsymbol * region
exception DuplicateField of region * pvsymbol
exception IllegalAssign of region * region * region
exception ImpureVariable of tvsymbol * ity
exception GhostDivergence

(* termination status *)
type oneway =
  | Total
  | Partial
  | Diverges

let total status = (status = Total)
let partial status = (status = Partial)
let diverges status = (status = Diverges)

let oneway_union t1 t2 = match t1, t2 with
  | Total, Total -> Total
  | _, Diverges | Diverges, _ -> Diverges
  | _ -> Partial

type effect = {
  eff_reads  : Spv.t;         (* known variables *)
  eff_writes : Spv.t Mreg.t;  (* writes to fields *)
  eff_taints : Sreg.t;        (* ghost code writes *)
  eff_covers : Sreg.t;        (* surviving writes *)
  eff_resets : Sreg.t;        (* locked by covers *)
  eff_raises : Sxs.t;         (* raised exceptions *)
  eff_spoils : Stv.t;         (* immutable tyvars *)
  eff_oneway : oneway;        (* non-termination *)
  eff_ghost  : bool;          (* ghost status *)
}

let eff_empty = {
  eff_reads  = Spv.empty;
  eff_writes = Mreg.empty;
  eff_taints = Sreg.empty;
  eff_covers = Sreg.empty;
  eff_resets = Sreg.empty;
  eff_raises = Sxs.empty;
  eff_spoils = Stv.empty;
  eff_oneway = Total;
  eff_ghost  = false;
}

let eff_equal e1 e2 =
  Spv.equal e1.eff_reads e2.eff_reads &&
  Mreg.equal Spv.equal e1.eff_writes e2.eff_writes &&
  Sreg.equal e1.eff_taints e2.eff_taints &&
  Sreg.equal e1.eff_covers e2.eff_covers &&
  Sreg.equal e1.eff_resets e2.eff_resets &&
  Sxs.equal e1.eff_raises e2.eff_raises &&
  Stv.equal e1.eff_spoils e2.eff_spoils &&
  e1.eff_oneway = e2.eff_oneway &&
  e1.eff_ghost = e2.eff_ghost

let eff_pure e =
  Mreg.is_empty e.eff_writes &&
  Sxs.is_empty e.eff_raises &&
  total e.eff_oneway

let check_writes {eff_writes = wrt} pvs =
  if not (Mreg.is_empty wrt) then Spv.iter (fun v ->
    if ity_r_frozen wrt v.pv_ity then Mreg.iter (fun r _ ->
      if ity_r_frozen (Sreg.singleton r) v.pv_ity then
        raise (IllegalUpdate (v,r))) wrt) pvs

let check_covers {eff_resets = rst; eff_covers = cvr} pvs =
  if not (Sreg.is_empty rst) then Spv.iter (fun v ->
    if ity_r_stale rst cvr v.pv_ity then Sreg.iter (fun r ->
      if ity_r_stale (Sreg.singleton r) cvr v.pv_ity then
        raise (StaleVariable (v,r))) rst) pvs

let check_taints tnt pvs =
  if not (Sreg.is_empty tnt) then Spv.iter (fun v ->
    if not v.pv_ghost then ity_vis_fold (fun () r ->
      if Sreg.mem r tnt then raise (BadGhostWrite (v,r))) () v.pv_ity) pvs

let visible_writes e =
  Mreg.subdomain (fun {reg_its = {its_private = priv}} fs ->
    priv || Spv.exists (fun fd -> not fd.pv_ghost) fs) e.eff_writes

let reset_taints e =
  let vwr = visible_writes e in
  let filter v tnt = if v.pv_ghost then tnt else
    ity_vis_fold Sreg.remove_left tnt v.pv_ity in
  let tnt = if e.eff_ghost || Sreg.is_empty vwr then
    begin check_taints vwr e.eff_reads; vwr end else
    Spv.fold filter e.eff_reads vwr in
  { e with eff_taints = tnt }

let eff_ghostify gh e =
  if not gh || e.eff_ghost then e else
  if not (total e.eff_oneway) then raise GhostDivergence else
  reset_taints { e with eff_ghost = true }

let eff_ghostify_weak gh e =
  if not gh || e.eff_ghost then e else
  if not (total e.eff_oneway && Sxs.is_empty e.eff_raises) then e else
  if not (Sreg.equal e.eff_taints (visible_writes e)) then e else
  (* it is not enough to catch BadGhostWrite from eff_ghostify below,
     because e may not have in eff_reads the needed visible variables
     (e.g. if e is the effect of a match-with branch after eff_bind).
     Therefore, we check that all visible writes are already taints. *)
  eff_ghostify gh e

let eff_partial e =
  if diverges e.eff_oneway || partial e.eff_oneway then e else
  if e.eff_ghost then raise GhostDivergence else
  { e with eff_oneway = Partial }

let eff_diverge e =
  if diverges e.eff_oneway then e else
  if e.eff_ghost then raise GhostDivergence else
  { e with eff_oneway = Diverges }

let eff_read_pre rd e =
  if Spv.subset rd e.eff_reads then e else
  let () = check_taints e.eff_taints rd in
  { e with eff_reads = Spv.union e.eff_reads rd }

let eff_read_post e rd =
  check_writes e rd;
  check_covers e rd;
  eff_read_pre rd e

let eff_bind rd e = if Mpv.is_empty rd then e else
  { e with eff_reads = Mpv.set_diff e.eff_reads rd }

let eff_read rd =
  if Spv.is_empty rd then eff_empty else
  { eff_empty with eff_reads = rd }

let eff_read_single v = eff_read (Spv.singleton v)
let eff_read_single_pre v e = eff_read_pre (Spv.singleton v) e
let eff_read_single_post e v = eff_read_post e (Spv.singleton v)
let eff_bind_single v e = eff_bind (Spv.singleton v) e

let check_mutable_field r f =
  if not (List.memq f r.reg_its.its_mfields) then raise (WriteImmutable (r,f))

let read_regs rd =
  Spv.fold (fun v s -> ity_rch_regs s v.pv_ity) rd Sreg.empty

(*TODO? add the third arg (resets) and check the invariants *)
let eff_write rd wr =
  if Mreg.is_empty wr then eff_read rd else
  let kn = read_regs rd in
  let wr = Mreg.filter (fun ({reg_its = s} as r) fs ->
    if Spv.is_empty fs && not s.its_private then invalid_arg "Ity.eff_write";
    Spv.iter (check_mutable_field r) fs; Sreg.mem r kn) wr in
  reset_taints { eff_empty with
    eff_reads = rd; eff_writes = wr; eff_covers = Mreg.domain wr }

(*TODO: should we use it and what semantics to give? *)
let eff_reset ({eff_writes = wr} as e) rs =
  if not (Mreg.set_disjoint wr rs) then invalid_arg "Ity.eff_reset";
  { e with eff_resets = Sreg.union rs e.eff_resets }

let rec ity_skel_check t1 t2 =
  if not (ity_equal t1 t2) then
  match t1.ity_node, t2.ity_node with
  | Ityreg {reg_its = s1; reg_args = tl1; reg_regs = rl1},
    Ityreg {reg_its = s2; reg_args = tl2; reg_regs = rl2}
  | Ityapp (s1,tl1,rl1), Ityapp (s2,tl2,rl2)
    when its_equal s1 s2 ->
      List.iter2 ity_skel_check tl1 tl2;
      List.iter2 ity_skel_check rl1 rl2
  | _ -> raise (TypeMismatch (t1,t2,isb_empty))

let eff_assign asl =
  (* compute all effects except eff_resets *)
  let get_reg = function
    | {pv_ity = {ity_node = Ityreg r}} -> r
    | v -> raise (AssignSnapshot v.pv_ity) in
  let writes = List.fold_left (fun wr (r,f,v) ->
    let r = get_reg r and ity = v.pv_ity in
    check_mutable_field r f;
    if r.reg_its.its_private then raise (AssignPrivate r);
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
    let fixed xl f t = if f.its_fixed then ity_rexp xl t else xl in
    its_fold fixed xl s tl rl in
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
  let effect = {
    eff_reads  = reads;
    eff_writes = Mreg.map Mpv.domain writes;
    eff_taints = taint;
    eff_covers = Mreg.domain (Mreg.set_diff writes resets);
    eff_resets = resets;
    eff_raises = Sxs.empty;
    eff_spoils = Stv.empty;
    eff_oneway = Total;
    eff_ghost  = ghost } in
  (* verify that we can rebuild every value *)
  check_writes effect reads;
  effect

let eff_reset_overwritten ({eff_writes = wr} as e) =
  if not (Sreg.is_empty e.eff_resets) then
    invalid_arg "Ity.eff_reset_overwritten";
  let rec reg2 regs reg =
    if Mreg.mem reg wr then regs else
    reg_exp_fold reg2 (Sreg.add reg regs) reg in
  let ity2 regs ity = ity_exp_fold reg2 regs ity in
  let add_write ({reg_its = s} as r) fs (svv, rst) =
    let fixed svv f t = if f.its_fixed then ity2 svv t else svv in
    let svv = its_fold fixed (Sreg.add r svv) s r.reg_args r.reg_regs in
    let sbs = its_match_regs s r.reg_args r.reg_regs in
    let add_mfld (svv,rst) f =
      let t = ity_full_inst sbs f.pv_ity in
      if Spv.mem f fs then svv, ity2 rst t else ity2 svv t, rst in
    List.fold_left add_mfld (svv,rst) s.its_mfields in
  let svv, rst = Mreg.fold add_write wr (Sreg.empty,Sreg.empty) in
  { e with eff_resets = Sreg.diff rst svv }

let eff_raise e x = { e with eff_raises = Sxs.add x e.eff_raises }
let eff_catch e x = { e with eff_raises = Sxs.remove x e.eff_raises }

let eff_spoil e t = { e with eff_spoils = ity_rch_vars e.eff_spoils t }

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
  eff_raises = Sxs.union e1.eff_raises e2.eff_raises;
  eff_spoils = Stv.union e1.eff_spoils e2.eff_spoils;
  eff_oneway = oneway_union e1.eff_oneway e2.eff_oneway;
  eff_ghost  = e1.eff_ghost && e2.eff_ghost }

let eff_union e1 e2 =
  check_taints e1.eff_taints e2.eff_reads;
  check_taints e2.eff_taints e1.eff_reads;
  eff_union e1 e2

(* TODO: remove later *)
let eff_union e1 e2 =
  let e = eff_union e1 e2 in
  assert (Sreg.disjoint e.eff_covers e.eff_resets);
  assert (Mreg.for_all (fun r _ -> reg_r_stale e.eff_resets e.eff_covers r)
            (Mreg.set_diff e.eff_writes e.eff_covers));
  e

let eff_contaminate e1 e2 =
  if not e1.eff_ghost then e2 else
  if Sxs.is_empty e1.eff_raises then e2 else
  eff_ghostify true e2

let eff_contaminate_weak e1 e2 =
  if not e1.eff_ghost then e2 else
  if Sxs.is_empty e1.eff_raises then eff_ghostify_weak true e2 else
  eff_ghostify true e2

let eff_union_par e1 e2 =
  eff_union (eff_contaminate_weak e2 e1) (eff_contaminate_weak e1 e2)

let eff_union_seq e1 e2 =
  check_writes e1 e2.eff_reads;
  check_covers e1 e2.eff_reads;
  eff_union (eff_contaminate_weak e2 e1) (eff_contaminate e1 e2)

(* NOTE: never export this function: it ignores eff_reads
   and eff_ghost, which are handled in cty_apply below. *)
let eff_inst sbs e =
  (* Immutable type variables can only be instantiated with pure types.
     All type variables in these types become immutable. *)
  let spoils = Mtv.fold (fun v i s -> if i.ity_pure then
      ity_rch_vars s i else raise (ImpureVariable (v,i)))
    (Mtv.set_inter sbs.isb_var e.eff_spoils) Stv.empty in
  (* All modified or stale regions in e must be instantiated into
     distinct regions. We allow regions that are not affected
     to be aliased, even if they contain modified subregions:
     the values are still updated at the same program points and
     with the same postconditions, as in the initial verified code.
     Every modified or stale region must be instantiated into a region,
     not a snapshot. Also, every region containing a modified or stale
     region, must also be instantiated into a region and not a snapshot.
     The latter is not necessary for soundness, but simplifies VCgen. *)
  let safe = remove_stale e (Mreg.set_diff sbs.isb_reg e.eff_covers) in
  let inst src = Mreg.fold (fun p v acc -> Mreg.fold (fun q t acc ->
    match t.ity_node with
    | Ityapp _ when reg_r_reachable p q -> raise (IllegalSnapshot t)
    | Ityreg r when reg_equal p q -> Mreg.add_new (IllegalAlias r) r v acc
    | _ -> acc) sbs.isb_reg acc) src Mreg.empty in
  let writes = inst e.eff_writes in
  let resets = inst e.eff_resets in
  let taints = inst e.eff_taints in
  let covers = inst e.eff_covers in
  let impact = inst (Mreg.set_diff sbs.isb_reg safe) in
  (* All type variables and unaffected regions must be instantiated
     outside [impact]. Every region in the instantiated execution
     is either brought in by the type substitution or instantiates
     one of the original regions. *)
  let dst = Mreg.fold (fun _ i s -> match i.ity_node with
    | Ityreg r -> Sreg.add r s | _ -> s) safe Sreg.empty in
  let dst = Mtv.fold (fun _ i s -> ity_rch_regs s i) sbs.isb_var dst in
  ignore (Mreg.inter (fun r _ _ -> raise (IllegalAlias r)) dst impact);
  { e with eff_writes = writes; eff_taints = taints;
           eff_covers = covers; eff_resets = resets;
           eff_spoils = spoils }

let mask_adjust eff ity mask =
  if eff.eff_ghost then MaskGhost else
  if ity_equal ity ity_unit then MaskVisible else mask

let eff_escape eff ity =
  let esc = Sity.singleton ity in
  let add_xs xs esc = Sity.add xs.xs_ity esc in
  let esc = Sxs.fold add_xs eff.eff_raises esc in
  let add_write r fs esc =
    let sbs = its_match_regs r.reg_its r.reg_args r.reg_regs in
    let add_fd f s = Sity.add (ity_full_inst sbs f.pv_ity) s in
    Spv.fold add_fd fs esc in
  Mreg.fold add_write eff.eff_writes esc

(* affected program variables by some writes effect *)

let ity_affected wr ity =
  Util.any ity_rch_fold (Mreg.contains wr) ity

let pv_affected wr v = ity_affected wr v.pv_ity

let pvs_affected wr pvs =
  if Mreg.is_empty wr then Spv.empty
  else Spv.filter (pv_affected wr) pvs

(** specification *)

type pre = term   (* precondition: pre_fmla *)
type post = term  (* postcondition: eps result . post_fmla *)

let create_post vs f = t_eps_close vs f

let open_post q = match q.t_node with
  | Teps bf -> t_open_bound bf
  | _ -> invalid_arg "Ity.open_post"

let open_post_with t q = match q.t_node with
  | Teps bf -> t_open_bound_with t bf
  | _ -> invalid_arg "Ity.open_post_with"

let clone_post_result q = match q.t_node with
  | Teps bf -> t_clone_bound_id bf
  | _ -> invalid_arg "Ity.clone_post_result"

let annot_attr = Ident.create_attribute "vc:annotation"
let break_attr = Ident.create_attribute "vc:break_me"

type cty = {
  cty_args   : pvsymbol list;
  cty_pre    : pre list;
  cty_post   : post list;
  cty_xpost  : post list Mxs.t;
  cty_oldies : pvsymbol Mpv.t;
  cty_effect : effect;
  cty_result : ity;
  cty_mask   : mask;
  cty_freeze : ity_subst;
}

let cty_unsafe args pre post xpost oldies effect result mask freeze = {
  cty_args   = args;
  cty_pre    = pre;
  cty_post   = post;
  cty_xpost  = xpost;
  cty_oldies = oldies;
  cty_effect = effect;
  cty_result = result;
  cty_mask   = mask_adjust effect result mask;
  cty_freeze = freeze;
}

let cty_reads c = c.cty_effect.eff_reads
let cty_ghost c = c.cty_effect.eff_ghost

let cty_pure {cty_args = args; cty_effect = eff} =
  eff_pure eff &&
  let pvs = List.fold_right Spv.add args eff.eff_reads in
  try check_covers eff pvs; true with StaleVariable _ -> false

let cty_ghostify gh ({cty_effect = eff} as c) =
  if not gh || eff.eff_ghost then c else
  { c with cty_effect = eff_ghostify gh eff; cty_mask = MaskGhost }

let spec_t_fold fn_t acc pre post xpost =
  let fn_l a fl = List.fold_left fn_t a fl in
  let acc = fn_l (fn_l acc pre) post in
  Mxs.fold (fun _ l a -> fn_l a l) xpost acc

let check_tvs reads raises result pre post xpost =
  (* each type variable in spec comes either from a known vsymbol
     or from the external exception, or from the result type.
     We need this to ensure that we can do a full instantiation.
     TODO: do we really need this? *)
  let add_pv v s = ity_freevars s v.pv_ity in
  let tvs = ity_freevars Stv.empty result in
  let tvs = Spv.fold add_pv reads tvs in
  let add_xs xs s = ity_freevars s xs.xs_ity in
  let tvs = Sxs.fold add_xs raises tvs in
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

let create_cty ?(mask=MaskVisible) ?(defensive=false)
               args pre post xpost oldies effect result =
  let exn = Invalid_argument "Ity.create_cty" in
  (* pre, post, and xpost are well-typed *)
  check_pre pre; check_post exn result post;
  Mxs.iter (fun xs xq -> check_post exn xs.xs_ity xq) xpost;
  (* mask is consistent with result *)
  mask_check exn result mask;
  let mask = mask_reduce mask in
  (* the arguments are pairwise distinct *)
  let sarg = List.fold_right (Spv.add_new exn) args Spv.empty in
  (* complete the reads and freeze the external context.
     oldies must be fresh: collisions with args and external
     reads are forbidden, to simplify instantiation later. *)
  Mpv.iter (fun {pv_ghost = gh; pv_ity = o} {pv_ity = t} ->
    if not (gh && o == ity_purify t) then raise exn) oldies;
  let preads = spec_t_fold t_freepvs sarg pre [] Mxs.empty in
  let qreads = spec_t_fold t_freepvs Spv.empty [] post xpost in
  let effect = eff_read_post effect qreads in
  let oldies = Mpv.set_inter oldies effect.eff_reads in
  let effect = eff_bind oldies effect in
  let preads = Mpv.fold (Util.const Spv.add) oldies preads in
  if not (Mpv.set_disjoint preads oldies) then raise exn;
  let effect = eff_read_pre preads effect in
  let xreads = Spv.diff effect.eff_reads sarg in
  let freeze = Spv.fold freeze_pv xreads isb_empty in
  let freeze = Sxs.fold freeze_xs effect.eff_raises freeze in
  check_tvs effect.eff_reads effect.eff_raises result pre post xpost;
  (* remove exceptions whose postcondition is False *)
  let is_false q = match open_post q with
    | _, {t_node = Tfalse} -> true | _ -> false in
  let filter _ () = function
    | [q] when is_false q -> None | _ -> Some () in
  let raises = Mxs.diff filter effect.eff_raises xpost in
  let effect = { effect with eff_raises = raises } in
  (* remove writes/taints invalidated by resets *)
  let effect = { effect with
    eff_writes = Mreg.set_inter effect.eff_writes effect.eff_covers;
    eff_taints = Mreg.set_inter effect.eff_taints effect.eff_covers} in
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
  let add_xs xs s = ity_rch_regs s xs.xs_ity in
  let vknown = Sxs.fold add_xs raises vknown in
  let effect = reset_taints { effect with
    eff_writes = Mreg.set_inter effect.eff_writes rknown;
    eff_covers = Mreg.set_inter effect.eff_covers rknown;
    eff_resets = Mreg.set_inter effect.eff_resets vknown} in
  (* only spoil the escaping type variables *)
  let escape = eff_escape effect result in
  let escape = Sity.fold_left ity_rch_vars Stv.empty escape in
  let spoils = Stv.inter effect.eff_spoils escape in
  let effect = { effect with eff_spoils = spoils } in
  (* be defensive in abstract function declarations *)
  let effect = if not defensive then effect else
    let resets = Mreg.set_diff vknown rknown in
    let resets = Mreg.set_union effect.eff_resets resets in
    { effect with eff_resets = resets; eff_spoils = escape } in
  (* remove the formal parameters from eff_reads *)
  let effect = { effect with eff_reads = xreads } in
  cty_unsafe args pre post xpost oldies effect result mask freeze

let create_cty_defensive = create_cty ~defensive:true
let create_cty           = create_cty ~defensive:false

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
  let eff = if same then c.cty_effect else eff_inst isb c.cty_effect in
  let eff = eff_read_pre (Spv.of_list vl) (eff_ghostify ghost eff) in
  (* stage 4: instantiate the specification *)
  let tsb = Mtv.map ty_of_ity isb.isb_var in
  let same = same || Mtv.for_all (fun v {ty_node = n} ->
    match n with Tyvar u -> tv_equal u v | _ -> false) tsb in
  let subst_t = if same then (fun t -> t_subst vsb t) else
                      (fun t -> t_ty_subst tsb vsb t) in
  let subst_l l = List.map subst_t l in
  cty_unsafe (List.rev rargs) (subst_l c.cty_pre)
    (subst_l c.cty_post) (Mxs.map subst_l c.cty_xpost)
    oldies eff res c.cty_mask freeze

let cty_tuple args =
  let ty = ty_tuple (List.map (fun v -> v.pv_vs.vs_ty) args) in
  let vs = create_vsymbol (id_fresh "result") ty in
  let tl = List.map (fun v -> t_var v.pv_vs) args in
  let post = create_post vs (t_equ (t_var vs) (t_tuple tl)) in
  let mask = mask_reduce (MaskTuple (List.map mask_of_pv args)) in
  let res = ity_tuple (List.map (fun v -> v.pv_ity) args) in
  let eff = eff_read (Spv.of_list args) in
  let eff = eff_ghostify (mask = MaskGhost) eff in
  let frz = List.fold_right freeze_pv args isb_empty in
  cty_unsafe [] [] [post] Mxs.empty Mpv.empty eff res mask frz

let cty_exec_post_raw c =
  let ity = List.fold_right (fun a ity ->
    ity_func a.pv_ity ity) c.cty_args c.cty_result in
  let al = List.map (fun a -> a.pv_vs) c.cty_args in
  let res = create_vsymbol (id_fresh "result") (ty_of_ity ity) in
  let res_al = t_func_app_l (t_var res) (List.map t_var al) in
  let oldies = Mpv.fold (fun {pv_vs = o} {pv_vs = v} s ->
    Mvs.add o (t_var v) s) c.cty_oldies Mvs.empty in
  let conv_post q =
    let v, h = open_post q in
    let rec down h s el vl = match el, vl with
      | {t_node = Tvar u}::el, v::vl when vs_equal u v ->
          down h s el vl
      | el, [] ->
          let tyl = List.map (fun v -> v.vs_ty) al in
          let ty = Opt.map (Util.const v.vs_ty) s.ls_value in
          t_equ (t_var res) (t_app_partial s (List.rev el) tyl ty)
      | _ -> t_subst_single v res_al h in
    let rec conv h = t_attr_copy h (match h.t_node with
      | Tapp (ps, [{t_node = Tvar u}; {t_node = Tapp(s, tl)} as t])
        when ls_equal ps ps_equ && vs_equal v u && t_v_occurs v t = 0 ->
          down h s (List.rev tl) (List.rev al)
      | Tbinop (Tiff, {t_node =
          Tapp (ps, [{t_node = Tvar u}; {t_node = Tapp (fs, [])}])},
          ({t_node = Tapp (s, tl)} as f))
        when ls_equal ps ps_equ && vs_equal v u &&
             ls_equal fs fs_bool_true && t_v_occurs v f = 0 ->
          down h s (List.rev tl) (List.rev al)
      | Tbinop (Tand, f, g) -> t_and (conv f) (conv g)
      | _ -> t_subst_single v res_al h) in
    conv (t_subst oldies h) in
  al, ity, res, List.map conv_post c.cty_post

let cty_exec_post c =
  if c.cty_args = [] then c.cty_post else
  let _, _, res, ql = cty_exec_post_raw c in
  List.map (create_post res) ql

let cty_exec ({cty_effect = eff} as c) =
  (* we do not purify the signature, so the regions will be frozen
     in the resulting pvsymbol. Thus, we have to forbid all effects,
     including allocation. TODO/FIXME: we should probably forbid
     the rest of the signature to contain regions at all. *)
  if diverges eff.eff_oneway then Loc.errorm
    "This function may not terminate, it cannot be used as pure";
  if partial eff.eff_oneway then Loc.errorm
    "This function may fail, it cannot be used as pure";
  if not (eff_pure eff && Sreg.is_empty eff.eff_resets) then Loc.errorm
    "This function has side effects, it cannot be used as pure";
  if not (Mreg.is_empty c.cty_freeze.isb_reg) then Loc.errorm
    "This function is stateful, it cannot be used as pure";
  let gh = List.exists (fun a -> a.pv_ghost) c.cty_args in
  let eff = eff_ghostify (gh || mask_ghost c.cty_mask) eff in
  (* translate the specification *)
  let al, ity, res, ql = cty_exec_post_raw c in
  let pre = List.map (t_forall_close_simp al []) c.cty_pre in
  let conv q = create_post res (t_forall_close_simp al [] q) in
  let post = List.map conv ql in
  (* we do not modify cty_freeze to respect the invariants of the cty type.
     It is sound to assume that the resulting cty can be executed multiple
     times, producing mappings with different type variables and regions.
     Still, Expr never uses it like this: it is merely attached to Eexec
     to provide the converted specification for VC generation. Pvsymbols
     that carry the resulting value, however, cannot be generalized. *)
  cty_unsafe [] pre post Mxs.empty Mpv.empty eff ity MaskVisible c.cty_freeze

let cty_exec c = if c.cty_args = [] then c else cty_exec c

let cty_read_pre pvs c =
  (* the external reads are already frozen and
     the arguments should stay instantiable *)
  let pvs = Spv.diff pvs c.cty_effect.eff_reads in
  let pvs = List.fold_right Spv.remove c.cty_args pvs in
  { c with cty_effect = eff_read_pre pvs c.cty_effect;
           cty_freeze = Spv.fold freeze_pv pvs c.cty_freeze }

let cty_read_post c pvs =
  check_writes c.cty_effect pvs;
  check_covers c.cty_effect pvs;
  cty_read_pre (Mpv.set_diff pvs c.cty_oldies) c

let cty_add_pre pre c = if pre = [] then c else begin check_pre pre;
  let c = cty_read_pre (List.fold_left t_freepvs Spv.empty pre) c in
  let rd = List.fold_right Spv.add c.cty_args c.cty_effect.eff_reads in
  check_tvs rd c.cty_effect.eff_raises c.cty_result pre [] Mxs.empty;
  { c with cty_pre = pre @ c.cty_pre } end

let cty_add_post c post = if post = [] then c else begin
  check_post (Invalid_argument "Ity.cty_add_post") c.cty_result post;
  let c = cty_read_post c (List.fold_left t_freepvs Spv.empty post) in
  let rd = List.fold_right Spv.add c.cty_args c.cty_effect.eff_reads in
  check_tvs rd c.cty_effect.eff_raises c.cty_result [] post Mxs.empty;
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
  | Ityvar v -> print_tv fmt v
  | Ityapp (s,[t1;t2],[]) when its_equal s its_func ->
      fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_ity pur 1) t1 (print_ity pur 0) t2
  | Ityapp (s,tl,[]) when is_ts_tuple s.its_ts ->
      fprintf fmt "(%a)" (Pp.print_list Pp.comma (print_ity pur 0)) tl
  | Ityapp (s,tl,_) when not pur && s.its_mutable && ity.ity_pure ->
      fprintf fmt "{%a%a}" print_its s (print_args (print_ity true 2)) tl
  | Ityapp (s,tl,_) when not pur && s.its_mutable ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "{%a}%a")
        print_its s (print_args (print_ity pur 2)) tl
  | Ityapp (s,tl,_) | Ityreg {reg_its = s; reg_args = tl} ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "%a%a")
        print_its s (print_args (print_ity pur 2)) tl

let print_ity fmt ity = print_ity false 0 fmt ity

let rec print_ity_node sb pur pri fmt ity = match ity.ity_node with
  | Ityvar v ->
      begin match Mtv.find_opt v sb.isb_var with
        | Some ity -> print_ity_node isb_empty pur pri fmt ity
        | None -> print_tv fmt v
      end
  | Ityapp (s,[t1;t2],[]) when its_equal s its_func ->
      fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_ity_node sb pur 1) t1 (print_ity_node sb pur 0) t2
  | Ityapp (s,tl,[]) when is_ts_tuple s.its_ts ->
      fprintf fmt "(%a)" (Pp.print_list Pp.comma (print_ity_node sb pur 0)) tl
  | Ityapp (s,tl,_) when pur ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "%a%a")
        print_its s (print_args (print_ity_node sb pur 2)) tl
  | Ityapp (s,tl,rl) when not s.its_mutable ->
      fprintf fmt (protect_on (pri > 1 && (tl <> [] || rl <> [])) "%a%a%a")
        print_its s (print_args (print_ity_node sb pur 2)) tl
        (print_regs (print_ity_node sb pur 0)) rl
  | Ityapp (s,tl,_) when ity.ity_pure ->
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
  print_pv v print_id_attrs v.pv_vs.vs_name
  print_ity v.pv_ity

let forget_pv v = forget_var v.pv_vs

let print_xs fmt xs = pp_print_string fmt (id_unique xprinter xs.xs_name)

let forget_xs xs = forget_id xprinter xs.xs_name

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
    let n = asprintf "%a" print_vs v in
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
  fprintf fmt "@[<hov 4>@[%a@]%a@]"
    (Pp.print_list_pre Pp.space print_pvty) args
    (Pp.print_option print_result) ity;
  if diverges eff.eff_oneway then pp_print_string fmt " diverges";
  let reads = List.fold_right Spv.remove args eff.eff_reads in
  if not (Spv.is_empty reads) then fprintf fmt "@\nreads  { @[%a@] }"
    (Pp.print_list Pp.comma print_pv) (Spv.elements reads);
  if not (Mreg.is_empty eff.eff_writes) then fprintf fmt "@\nwrites { @[%a@] }"
    (Pp.print_list Pp.comma print_write) (Mreg.bindings eff.eff_writes);
  if not (Sreg.is_empty eff.eff_covers) then fprintf fmt "@\ncovers { @[%a@] }"
    (Pp.print_list Pp.comma print_region) (Sreg.elements eff.eff_covers);
  if not (Sreg.is_empty eff.eff_resets) then fprintf fmt "@\nresets { @[%a@] }"
    (Pp.print_list Pp.comma print_region) (Sreg.elements eff.eff_resets);
  if not (Stv.is_empty eff.eff_spoils) then fprintf fmt "@\nspoils { @[%a@] }"
    (Pp.print_list Pp.comma Pretty.print_tv) (Stv.elements eff.eff_spoils);
  Pp.print_list Pp.nothing print_pre fmt pre;
  Pp.print_list Pp.nothing print_old fmt (Mpv.bindings oldies);
  Pp.print_list Pp.nothing print_post fmt post;
  Pp.print_list Pp.nothing print_xpost fmt (Mxs.bindings xpost)

let print_cty fmt c = print_spec c.cty_args c.cty_pre c.cty_post
  c.cty_xpost c.cty_oldies c.cty_effect fmt (Some c.cty_result)

let forget_cty c =
  List.iter forget_pv c.cty_args;
  Mpv.iter (fun v _ -> forget_pv v) c.cty_oldies

(** exception handling *)

let () = Exn_printer.register (fun fmt e -> match e with
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
(*
  | UnboundException xs -> fprintf fmt
      "This function raises %a but does not specify a post-condition for it"
        print_xs xs
*)
  | TypeMismatch (t1,t2,s) -> fprintf fmt
      "Type mismatch between %a and %a"
        (print_ity_node s false 0) t1 print_ity_full t2
  | IllegalUpdate (v, _r) -> fprintf fmt
      "This expression modifies a non-updatable component of variable %a"
        print_pv v
  | StaleVariable (v, _r) -> fprintf fmt
      "This expression prohibits further usage of the variable %a \
        or any function that depends on it" print_pv v
  | BadGhostWrite (v, _r) -> fprintf fmt
      "This expression makes a ghost modification in the non-ghost variable %a"
        print_pv v
  | AssignPrivate r -> fprintf fmt
      "This assignment modifies a value of the private type %a" print_reg r
  | AssignSnapshot t -> fprintf fmt
      "This assignment modifies a value of the immutable type %a" print_ity t
  | WriteImmutable (r, v) -> fprintf fmt
      "In the type symbol %a, the field %s is immutable"
        print_its r.reg_its v.pv_vs.vs_name.id_string
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
  | ImpureVariable (v,t) -> fprintf fmt
      "This application instantiates pure type variable %a \
        with a mutable type %a" Pretty.print_tv v print_ity t
  | IllegalAssign (r1,r2,r3) -> fprintf fmt
      "This assignment mismatches regions (%a: %a - %a)"
        print_reg r1 print_reg r2 print_reg r3
  | _ -> raise e)
