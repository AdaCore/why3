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
  its_ts      : tysymbol;       (** pure "snapshot" type symbol *)
  its_privmut : bool;           (** private mutable record type *)
  its_mfields : pvsymbol list;  (** mutable record fields *)
  its_regions : region list;    (** mutable shareable components *)
  its_arg_imm : bool list;      (** non-updatable type parameters *)
  its_arg_exp : bool list;      (** exposed type parameters *)
  its_arg_vis : bool list;      (** non-ghost type parameters *)
  its_arg_frz : bool list;      (** irreplaceable type parameters *)
  its_reg_vis : bool list;      (** non-ghost shareable components *)
  its_reg_frz : bool list;      (** irreplaceable shareable components *)
  its_def     : ity type_def;   (** type definition *)
}

and ity = {
  ity_node : ity_node;
  ity_pure : bool;
  ity_tag  : Weakhtbl.tag;
}

and ity_node =
  | Ityreg of region
    (** record with mutable fields and shareable components *)
  | Ityapp of itysymbol * ity list * region list
    (** algebraic type with shareable components *)
  | Itypur of itysymbol * ity list
    (** immutable type or a snapshot of a mutable type *)
  | Ityvar of tvsymbol
    (** type variable *)

and region = {
  reg_name : ident;
  reg_its  : itysymbol;
  reg_args : ity list;
  reg_regs : region list;
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

let its_mutable s = s.its_privmut || s.its_mfields <> [] ||
  match s.its_def with Alias {ity_node = Ityreg _} -> true | _ -> false

let its_impure s = its_mutable s || s.its_regions <> []

exception NonUpdatable of itysymbol * ity

let check_its_args s tl =
  assert (not (is_alias_type_def s.its_def));
  let check_imm acc imm ity =
    if imm && not ity.ity_pure then raise (NonUpdatable (s,ity));
    acc && ity.ity_pure in
  List.fold_left2 check_imm true s.its_arg_imm tl

module Hsity = Hashcons.Make (struct
  type t = ity

  let equal ity1 ity2 = match ity1.ity_node, ity2.ity_node with
    | Ityvar v1, Ityvar v2 -> tv_equal v1 v2
    | Ityreg r1, Ityreg r2 -> reg_equal r1 r2
    | Itypur (s1,l1), Itypur (s2,l2) ->
        its_equal s1 s2 &&
        List.for_all2 ity_equal l1 l2
    | Ityapp (s1,l1,r1), Ityapp (s2,l2,r2) ->
        its_equal s1 s2 &&
        List.for_all2 ity_equal l1 l2 &&
        List.for_all2 reg_equal r1 r2
    | _ -> false

  let hash ity = match ity.ity_node with
    | Ityvar v -> tv_hash v
    | Ityreg r -> reg_hash r
    | Itypur (s,tl) ->
        Hashcons.combine_list ity_hash (its_hash s) tl
    | Ityapp (s,tl,rl) ->
        Hashcons.combine_list reg_hash
          (Hashcons.combine_list ity_hash (its_hash s) tl) rl

  let pure ity = match ity.ity_node with
    | Ityvar _ -> true
    | Ityreg _ -> false
    | Itypur (s,tl) -> check_its_args s tl
    | Ityapp (s,tl,_::_) -> check_its_args s tl && false
    | Ityapp _ -> assert false

  let tag n ity = { ity with
    ity_pure = pure ity;
    ity_tag  = Weakhtbl.create_tag n }
end)

let mk_ity node = {
  ity_node = node;
  ity_pure = true;
  ity_tag  = Weakhtbl.dummy_tag;
}

let mk_reg name s tl rl = {
  reg_name = id_register name;
  reg_its  = s;
  reg_args = (ignore (check_its_args s tl); tl);
  reg_regs = rl;
}

let ity_var v = Hsity.hashcons (mk_ity (Ityvar v))
let ity_reg r = Hsity.hashcons (mk_ity (Ityreg r))

let ity_pur_unsafe s tl    = Hsity.hashcons (mk_ity (Itypur (s,tl)))
let ity_app_unsafe s tl rl = Hsity.hashcons (mk_ity (Ityapp (s,tl,rl)))

(* generic traversal functions *)

let dfold fn1 fn2 acc l1 l2 =
  List.fold_left fn2 (List.fold_left fn1 acc l1) l2

let dfold2 fn1 fn2 acc l1 r1 l2 r2 =
  List.fold_left2 fn2 (List.fold_left2 fn1 acc l1 r1) l2 r2

let ity_fold fnt fnr acc ity = match ity.ity_node with
  | Ityapp (_,tl,rl) -> dfold fnt fnr acc tl rl
  | Itypur (_,tl) -> List.fold_left fnt acc tl
  | Ityreg r -> fnr acc r
  | Ityvar _ -> acc

let reg_fold fnt fnr acc r = dfold fnt fnr acc r.reg_args r.reg_regs

(* symbol-wise fold *)

let rec ity_s_fold fn acc ity = match ity.ity_node with
  | Ityapp (s,_,_) | Itypur (s,_) ->
      ity_fold (ity_s_fold fn) (reg_s_fold fn) (fn acc s) ity
  | Ityreg r -> reg_s_fold fn acc r
  | Ityvar _ -> acc

and reg_s_fold fn acc r =
  reg_fold (ity_s_fold fn) (reg_s_fold fn) (fn acc r.reg_its) r

(* traversal functions on type variables and regions *)

let rec ity_v_fold fn acc ity = match ity.ity_node with
  | Ityapp (_,tl,_) | Itypur (_,tl) | Ityreg {reg_args = tl} ->
      List.fold_left (ity_v_fold fn) acc tl
  | Ityvar v -> fn acc v

let reg_v_fold fn acc r = List.fold_left (ity_v_fold fn) acc r.reg_args

let ity_freevars s ity = ity_v_fold (fun s v -> Stv.add v s) s ity
let reg_freevars s reg = reg_v_fold (fun s v -> Stv.add v s) s reg

let ity_v_occurs v ity = Util.any ity_v_fold (tv_equal v) ity
let reg_v_occurs v reg = Util.any reg_v_fold (tv_equal v) reg

let ity_closed ity = Util.all ity_v_fold Util.ffalse ity

let rec ity_r_fold fn acc ity = if ity.ity_pure then acc else
                                ity_fold (ity_r_fold fn) fn acc ity
let     reg_r_fold fn acc reg = reg_fold (ity_r_fold fn) fn acc reg

let rec reg_freeregs s reg = reg_r_fold reg_freeregs (Sreg.add reg s) reg
let     ity_freeregs s ity = ity_r_fold reg_freeregs s ity

let rec reg_r_occurs r reg = reg_equal r reg ||
                             Util.any reg_r_fold (reg_r_occurs r) reg
let     ity_r_occurs r ity = Util.any ity_r_fold (reg_r_occurs r) ity

(* detect stale regions *)

let rec ity_r_stale reg cvr exp ity =
  exp && not ity.ity_pure && match ity.ity_node with
  | Ityreg r -> reg_r_stale reg cvr r
  | Ityapp (s,tl,rl) -> its_r_stale reg cvr s tl rl
  | Itypur (_,tl) -> List.exists (ity_r_stale reg cvr true) tl
  | Ityvar _ -> false

and reg_r_stale reg cvr r =
  reg_equal r reg || (not (Sreg.mem r cvr) &&
    its_r_stale reg cvr r.reg_its r.reg_args r.reg_regs)

and its_r_stale reg cvr s tl rl =
  List.exists2 (ity_r_stale reg cvr) s.its_arg_exp tl ||
  List.exists (reg_r_stale reg cvr) rl

let ity_r_stale reg cvr ity = ity_r_stale reg cvr true ity

(* detect non-ghost type variables and regions *)

let rec ity_visible fnv fnr acc vis ity =
  if not vis then acc else
  match ity.ity_node with
  | Ityreg r ->
      reg_visible fnv fnr acc vis r
  | Ityapp (s,tl,rl) ->
      dfold2 (ity_visible fnv fnr) (reg_visible fnv fnr)
        acc s.its_arg_vis tl s.its_reg_vis rl
  | Itypur (s,tl) ->
      List.fold_left2 (ity_visible fnv fnr) acc s.its_arg_vis tl
  | Ityvar v -> fnv acc v

and reg_visible fnv fnr acc vis r =
  if not vis then acc else
  dfold2 (ity_visible fnv fnr) (reg_visible fnv fnr)
    (fnr acc r) r.reg_its.its_arg_vis r.reg_args
                r.reg_its.its_reg_vis r.reg_regs

let ity_v_visible vars ity =
  ity_visible (fun s v -> Stv.add v s) Util.const vars true ity

let ity_r_visible regs ity = if ity.ity_pure then regs else
  ity_visible Util.const (fun s r -> Sreg.add r s) regs true ity

(* detect non-updatable type variables *)

let rec ity_v_immutable vars imm ity =
  match ity.ity_node with
  | _ when imm -> ity_freevars vars ity
  | Ityreg {reg_its = s; reg_args = tl}
  | Ityapp (s,tl,_) | Itypur (s,tl) ->
      List.fold_left2 ity_v_immutable vars s.its_arg_imm tl
  | Ityvar _ -> vars

let ity_v_immutable vars ity = ity_v_immutable vars true ity

(* detect exposed type variables *)

let rec ity_v_exposed vars exp ity =
  match ity.ity_node with
  | _ when not exp -> vars
  | Ityreg _ -> vars
  | Ityapp (s,tl,_) | Itypur (s,tl) ->
      List.fold_left2 ity_v_exposed vars s.its_arg_exp tl
  | Ityvar v -> Stv.add v vars

let ity_v_exposed vars ity = ity_v_exposed vars true ity

(* smart constructors *)

exception BadItyArity of itysymbol * int
exception BadRegArity of itysymbol * int

exception DuplicateRegion of region
exception UnboundRegion of region

type ity_subst = {
  isb_tv  : ity Mtv.t;
  isb_reg : region Mreg.t;
}

let isb_empty = {
  isb_tv  = Mtv.empty;
  isb_reg = Mreg.empty;
}

exception TypeMismatch of ity * ity * ity_subst

let ity_equal_check t1 t2 = if not (ity_equal t1 t2) then
  raise (TypeMismatch (t1, t2, isb_empty))

let reg_equal_check r1 r2 = if not (reg_equal r1 r2) then
  raise (TypeMismatch (ity_reg r1, ity_reg r2, isb_empty))

let ity_full_inst sbs ity =
  let freg r = Mreg.find r sbs.isb_reg in
  let rec inst ity = match ity.ity_node with
    | Ityapp (s,tl,rl) ->
        ity_app_unsafe s (List.map inst tl) (List.map freg rl)
    | Itypur (s,tl) -> ity_pur_unsafe s (List.map inst tl)
    | Ityvar v -> Mtv.find v sbs.isb_tv
    | Ityreg r -> ity_reg (freg r) in
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
      dfold2 ity_match reg_match sbs l1 l2 r1 r2
  | Itypur (s1,l1), Itypur (s2,l2) when its_equal s1 s2 ->
      List.fold_left2 ity_match sbs l1 l2
  | Ityreg r1, Ityreg r2 -> reg_match sbs r1 r2
  | Ityvar v1, _ -> { sbs with
      isb_tv = Mtv.change set v1 sbs.isb_tv }
  | _ -> raise Exit

and reg_match sbs reg1 reg2 =
  let known = ref false in
  let eq reg reg2 = known := true; reg_equal reg reg2 in
  let sbs = { sbs with isb_reg = Mreg.change
    (add_or_keep eq reg2) reg1 sbs.isb_reg } in
  if !known then sbs else dfold2 ity_match reg_match sbs
    reg1.reg_args reg2.reg_args reg1.reg_regs reg2.reg_regs

let ity_match sbs ity1 ity2 = try ity_match sbs ity1 ity2
  with Exit -> raise (TypeMismatch (ity1,ity2,sbs))

let reg_match sbs reg1 reg2 = try reg_match sbs reg1 reg2
  with Exit -> raise (TypeMismatch (ity_reg reg1, ity_reg reg2, sbs))

let ity_freeze sbs ity = ity_match sbs ity ity
let reg_freeze sbs reg = reg_match sbs reg reg

let rec ty_of_ity ity = match ity.ity_node with
  | Ityvar v -> ty_var v
  | Itypur (s,tl) | Ityapp (s,tl,_)
  | Ityreg {reg_its = s; reg_args = tl} ->
      ty_app s.its_ts (List.map ty_of_ity tl)

let rec ity_purify ity = match ity.ity_node with
  | _ when ity.ity_pure -> ity
  | Ityvar _ -> ity
  | Itypur (s,tl) | Ityapp (s,tl,_)
  | Ityreg {reg_its = s; reg_args = tl} ->
      ity_pur_unsafe s (List.map ity_purify tl)

let its_match_args s tl =
  try {
    isb_tv  = List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty;
    isb_reg = Mreg.empty }
  with Invalid_argument _ -> raise (BadItyArity (s, List.length tl))

let its_match_regs s tl rl =
  try List.fold_left2 reg_match (its_match_args s tl) s.its_regions rl
  with Invalid_argument _ -> raise (BadItyArity (s, List.length rl))

let ity_pur s tl =
  (* compute the substitution even for non-aliases to verify arity *)
  let sbs = its_match_args s tl in
  match s.its_def with
  | Alias ity ->
      ity_full_inst sbs (ity_purify ity)
  | _ ->
      ity_pur_unsafe s tl

let create_region sbs id s tl rl = match s.its_def with
  | Alias { ity_node = Ityreg r } ->
      let tl = List.map (ity_full_inst sbs) r.reg_args in
      let rl = List.map (reg_full_inst sbs) r.reg_regs in
      mk_reg id r.reg_its tl rl
  | _ when its_mutable s ->
      mk_reg id s tl rl
  | _ -> invalid_arg "Ity.create_region"

let ity_app sbs s tl rl =
  if its_mutable s then
    ity_reg (create_region sbs (id_fresh "rho") s tl rl)
  else match s.its_def with
  | Alias ity ->
      ity_full_inst sbs ity
  | _ when rl = [] ->
      ity_pur_unsafe s tl
  | _ ->
      ity_app_unsafe s tl rl

let rec ity_inst_fresh sbs ity = match ity.ity_node with
  | Ityvar v ->
      sbs, Mtv.find v sbs.isb_tv
  | Itypur (s,tl) ->
      let sbs, tl = Lists.map_fold_left ity_inst_fresh sbs tl in
      sbs, ity_pur_unsafe s tl
  | Ityapp (s,tl,rl) ->
      let sbs, tl = Lists.map_fold_left ity_inst_fresh sbs tl in
      let sbs, rl = Lists.map_fold_left reg_inst_fresh sbs rl in
      sbs, ity_app_unsafe s tl rl
  | Ityreg r when Mreg.mem r sbs.isb_reg ->
      sbs, ity_reg (Mreg.find r sbs.isb_reg)
  | Ityreg r ->
      let sbs, r = reg_inst_fresh sbs r in
      sbs, ity_reg r

and reg_inst_fresh sbs r =
  let sbs, tl = Lists.map_fold_left ity_inst_fresh sbs r.reg_args in
  let sbs, rl = Lists.map_fold_left reg_inst_fresh sbs r.reg_regs in
  let reg = mk_reg (id_clone r.reg_name) r.reg_its tl rl in
  reg_match sbs r reg, reg

let ity_app_fresh s tl =
  let sbs = its_match_args s tl in
  let sbs, rl = Lists.map_fold_left reg_inst_fresh sbs s.its_regions in
  ity_app sbs s tl rl

let ity_app s tl rl =
  ity_app (its_match_regs s tl rl) s tl rl

let create_region id s tl rl =
  create_region (its_match_regs s tl rl) id s tl rl

(* itysymbol creation *)

let create_its, restore_its =
  let ts_to_its = Wts.create 17 in
  (fun ~ts ~pm ~mfld ~regs ~aimm ~aexp ~avis ~afrz ~rvis ~rfrz ~def ->
    let its = {
      its_ts      = ts;
      its_privmut = pm;
      its_mfields = mfld;
      its_regions = regs;
      its_arg_imm = aimm;
      its_arg_exp = aexp;
      its_arg_vis = avis;
      its_arg_frz = afrz;
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
      ity_pur_unsafe s (List.map ity_of_ty tl)

let its_of_ts ts imm =
  let tl = List.map Util.ttrue ts.ts_args in
  let il = if imm then tl else List.map Util.ffalse ts.ts_args in
  let def = match ts.ts_def with
    | Alias ty -> Alias (ity_of_ty ty)
    | Range ir -> Range ir
    | Float fp -> Float fp
    | NoDef    -> NoDef in
  create_its ~ts ~pm:false ~mfld:[] ~regs:[] ~aimm:il ~aexp:tl ~avis:tl
          ~afrz:tl ~rvis:[] ~rfrz:[] ~def

let create_itysymbol_pure id args =
  its_of_ts (create_tysymbol id args NoDef) true

let create_itysymbol_alias id args def =
  (* FIXME? should we compute [arg|reg]_[imm|exp|vis|frz]? *)
  let ts = create_tysymbol id args (Alias (ty_of_ity def)) in
  let regs = Sreg.elements (let add_r s r = Sreg.add r s in
    match def.ity_node with
    | Ityreg reg -> reg_r_fold add_r Sreg.empty reg
    | _          -> ity_r_fold add_r Sreg.empty def) in
  let tl = List.map Util.ttrue args in
  let rl = List.map Util.ttrue regs in
  create_its ~ts ~pm:false ~mfld:[] ~regs ~aimm:tl ~aexp:tl
    ~avis:tl ~afrz:tl ~rvis:rl ~rfrz:rl ~def:(Alias def)

exception ImpureField of ity

let create_itysymbol_rich id args pm flds =
  let ts = create_tysymbol id args NoDef in
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
    Mpv.iter (fun {pv_vs = v; pv_ity = i} _ -> if not i.ity_pure
      then Loc.error ?loc:v.vs_name.id_loc (ImpureField i)) flds;
    create_its ~ts ~pm ~mfld ~regs:[] ~aimm:tl ~aexp:tl ~avis:tl
      ~afrz:tl ~rvis:[] ~rfrz:[] ~def:NoDef
  end else (* non-private updatable type *)
    let top_regs ity = ity_r_fold (fun s r -> Sreg.add r s) ity in
    let regs = Sreg.elements (collect_all top_regs Sreg.empty) in
    let check_args s = List.map (fun v -> Stv.mem v s) args in
    let check_regs s = List.map (fun r -> Sreg.mem r s) regs in
    let aimm = check_args (collect_all ity_v_immutable Stv.empty) in
    let aexp = check_args (collect_all ity_v_exposed Stv.empty) in
    let avis = check_args (collect_vis ity_v_visible Stv.empty) in
    let rvis = check_regs (collect_vis ity_r_visible Sreg.empty) in
    let afrz = check_args (collect_imm ity_freevars Stv.empty) in
    let rfrz = check_regs (collect_imm ity_freeregs Sreg.empty) in
    create_its ~ts ~pm ~mfld ~regs ~aimm ~aexp ~avis ~afrz ~rvis
      ~rfrz ~def:NoDef

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
let its_pred = its_of_ts ts_pred true

let ity_int  = ity_pur its_int  []
let ity_real = ity_pur its_real []
let ity_bool = ity_pur its_bool []

let ity_func a b = ity_pur its_func [a;b]
let ity_pred a   = ity_pur its_pred [a]

let its_tuple = Hint.memo 17 (fun n -> its_of_ts (ts_tuple n) false)

let ity_tuple tl = ity_pur (its_tuple (List.length tl)) tl

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
  if not ity.ity_pure then Loc.errorm ?loc:id.pre_loc
    "The type of exception %s has mutable components" id.pre_name;
  { xs_name = id_register id; xs_ity = ity; }

module Exn = MakeMSH (struct
  type t = xsymbol
  let tag xs = Weakhtbl.tag_hash xs.xs_name.id_tag
end)

module Sexn = Exn.S
module Mexn = Exn.M

(* effects *)

exception IllegalAlias of region
exception AssignPrivate of region
exception BadGhostWrite of pvsymbol * region
exception StaleVariable of pvsymbol * region
exception DuplicateField of region * pvsymbol
exception GhostDivergence

type effect = {
  eff_reads  : Spv.t;         (* known variables *)
  eff_writes : Spv.t Mreg.t;  (* modifications to specific fields *)
  eff_covers : Sreg.t Mreg.t; (* confinement of regions to covers *)
  eff_taints : Sreg.t;        (* ghost modifications *)
  eff_raises : Sexn.t;        (* raised exceptions *)
  eff_oneway : bool;          (* non-termination *)
  eff_ghost  : bool;          (* ghost status *)
}

let eff_empty = {
  eff_reads  = Spv.empty;
  eff_writes = Mreg.empty;
  eff_covers = Mreg.empty;
  eff_taints = Sreg.empty;
  eff_raises = Sexn.empty;
  eff_oneway = false;
  eff_ghost  = false;
}

let eff_equal e1 e2 =
  Spv.equal e1.eff_reads e2.eff_reads &&
  Mreg.equal Spv.equal e1.eff_writes e2.eff_writes &&
  Mreg.equal Sreg.equal e1.eff_covers e2.eff_covers &&
  Sreg.equal e1.eff_taints e2.eff_taints &&
  Sexn.equal e1.eff_raises e2.eff_raises &&
  e1.eff_oneway = e2.eff_oneway &&
  e1.eff_ghost = e2.eff_ghost

let eff_pure e =
  Mreg.is_empty e.eff_writes &&
  Sexn.is_empty e.eff_raises &&
  not e.eff_oneway

let check_covers cvr pvs =
  if not (Mreg.is_empty cvr) then Spv.iter (fun v ->
    Mreg.iter (fun r c -> if ity_r_stale r c v.pv_ity
      then raise (StaleVariable (v,r))) cvr) pvs

let check_taints tnt pvs =
  if not (Sreg.is_empty tnt) then Spv.iter (fun v ->
    ity_visible Util.const (fun () r -> if Sreg.mem r tnt
      then raise (BadGhostWrite (v,r))) () (not v.pv_ghost) v.pv_ity) pvs

let visible_writes e =
  Mreg.subdomain (fun {reg_its = {its_privmut = priv}} fs ->
    priv || Spv.exists (fun fd -> not fd.pv_ghost) fs) e.eff_writes

let visible_reads e =
  Spv.fold (fun {pv_ghost = gh; pv_ity = ity} s ->
    if gh then s else ity_r_visible s ity) e.eff_reads Sreg.empty

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
  let _ = check_taints e.eff_taints rd in
  let _ = check_covers e.eff_covers rd in
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

let eff_write rd wr =
  if Mreg.is_empty wr then { eff_empty with eff_reads = rd } else
  let kn = Spv.fold (fun v s -> ity_freeregs s v.pv_ity) rd Sreg.empty in
  let wr = Mreg.filter (fun ({reg_its = {its_privmut = p}} as r) fs ->
    if not p && Spv.is_empty fs then invalid_arg "Ity.eff_write";
    Spv.iter (check_mutable_field "Ity.eff_write" r) fs;
    Sreg.mem r kn) wr in
  reset_taints { eff_empty with eff_reads = rd; eff_writes = wr }

let merge_fields _ f1 f2 = Some (Spv.union f1 f2)

let merge_covers reg c1 c2 = Some (Sreg.union
  (Sreg.filter (fun r -> not (reg_r_stale reg c1 r)) c2)
  (Sreg.filter (fun r -> not (reg_r_stale reg c2 r)) c1))

let get_cover reg m = Mreg.subdomain (fun r _ ->
  not (reg_equal reg r) && reg_r_occurs reg r) m

(* freeze type variables and regions outside modified fields *)
let freeze_of_writes wr =
  let freeze_of_write r fs frz =
    let sbs = its_match_regs r.reg_its r.reg_args r.reg_regs in
    let frz_fa frz b a = if b then ity_freeze frz a else frz in
    let frz_fr frz b r = if b then reg_freeze frz r else frz in
    let frz_if frz f = ity_freeze frz (ity_full_inst sbs f.pv_ity) in
    let frz_mf frz f = if Mpv.mem f fs then frz else frz_if frz f in
    let frz = reg_v_fold (fun frz v -> (* freeze type variables *)
      { frz with isb_tv = Mtv.add v (ity_var v) frz.isb_tv }) frz r in
    let frz = dfold2 frz_fa frz_fr frz r.reg_its.its_arg_frz r.reg_args
                                       r.reg_its.its_reg_frz r.reg_regs in
    List.fold_left frz_mf frz r.reg_its.its_mfields in
  Mreg.fold freeze_of_write wr isb_empty

let eff_assign asl =
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
  (* type variables and regions outside modified fields are frozen *)
  let frz = freeze_of_writes writes in
  (* non-frozen regions are allowed to be renamed, preserving aliases *)
  let sbst, sbsf = Mreg.fold (fun r fs acc ->
    let sbs = its_match_regs r.reg_its r.reg_args r.reg_regs in
    (* TODO: catch the TypeMismatch exception
       and produce a reasonable error message *)
    Mpv.fold (fun f ity (sbst,sbsf) ->
      let fity = ity_full_inst sbs f.pv_ity in
      ity_match sbst fity ity,
      ity_match sbsf ity fity) fs acc) writes (frz,frz) in
  let sbst, sbsf = sbst.isb_reg, sbsf.isb_reg in
  (* every LHS region not instantiated to itself is confined,
     every non-instantiated RHS region is reset *)
  let cover = Mreg.mapi_filter (fun ro rn ->
    if reg_equal ro rn then None else Some (get_cover ro writes)) sbst in
  let reset = Mreg.map (fun _ -> Sreg.empty) (Mreg.set_diff sbsf sbst) in
  (* construct the effect *)
  let ghost = List.for_all (fun (r,f,v) ->
    r.pv_ghost || f.pv_ghost || v.pv_ghost) asl in
  let taint = List.fold_left (fun s (r,f,v) ->
    if (r.pv_ghost || v.pv_ghost) && not f.pv_ghost then
      Sreg.add (get_reg r) s else s) Sreg.empty asl in
  let reads = List.fold_left (fun s (r,_,v) ->
    Spv.add r (Spv.add v s)) Spv.empty asl in
  check_taints taint reads;
  { eff_reads  = reads;
    eff_writes = Mreg.map Mpv.domain writes;
    eff_covers = Mreg.set_union reset cover;
    eff_taints = taint;
    eff_raises = Sexn.empty;
    eff_oneway = false;
    eff_ghost  = ghost }

let eff_strong ({eff_writes = wr} as e) =
  let freeze r _ sbs = reg_freeze sbs r in
  let sbs = Mreg.fold freeze wr isb_empty in
  let frz = (freeze_of_writes wr).isb_reg in
  let cvr = Mreg.set_diff sbs.isb_reg frz in
  let cvr = Mreg.map (fun ro -> get_cover ro wr) cvr in
  let cvr = Mreg.union merge_covers e.eff_covers cvr in
  { e with eff_covers = cvr }

let eff_raise e x = { e with eff_raises = Sexn.add x e.eff_raises }
let eff_catch e x = { e with eff_raises = Sexn.remove x e.eff_raises }
let eff_reset e r = { e with eff_covers = Mreg.add r Sreg.empty e.eff_covers }

let eff_union e1 e2 = {
  eff_reads  = Spv.union e1.eff_reads e2.eff_reads;
  eff_writes = Mreg.union merge_fields e1.eff_writes e2.eff_writes;
  eff_covers = Mreg.union merge_covers e1.eff_covers e2.eff_covers;
  eff_taints = Sreg.union e1.eff_taints e2.eff_taints;
  eff_raises = Sexn.union e1.eff_raises e2.eff_raises;
  eff_oneway = e1.eff_oneway || e2.eff_oneway;
  eff_ghost  = e2.eff_ghost }

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
  check_covers e1.eff_covers e2.eff_reads;
  check_taints e1.eff_taints e2.eff_reads;
  check_taints e2.eff_taints e1.eff_reads;
  eff_union e1 e2

(* NOTE: do not export this function *)
let eff_inst sbs e =
  (* all modified or reset regions in e must be instantiated into
     distinct regions. We allow regions that are not affected directly
     to be aliased, even if they contain modified or reset subregions:
     the values are still updated at the same program points and with
     the same postconditions, as in the initial verified code. *)
  let inst fn src = Mreg.fold (fun r v acc ->
    let r = reg_full_inst sbs r and v = fn v in
    Mreg.add_new (IllegalAlias r) r v acc) src Mreg.empty in
  let writes = inst (fun fld -> fld) e.eff_writes in
  let covers = inst (inst ignore) e.eff_covers in
  let taints = inst ignore e.eff_taints in
  let impact = Mreg.merge (fun r fld cvr -> match fld, cvr with
    | Some _, Some _ -> raise (IllegalAlias r)
    | _ -> Some ()) writes covers in
  (* all type variables and unaffected regions must be instantiated
     outside [impact]. Every region in the instantiated execution
     is either brought in by the type substitution or instantiates
     one of the original regions. *)
  let sreg = Mreg.set_diff sbs.isb_reg e.eff_writes in
  let sreg = Mreg.set_diff sreg e.eff_covers in
  let dst = Mreg.fold (fun _ r s -> Sreg.add r s) sreg Sreg.empty in
  let dst = Mtv.fold (fun _ i s -> ity_freeregs s i) sbs.isb_tv dst in
  ignore (Mreg.inter (fun r _ _ -> raise (IllegalAlias r)) dst impact);
  { e with eff_writes = writes; eff_covers = covers; eff_taints = taints }

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
        let (* non-ghost *) x = Nil in
        let ghost y = if true then x else Some ghost_ref in
        match x with Some r -> r := 0 | None -> () end
     The write is regular here, but the only path to it, via
     ghost_ref is ghost. Strictly speaking, such writes can
     be removed (we cannot create a real regular alias to a
     ghost location), but it is simpler to just recast them
     as ghost, to keep the type signature consistent. *)
  let known = List.fold_right freeze_pv args freeze in
  let filter m = Mreg.set_inter m known.isb_reg in
  let effect = reset_taints { effect with
    eff_writes = filter effect.eff_writes;
    eff_covers = Mreg.map filter (filter effect.eff_covers) } in
  (* reset every fresh region in the result *)
  let resreg = ity_freeregs Sreg.empty result in
  let unknwn = Mreg.set_diff resreg known.isb_reg in
  let resets = Mreg.map (fun _ -> Sreg.empty) unknwn in
  let covers = Mreg.set_union resets effect.eff_covers in
  let effect = { effect with eff_covers = covers } in
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
  (* stage 4: reset the new fresh regions in the result *)
  let effect = if ity_equal c.cty_result res then effect else
    let known = List.fold_right freeze_pv rargs freeze in
    let resreg = ity_freeregs Sreg.empty res in
    let unknwn = Mreg.set_diff resreg known.isb_reg in
    let resets = Mreg.map (fun _ -> Sreg.empty) unknwn in
    let covers = Mreg.set_union resets effect.eff_covers in
    { effect with eff_covers = covers } in
  (* stage 5: instantiate the specification *)
  let tsb = Mtv.map ty_of_ity isb.isb_tv in
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

let rec print_ity pri fmt ity = match ity.ity_node with
  | Ityvar v -> print_tv fmt v
  | Itypur (s,[t1;t2]) when its_equal s its_func ->
      fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_ity 1) t1 (print_ity 0) t2
  | Itypur (s,tl) when is_ts_tuple s.its_ts ->
      fprintf fmt "(%a)" (Pp.print_list Pp.comma (print_ity 0)) tl
  | Itypur (s,tl) when its_impure s ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "{%a}%a")
        print_its s (print_args (print_ity 2)) tl
  | Itypur (s,tl)
  | Ityapp (s,tl,_)
  | Ityreg {reg_its = s; reg_args = tl} ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "%a%a")
        print_its s (print_args (print_ity 2)) tl

let print_ity fmt ity = print_ity 0 fmt ity

let rec print_ity_node sb pri fmt ity = match ity.ity_node with
  | Ityvar v ->
      begin match Mtv.find_opt v sb.isb_tv with
        | Some ity -> print_ity_node isb_empty pri fmt ity
        | None -> print_tv fmt v
      end
  | Itypur (s,[t1;t2]) when its_equal s its_func ->
      fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_ity_node sb 1) t1 (print_ity_node sb 0) t2
  | Itypur (s,tl) when is_ts_tuple s.its_ts ->
      fprintf fmt "(%a)" (Pp.print_list Pp.comma (print_ity_node sb 0)) tl
  | Itypur (s,tl) when its_impure s ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "{%a}%a")
        print_its s (print_args (print_ity_node sb 2)) tl
  | Itypur (s,tl) ->
      fprintf fmt (protect_on (pri > 1 && tl <> []) "%a%a")
        print_its s (print_args (print_ity_node sb 2)) tl
  | Ityapp (s,tl,rl) ->
      fprintf fmt (protect_on (pri > 1) "%a%a%a")
        print_its s (print_args (print_ity_node sb 2)) tl
        (print_regs (print_reg_node sb)) rl
  | Ityreg r ->
      fprintf fmt (protect_on (pri > 1) "%a") (print_reg_node sb) r

and print_reg_node sb fmt r = print_reg fmt (Mreg.find_def r r sb.isb_reg)

and print_reg fmt r = fprintf fmt "%a%a%a@ %a"
  print_its r.reg_its (print_args (print_ity_node isb_empty 2)) r.reg_args
  (print_regs print_reg) r.reg_regs print_reg_name r

let print_ity_full fmt ity = print_ity_node isb_empty 0 fmt ity

let print_pv fmt v = print_vs fmt v.pv_vs

let print_pvty fmt v = fprintf fmt "@[(%s%a%a:@,%a)@]"
  (if v.pv_ghost then "ghost " else "")
  print_pv v print_id_labels v.pv_vs.vs_name
  print_ity v.pv_ity

let forget_pv v = forget_var v.pv_vs

let print_xs fmt xs = pp_print_string fmt (id_unique xprinter xs.xs_name)

exception FoundPrefix of pvsymbol list

let unknown = create_pvsymbol (id_fresh "?") ity_unit

let print_spec args pre post xpost eff fmt ity =
  let dot fmt () = pp_print_char fmt '.' in
  let print_pfx reg fmt pfx = fprintf fmt "@[%a:@,%a@]"
    (Pp.print_list dot print_pv) pfx print_reg reg in
  let rec find_prefix pfx reg ity = match ity.ity_node with
    | Ityreg r when reg_equal reg r -> raise (FoundPrefix pfx)
    | Ityreg r when reg_r_occurs reg r ->
        let sbs = its_match_regs r.reg_its r.reg_args r.reg_regs in
        List.iter (fun fd -> let ity = ity_full_inst sbs fd.pv_ity in
          find_prefix (fd::pfx) reg ity) r.reg_its.its_mfields;
        raise (FoundPrefix (unknown::pfx))
    | _ when ity_r_occurs reg ity ->
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
  let print_raise fmt (reg,cvr) =
    let print_cvr fmt reg = print_pfx reg fmt (find_prefix reg) in
    if Sreg.is_empty cvr then print_pfx reg fmt (find_prefix reg) else
      fprintf fmt "%a@ (under %a)" (print_pfx reg) (find_prefix reg)
        (Pp.print_list Pp.comma print_cvr) (Sreg.elements cvr) in
  let print_result fmt ity = fprintf fmt " :@ %a" print_ity ity in
  let print_pre fmt p = fprintf fmt "@\nrequires { @[%a@] }" print_term p in
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
  if not (Spv.is_empty eff.eff_reads) then fprintf fmt "@\nreads  { %a }"
    (Pp.print_list Pp.comma print_pv) (Spv.elements eff.eff_reads);
  if not (Mreg.is_empty eff.eff_writes) then fprintf fmt "@\nwrites { %a }"
    (Pp.print_list Pp.comma print_write) (Mreg.bindings eff.eff_writes);
  if not (Mreg.is_empty eff.eff_covers) then fprintf fmt "@\ncovers { %a }"
    (Pp.print_list Pp.comma print_raise) (Mreg.bindings eff.eff_covers);
  Pp.print_list Pp.nothing print_pre fmt pre;
  Pp.print_list Pp.nothing print_post fmt post;
  Pp.print_list Pp.nothing print_xpost fmt (Mexn.bindings xpost)

let print_cty fmt c = print_spec c.cty_args c.cty_pre c.cty_post
  c.cty_xpost c.cty_effect fmt (Some c.cty_result)

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
  | ImpureField ity -> fprintf fmt
      "Field type %a is mutable, it cannot be used in a type which is \
        private, recursive, or has an invariant" print_ity_full ity
(*
  | UnboundException xs -> fprintf fmt
      "This function raises %a but does not specify a post-condition for it"
        print_xs xs
*)
  | TypeMismatch (t1,t2,s) -> fprintf fmt
      "Type mismatch between %a and %a"
        (print_ity_node s 0) t1 print_ity_full t2
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
  | IllegalAlias _reg -> fprintf fmt
      "This application creates an illegal alias"
  | _ -> raise e)
