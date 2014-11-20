(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
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

(** {2 Individual types (first-order types w/o effects)} *)

type itysymbol = {
  its_ts      : tysymbol;       (** pure "snapshot" type symbol *)
  its_private : bool;           (** is a private/abstract type *)
  its_mutable : bool;           (** is a record with mutable fields *)
  its_mfields : pvsymbol list;  (** mutable fields *)
  its_regions : region list;    (** mutable shareable components *)
  its_reg_vis : bool list;      (** non-ghost shareable components *)
  its_arg_vis : bool list;      (** non-ghost type parameters *)
  its_arg_upd : bool list;      (** updatable type parameters *)
  its_def     : ity option;     (** is a type alias *)
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

exception NonUpdatable of itysymbol * ity

let check_its_args s tl =
  assert (s.its_def = None);
  let check_upd acc upd ity =
    if not (upd || ity.ity_pure) then raise (NonUpdatable (s,ity));
    acc && ity.ity_pure in
  List.fold_left2 check_upd true s.its_arg_upd tl

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
  | Ityvar v -> fn acc v
  | _ -> ity_fold (ity_v_fold fn) Util.const acc ity

let reg_v_fold fn acc r = List.fold_left (ity_v_fold fn) acc r.reg_args

let ity_freevars s ity = ity_v_fold (fun s v -> Stv.add v s) s ity

let ity_v_occurs tv ity = Util.any ity_v_fold (tv_equal tv) ity

let ity_closed ity = Util.all ity_v_fold Util.ffalse ity

let rec ity_r_fold fn acc ity = ity_fold (ity_r_fold fn) fn acc ity
let     reg_r_fold fn acc reg = reg_fold (ity_r_fold fn) fn acc reg

let rec reg_r_occurs reg r =
  reg_equal r reg ||
    Util.any reg_r_fold (reg_r_occurs reg) r

let rec reg_r_stale reg cvr r =
  reg_equal r reg || (not (Sreg.mem r cvr) &&
    Util.any reg_r_fold (reg_r_stale reg cvr) r)

let ity_r_occurs reg ity = Util.any ity_r_fold (reg_r_occurs reg) ity

let ity_r_stale reg cvr ity = Util.any ity_r_fold (reg_r_stale reg cvr) ity

let ity_immutable ity = ity.ity_pure

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
  | Ityvar tv -> fnv acc tv

and reg_visible fnv fnr acc vis r =
  if not vis then acc else
  dfold2 (ity_visible fnv fnr) (reg_visible fnv fnr)
    (fnr acc r) r.reg_its.its_arg_vis r.reg_args
                r.reg_its.its_reg_vis r.reg_regs

let ity_r_visible regs ity =
  ity_visible Util.const (fun s r -> Sreg.add r s) regs true ity

let ity_v_visible vars ity =
  ity_visible (fun s v -> Stv.add v s) Util.const vars true ity

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
exception RegionMismatch of region * region * ity_subst

let ity_equal_check t1 t2 =
  if not (ity_equal t1 t2) then raise (TypeMismatch (t1,t2,isb_empty))

let reg_equal_check r1 r2 =
  if not (reg_equal r1 r2) then raise (RegionMismatch (r1,r2,isb_empty))

let ity_full_inst sbs ity =
  let freg r = Mreg.find r sbs.isb_reg in
  let rec inst ity = match ity.ity_node with
    | Ityapp (s,tl,rl) ->
        ity_app_unsafe s (List.map inst tl) (List.map freg rl)
    | Itypur (s,tl) -> ity_pur_unsafe s (List.map inst tl)
    | Ityvar v -> Mtv.find v sbs.isb_tv
    | Ityreg r -> ity_reg (freg r) in
  if ity_immutable ity && ity_closed ity then ity else inst ity

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
  with Exit -> raise (RegionMismatch (reg1,reg2,sbs))

let ity_freeze sbs ity = ity_match sbs ity ity
let reg_freeze sbs reg = reg_match sbs reg reg

let rec ty_of_ity ity = match ity.ity_node with
  | Ityvar v -> ty_var v
  | Itypur (s,tl) | Ityapp (s,tl,_)
  | Ityreg {reg_its = s; reg_args = tl} ->
      ty_app s.its_ts (List.map ty_of_ity tl)

let rec ity_purify ity = match ity.ity_node with
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
  | Some ity ->
      ity_full_inst sbs (ity_purify ity)
  | None ->
      ity_pur_unsafe s tl

let create_region sbs id s tl rl = match s.its_def with
  | Some { ity_node = Ityreg r } ->
      let tl = List.map (ity_full_inst sbs) r.reg_args in
      let rl = List.map (reg_full_inst sbs) r.reg_regs in
      mk_reg id r.reg_its tl rl
  | None when s.its_mutable ->
      mk_reg id s tl rl
  | _ -> invalid_arg "Ity.create_region"

let ity_app sbs s tl rl =
  if s.its_mutable then
    ity_reg (create_region sbs (id_fresh "rho") s tl rl)
  else match s.its_def with
  | Some ity ->
      ity_full_inst sbs ity
  | None when rl = [] ->
      ity_pur_unsafe s tl
  | None ->
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

let create_itysymbol_unsafe, restore_its =
  let ts_to_its = Wts.create 17 in
  (fun ~ts ~pri ~mut ~fld ~regs ~rvis ~avis ~aupd ~def ->
    let its = {
      its_ts      = ts;
      its_private = pri;
      its_mutable = mut;
      its_mfields = fld;
      its_regions = regs;
      its_reg_vis = rvis;
      its_arg_vis = avis;
      its_arg_upd = aupd;
      its_def     = def;
    } in
    Wts.set ts_to_its ts its;
    its),
  (fun ts -> Wts.find ts_to_its ts)

let create_itysymbol name args pri mut regs fld def =
  let exn = Invalid_argument "Ity.create_itysymbol" in
  (* prepare arguments *)
  let args, avis, aupd =
    List.fold_right (fun (tv,v,u) (args,avis,aupd) ->
      tv::args, v::avis, u::aupd) args ([],[],[]) in
  let regs, rvis = List.split regs in
  let fld = Spv.elements fld in
  (* create_tysymbol checks that [args] has no duplicates
     and covers every type variable in [def] *)
  let ts = create_tysymbol name args (Opt.map ty_of_ity def) in
  (* all regions *)
  let add_r s r = Sreg.add_new (DuplicateRegion r) r s in
  let sregs = List.fold_left add_r Sreg.empty regs in
  (* all type variables *)
  let sargs = List.fold_right Stv.add args Stv.empty in
  (* each type variable in [regs] must be in [args] *)
  let check_v ity = ity_v_fold (fun () v ->
    if not (Stv.mem v sargs) then raise (UnboundTypeVar v)) () ity in
  List.iter (fun r -> List.iter check_v r.reg_args) regs;
  (* each type variable in [fld] must be in [args],
     and each top region in [fld] must be in [regs] *)
  let check_r ity = ity_r_fold (fun () r ->
    if not (Sreg.mem r sregs) then raise (UnboundRegion r)) () ity in
  List.iter (fun f -> check_v f.pv_ity; check_r f.pv_ity) fld;
  (* top regions in [def] must be exactly [regs],
     and [def] is mutable if and only if the symbol is *)
  let dregs = let add_r s r = Sreg.add r s in match def with
    | Some {ity_node = Ityreg reg} when mut ->
                               reg_r_fold add_r Sreg.empty reg
    | Some ity when not mut -> ity_r_fold add_r Sreg.empty ity
    | Some _ -> raise exn
    | None -> sregs in
  if not (Sreg.equal sregs dregs) then if Sreg.subset sregs dregs
    then raise (UnboundRegion (Sreg.choose (Sreg.diff dregs sregs)))
    else raise exn;
  (* if we have mutable fields then we are mutable *)
  if fld <> [] && not mut then raise exn;
  (* if we are an alias then we are not private and have no fields *)
  if def <> None && (pri || fld <> []) then raise exn;
  (* if we are private, [regs] is Nil and [args] are non-updateble *)
  if pri && (regs <> [] || List.exists (fun u -> u) aupd) then raise exn;
  (* updatable type variables are updatable in [def], [regs], and [fld] *)
  let v_updatable = List.fold_left2 (fun s upd v ->
    if upd then Stv.add v s else s) Stv.empty aupd args in
  let check_v () v = if Stv.mem v v_updatable then raise exn in
  let rec nu_ity upd ity = match ity.ity_node with
    | _ when not upd -> ity_v_fold check_v () ity
    | Ityreg {reg_its = s; reg_args = tl}
    | Ityapp (s,tl,_) | Itypur (s,tl) -> nu_its s tl
    | Ityvar _ -> ()
  and nu_its s tl = List.iter2 nu_ity s.its_arg_upd tl in
  Opt.iter (nu_ity true) def;
  List.iter (fun r -> nu_its r.reg_its r.reg_args) regs;
  List.iter (fun f -> nu_ity true f.pv_ity) fld;
  (* invisible type variables and regions are invisible in [def],
     in the visible regions, and in the non-ghost mutable fields *)
  let v_invisible = List.fold_left2 (fun s vis v ->
    if vis then s else Stv.add v s) Stv.empty avis args in
  let r_invisible = List.fold_left2 (fun s vis r ->
    if vis then s else Sreg.add r s) Sreg.empty rvis regs in
  let check_v () v = if Stv.mem v v_invisible then raise exn in
  let check_r () r = if Sreg.mem r r_invisible then raise exn in
  Opt.iter (ity_visible check_v check_r () true) def;
  List.iter2 (reg_visible check_v check_r ()) rvis regs;
  List.iter (fun f ->
    ity_visible check_v check_r () (not f.pv_ghost) f.pv_ity) fld;
  (* NOTE: record/constructor fields must be pairwise separated, but this
     should be checked during the type declaration, [fld] is not enough *)
  create_itysymbol_unsafe ~ts ~pri ~mut ~fld ~regs ~rvis ~avis ~aupd ~def

let rec ity_of_ty ty = match ty.ty_node with
  | Tyvar v -> ity_var v
  | Tyapp (s,tl) ->
      let s = try restore_its s with Not_found ->
        invalid_arg "Ity.ity_of_ty" in
      ity_pur_unsafe s (List.map ity_of_ty tl)

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

let its_int = create_itysymbol_unsafe
    ~ts:ts_int ~pri:false ~mut:false ~fld:[]
    ~regs:[] ~rvis:[] ~avis:[] ~aupd:[] ~def:None

let its_real = create_itysymbol_unsafe
    ~ts:ts_real ~pri:false ~mut:false ~fld:[]
    ~regs:[] ~rvis:[] ~avis:[] ~aupd:[] ~def:None

let its_bool = create_itysymbol_unsafe
    ~ts:ts_bool ~pri:false ~mut:false ~fld:[]
    ~regs:[] ~rvis:[] ~avis:[] ~aupd:[] ~def:None

let its_func = create_itysymbol_unsafe
    ~ts:ts_func ~pri:false ~mut:false ~fld:[]
    ~regs:[] ~rvis:[] ~avis:[true;true] ~aupd:[false;false] ~def:None

let its_pred = create_itysymbol_unsafe
    ~ts:ts_pred ~pri:false ~mut:false ~fld:[]
    ~regs:[] ~rvis:[] ~avis:[true] ~aupd:[false]
    ~def:(Opt.map ity_of_ty ts_pred.ts_def)

let ity_int  = ity_pur its_int  []
let ity_real = ity_pur its_real []
let ity_bool = ity_pur its_bool []

let ity_func a b = ity_pur its_func [a;b]
let ity_pred a   = ity_pur its_pred [a]

let its_tuple = Hint.memo 17 (fun n ->
  let ts = ts_tuple n in
  let ll = List.map (fun _ -> true) ts.ts_args in
  create_itysymbol_unsafe
    ~ts:ts ~pri:false ~mut:false ~fld:[]
    ~regs:[] ~rvis:[] ~avis:ll ~aupd:ll ~def:None)

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

exception PolymorphicException of ident * ity
exception MutableException of ident * ity

let xs_equal : xsymbol -> xsymbol -> bool = (==)
let xs_hash xs = id_hash xs.xs_name
let xs_compare xs1 xs2 = id_compare xs1.xs_name xs2.xs_name

let create_xsymbol id ity =
  let id = id_register id in
  if not (ity_closed ity) then raise (PolymorphicException (id, ity));
  if not (ity_immutable ity) then raise (MutableException (id, ity));
  { xs_name = id; xs_ity = ity; }

module Exn = MakeMSH (struct
  type t = xsymbol
  let tag xs = Weakhtbl.tag_hash xs.xs_name.id_tag
end)

module Sexn = Exn.S
module Mexn = Exn.M

(* effects *)

type effect = {
  eff_writes : Spv.t Mreg.t;
  eff_resets : Sreg.t Mreg.t;
  eff_raises : Sexn.t;
  eff_diverg : bool;
}

let eff_empty = {
  eff_writes = Mreg.empty;
  eff_resets = Mreg.empty;
  eff_raises = Sexn.empty;
  eff_diverg = false;
}

let eff_is_empty e =
  Mreg.is_empty e.eff_writes &&
  Mreg.is_empty e.eff_resets &&
  Sexn.is_empty e.eff_raises &&
  not e.eff_diverg

let eff_is_pure e =
  Mreg.is_empty e.eff_writes &&
  Sexn.is_empty e.eff_raises &&
  not e.eff_diverg

let eff_equal e1 e2 =
  Mreg.equal Spv.equal e1.eff_writes e2.eff_writes &&
  Mreg.equal Sreg.equal e1.eff_resets e2.eff_resets &&
  Sexn.equal e1.eff_raises e2.eff_raises &&
  e1.eff_diverg = e2.eff_diverg

let merge_fields _ f1 f2 = Some (Spv.union f1 f2)

let merge_covers reg c1 c2 = Some (Sreg.union
  (Sreg.filter (fun r -> not (reg_r_stale reg c1 r)) c2)
  (Sreg.filter (fun r -> not (reg_r_stale reg c2 r)) c1))

let eff_union x y = {
  eff_writes = Mreg.union merge_fields x.eff_writes y.eff_writes;
  eff_resets = Mreg.union merge_covers x.eff_resets y.eff_resets;
  eff_raises = Sexn.union x.eff_raises y.eff_raises;
  eff_diverg = x.eff_diverg || y.eff_diverg;
}

let eff_write e r f =
  begin match f with
    | Some f when List.memq f r.reg_its.its_mfields -> ()
    | None -> ()
    | _ -> invalid_arg "Ity.eff_write"
  end;
  let add fs = match f, fs with
    | Some f, Some fs -> Some (Spv.add f fs)
    | Some f, None    -> Some (Spv.singleton f)
    | None,   Some fs -> Some fs
    | None,   None    -> Some Spv.empty in
  { e with eff_writes = Mreg.change add r e.eff_writes }

let eff_raise e x = { e with eff_raises = Sexn.add x e.eff_raises }
let eff_catch e x = { e with eff_raises = Sexn.remove x e.eff_raises }
let eff_reset e r = { e with eff_resets = Mreg.add r Sreg.empty e.eff_resets }
let eff_diverge e = { e with eff_diverg = true }

exception AssignPrivate of region

(* freeze type variables and regions outside modified fields *)
let freeze_of_writes wr =
  let freeze_of_write r fs frz =
    let frz = List.fold_left ity_freeze frz r.reg_args in
    let freeze_unhit frz r reg =
      (* fields are unaliased in [s], therefore if region [r] from
          [s.its_regions] occurs in [f.pv_ity], it cannot occur in
          any other field of [s], and therefore [reg] doesn't need
          to be frozen. If [reg] or subregions of [reg] are aliased
          with other fields of the modified value, they will occur
          in the instances of other regions in [s.its_regions], and
          will be frozen there. *)
      let hit f _ = ity_r_occurs r f.pv_ity in
      if Mpv.exists hit fs then frz else reg_freeze frz reg in
    List.fold_left2 freeze_unhit frz r.reg_its.its_regions r.reg_regs in
  Mreg.fold freeze_of_write wr isb_empty

let eff_assign e asl =
  let seen, e = List.fold_left (fun (seen,e) (r,f,ity) ->
    if r.reg_its.its_private then raise (AssignPrivate r);
    if not (List.memq f r.reg_its.its_mfields) then
      invalid_arg "Ity.eff_assign";
    let seen = Mreg.change (fun fs -> Some (match fs with
      | Some fs -> Mpv.add_new (Invalid_argument "Ity.eff_assign") f ity fs
      | None    -> Mpv.singleton f ity)) r seen in
    seen, eff_write e r (Some f)) (Mreg.empty, e) asl in
  (* type variables and regions outside modified fields are frozen *)
  let frz = freeze_of_writes seen in
  (* non-frozen regions are allowed to be renamed, preserving aliases *)
  let sbst, sbsf = Mreg.fold (fun r fs acc ->
    let sbs = its_match_regs r.reg_its r.reg_args r.reg_regs in
    (* TODO: catch the TypeMismatch exception and produce a reasonable
       error message *)
    Mpv.fold (fun pv ity (sbst,sbsf) ->
      let fity = ity_full_inst sbs pv.pv_ity in
      ity_match sbst fity ity,
      ity_match sbsf ity fity) fs acc) seen (frz,frz) in
  let sbst, sbsf = sbst.isb_reg, sbsf.isb_reg in
  (* every non-instantiated right-hand side region is reset *)
  let rst = Mreg.set_diff sbsf sbst in
  let e = Mreg.fold (fun r _ e -> eff_reset e r) rst e in
  (* every LHS region not instantiated to itself is refreshed *)
  let rfr = Mreg.mapi_filter (fun ro rn ->
    if reg_equal ro rn then None else
    Some (Mreg.mapi_filter (fun r _ ->
      if reg_r_occurs ro r then Some () else None) seen)) sbst in
  { e with eff_resets = Mreg.union merge_covers e.eff_resets rfr }

let refresh_of_effect ({eff_writes = wr} as e) =
  let freeze r _ sbs = reg_freeze sbs r in
  let sbs = Mreg.fold freeze wr isb_empty in
  let frz = (freeze_of_writes wr).isb_reg in
  let rfr = Mreg.set_diff sbs.isb_reg frz in
  let rfr = Mreg.map (fun ro ->
    Mreg.mapi_filter (fun r _ ->
      if reg_r_occurs ro r then Some () else None) wr) rfr in
  { e with eff_resets = Mreg.union merge_covers e.eff_resets rfr }

exception IllegalAlias of region

let eff_full_inst sbs e =
  (* all modified or reset regions in e must be instantiated
     into distinct regions. We allow regions that are not
     affected directly to be aliased, even if they contain
     modified or reset subregions - the values are still
     updated at the same program points and with the same
     postconditions, as in the initial verified code. *)
  let inst fn src = Mreg.fold (fun r v acc ->
    let r = reg_full_inst sbs r in
    Mreg.add_new (IllegalAlias r) r (fn v) acc) src Mreg.empty in
  let writes = inst (fun fld -> fld) e.eff_writes in
  let resets = inst (inst (fun () -> ())) e.eff_resets in
  let impact = Mreg.merge (fun r fld cvr -> match fld, cvr with
    | Some _, Some _ -> raise (IllegalAlias r)
    | _ -> Some ()) writes resets in
  (* all type variables must be instantiated into types that
     are not affected by the effect. *)
  let check_v _ dst = Sreg.iter (fun r ->
    if ity_r_occurs r dst then raise (IllegalAlias r)) impact in
  Mtv.iter check_v sbs.isb_tv;
  (* all unaffected regions must be instantiated into regions
     outside [impact].

     Now, every region in the instantiated execution is either
     brought in by the type substitution and thus is unaffected,
     or instantiates one of the original regions and is affected
     if and only if the original one is. *)
  let check_r r dst =
    if not (Mreg.mem r e.eff_writes) &&
       not (Mreg.mem r e.eff_resets) &&
            Sreg.mem dst impact
    then raise (IllegalAlias dst) in
  Mreg.iter check_r sbs.isb_reg;
  { e with eff_writes = writes; eff_resets = resets }

let eff_stale_region eff ity =
  Mreg.exists (fun r c -> ity_r_stale r c ity) eff.eff_resets

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
  cty_reads  : Spv.t;
  cty_effect : effect;
  cty_result : ity;
  cty_freeze : ity_subst;
}

let cty_unsafe args pre post xpost reads effect result freeze = {
  cty_args   = args;
  cty_pre    = pre;
  cty_post   = post;
  cty_xpost  = xpost;
  cty_reads  = reads;
  cty_effect = effect;
  cty_result = result;
  cty_freeze = freeze;
}

let spec_t_fold fn_t acc pre post xpost =
  let fn_l a fl = List.fold_left fn_t a fl in
  let acc = fn_l (fn_l acc pre) post in
  Mexn.fold (fun _ l a -> fn_l a l) xpost acc

let check_tvs reads args result pre post xpost =
  (* every type variable in spec comes either from a known vsymbol
     or from the result type. We need this to ensure that we always
     can do a full instantiation. TODO: do we really need this? *)
  let add_pv v s = ity_freevars s v.pv_ity in
  let tvs = ity_freevars Stv.empty result in
  let tvs = List.fold_right add_pv args tvs in
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

let create_cty args pre post xpost reads effect result =
  let exn = Invalid_argument "Ity.create_cty" in
  (* pre, post, and xpost are well-typed *)
  check_pre pre; check_post exn result post;
  Mexn.iter (fun xs xq -> check_post exn xs.xs_ity xq) xpost;
  (* the arguments must be pairwise distinct *)
  let sarg = List.fold_right (Spv.add_new exn) args Spv.empty in
  (* remove args from reads and freeze the external context *)
  let reads = spec_t_fold t_freepvs reads pre post xpost in
  let reads = Spv.diff reads sarg in
  let freeze = Spv.fold freeze_pv reads isb_empty in
  check_tvs reads args result pre post xpost;
  (* remove exceptions whose postcondition is False *)
  let is_false _ xq = List.exists (t_equal t_false) xq in
  let nothrow = Mexn.filter is_false xpost in
  let xpost = Mexn.set_diff xpost nothrow in
  let raises = Mexn.set_diff effect.eff_raises nothrow in
  let effect = { effect with eff_raises = raises } in
  (* remove effects on unknown regions *)
  let known = (Spv.fold freeze_pv sarg freeze).isb_reg in
  let filter m = Mreg.set_inter m known in
  let effect = { effect with
    eff_writes = filter effect.eff_writes;
    eff_resets = Mreg.map filter (filter effect.eff_resets) } in
  (* reset every fresh region in the result *)
  let frzres = ity_freeze isb_empty result in
  let fresh = Mreg.set_diff frzres.isb_reg known in
  let resets = Mreg.map (Util.const Sreg.empty) fresh in
  let resets = Mreg.union merge_covers effect.eff_resets resets in
  let effect = { effect with eff_resets = resets } in
  cty_unsafe args pre post xpost reads effect result freeze

let t_ty_subst_l tsb vsb l = List.map (fun t -> t_ty_subst tsb vsb t) l
let t_subst_l        vsb l = List.map (fun t -> t_subst        vsb t) l

let cty_apply c pvl args res =
  let rec apply isb same gh vsb al vl = match al, vl with
    | a::al, v::vl when v.pv_ghost || not a.pv_ghost ->
        let isb = ity_match isb a.pv_ity v.pv_ity in
        let same = same && ity_equal a.pv_ity v.pv_ity in
        let gh = gh || (v.pv_ghost && not a.pv_ghost) in
        let vsb = Mvs.add a.pv_vs (t_var v.pv_vs) vsb in
        apply isb same gh vsb al vl
    | al, [] when List.length al = List.length args ->
        let freeze = if same (*so far*) then isb else
          List.fold_right freeze_pv pvl c.cty_freeze in
        let same = same && ity_equal c.cty_result res &&
          List.for_all2 (fun a t -> ity_equal a.pv_ity t) al args in
        if same && pvl = [] then gh, c else
        let eff, subst_l =
          if same then c.cty_effect, t_subst_l else
          let isb = List.fold_left2 (fun s a ity ->
            ity_match s a.pv_ity ity) isb al args in
          let isb = ity_match isb c.cty_result res in
          let eff = eff_full_inst isb c.cty_effect in
          let check v t = match t.ity_node with
            | Ityvar u -> tv_equal u v | _ -> false in
          eff, if Mtv.for_all check isb.isb_tv then t_subst_l
            else t_ty_subst_l (Mtv.map ty_of_ity isb.isb_tv) in
        let args = List.map2 (fun {pv_vs = vs; pv_ghost = ghost} t ->
          create_pvsymbol (id_clone vs.vs_name) ~ghost t) al args in
        let vsb = List.fold_left2 (fun m a v ->
          Mvs.add a.pv_vs (t_var v.pv_vs) m) vsb al args in
        let p = subst_l vsb c.cty_pre and q = subst_l vsb c.cty_post in
        let xq = Mexn.map (fun xqfl -> subst_l vsb xqfl) c.cty_xpost in
        let rds = List.fold_right Spv.add pvl c.cty_reads in
        gh, cty_unsafe args p q xq rds eff res freeze
    | _ ->
        invalid_arg "Ity.cty_apply" in
  apply c.cty_freeze true false Mvs.empty c.cty_args pvl

let cty_add_reads c pvs =
  (* the external reads are already frozen and
     the arguments should stay instantiable *)
  let pvs = Spv.diff pvs c.cty_reads in
  let pvs = List.fold_right Spv.remove c.cty_args pvs in
  { c with cty_reads  = Spv.union c.cty_reads pvs;
           cty_freeze = Spv.fold freeze_pv pvs c.cty_freeze }

let cty_add_pre c pre =
  check_pre pre;
  let c = cty_add_reads c (List.fold_left t_freepvs Spv.empty pre) in
  check_tvs c.cty_reads c.cty_args c.cty_result pre [] Mexn.empty;
  { c with cty_pre = pre @ c.cty_pre }

let cty_add_post c post =
  check_post (Invalid_argument "Ity.cty_add_post") c.cty_result post;
  let c = cty_add_reads c (List.fold_left t_freepvs Spv.empty post) in
  check_tvs c.cty_reads c.cty_args c.cty_result [] post Mexn.empty;
  { c with cty_post = post @ c.cty_post }

let cty_pop_post c = match c.cty_post with
  | [] -> invalid_arg "Ity.cty_pop_post"
  | _::post -> { c with cty_post = post }
