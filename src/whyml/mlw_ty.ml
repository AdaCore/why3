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

(** value types (w/o effects) *)

module rec T : sig

  type varset = {
    vars_tv  : Stv.t;
    vars_reg : Reg.S.t;
  }

  type itysymbol = {
    its_ts   : tysymbol;
    its_regs : region list;
    its_def  : ity option;
    its_ghrl : bool list;
    its_inv  : bool;
    its_abst : bool;
    its_priv : bool;
  }

  and ity = {
    ity_node : ity_node;
    ity_vars : varset;
    ity_tag  : Weakhtbl.tag;
  }

  and ity_node =
    | Ityvar of tvsymbol
    | Itypur of tysymbol * ity list
    | Ityapp of itysymbol * ity list * region list

  and region = {
    reg_name : ident;
    reg_ity  : ity;
  }

end = struct

  type varset = {
    vars_tv  : Stv.t;
    vars_reg : Reg.S.t;
  }

  type itysymbol = {
    its_ts   : tysymbol;
    its_regs : region list;
    its_def  : ity option;
    its_ghrl : bool list;
    its_inv  : bool;
    its_abst : bool;
    its_priv : bool;
  }

  and ity = {
    ity_node : ity_node;
    ity_vars : varset;
    ity_tag  : Weakhtbl.tag;
  }

  and ity_node =
    | Ityvar of tvsymbol
    | Itypur of tysymbol * ity list
    | Ityapp of itysymbol * ity list * region list

  and region = {
    reg_name : ident;
    reg_ity  : ity;
  }

end

and Reg : sig
  module M : Extmap.S with type key = T.region
  module S : Extset.S with module M = M
  module H : Exthtbl.S with type key = T.region
  module W : Weakhtbl.S with type key = T.region
end = MakeMSHW (struct
  type t = T.region
  let tag r = r.T.reg_name.id_tag
end)

open T

(** regions *)

module Sreg = Reg.S
module Mreg = Reg.M
module Hreg = Reg.H
module Wreg = Reg.W

let reg_equal : region -> region -> bool = (==)
let reg_hash r = id_hash r.reg_name

let create_region id ty = { reg_name = id_register id; reg_ity = ty }

(* variable sets *)

let vars_empty = { vars_tv = Stv.empty ; vars_reg = Sreg.empty }

let vars_union s1 s2 = {
  vars_tv  = Stv.union s1.vars_tv s2.vars_tv;
  vars_reg = Sreg.union s1.vars_reg s2.vars_reg;
}

(* value type symbols *)

module Itsym = MakeMSHW (struct
  type t = itysymbol
  let tag its = its.its_ts.ts_name.id_tag
end)

module Sits = Itsym.S
module Mits = Itsym.M
module Hits = Itsym.H
module Wits = Itsym.W

let its_equal : itysymbol -> itysymbol -> bool = (==)
let ity_equal : ity       -> ity       -> bool = (==)

let its_hash its = id_hash its.its_ts.ts_name
let ity_hash ity = Weakhtbl.tag_hash ity.ity_tag

module Hsity = Hashcons.Make (struct
  type t = ity

  let equal ity1 ity2 = match ity1.ity_node, ity2.ity_node with
    | Ityvar n1, Ityvar n2 ->
        tv_equal n1 n2
    | Itypur (s1,l1), Itypur (s2,l2) ->
        ts_equal s1 s2 && List.for_all2 ity_equal l1 l2
    | Ityapp (s1,l1,r1), Ityapp (s2,l2,r2) ->
        its_equal s1 s2 && List.for_all2 ity_equal l1 l2
          && List.for_all2 reg_equal r1 r2
    | _ ->
        false

  let hash ity = match ity.ity_node with
    | Ityvar v -> tv_hash v
    | Itypur (s,tl) -> Hashcons.combine_list ity_hash (ts_hash s) tl
    | Ityapp (s,tl,rl) ->
        Hashcons.combine_list reg_hash
          (Hashcons.combine_list ity_hash (its_hash s) tl) rl

  let ity_vars s ity = vars_union s ity.ity_vars
  let reg_vars s r = { s with vars_reg = Sreg.add r s.vars_reg }

  let vars ity = match ity.ity_node with
    | Ityvar v ->
        { vars_tv = Stv.singleton v; vars_reg = Sreg.empty }
    | Itypur (_,tl) ->
        List.fold_left ity_vars vars_empty tl
    | Ityapp (_,tl,rl) ->
        List.fold_left reg_vars (List.fold_left ity_vars vars_empty tl) rl

  let tag n ity = { ity with
    ity_vars = vars ity;
    ity_tag  = Weakhtbl.create_tag n }

end)

module Ity = MakeMSHW (struct
  type t = ity
  let tag ity = ity.ity_tag
end)

module Sity = Ity.S
module Mity = Ity.M
module Hity = Ity.H
module Wity = Ity.W

let mk_ity n = {
  ity_node = n;
  ity_vars = vars_empty;
  ity_tag  = Weakhtbl.dummy_tag;
}

let ity_var n = Hsity.hashcons (mk_ity (Ityvar n))
let ity_pur_unsafe s tl = Hsity.hashcons (mk_ity (Itypur (s,tl)))
let ity_app_unsafe s tl rl = Hsity.hashcons (mk_ity (Ityapp (s,tl,rl)))

(* generic traversal functions *)

let ity_map fn ity = match ity.ity_node with
  | Ityvar _ -> ity
  | Itypur (f,tl) -> ity_pur_unsafe f (List.map fn tl)
  | Ityapp (f,tl,rl) -> ity_app_unsafe f (List.map fn tl) rl

let ity_fold fn acc ity = match ity.ity_node with
  | Ityvar _ -> acc
  | Itypur (_,tl)
  | Ityapp (_,tl,_) -> List.fold_left fn acc tl

let ity_all pr ity = Util.all ity_fold pr ity
let ity_any pr ity = Util.any ity_fold pr ity

(* symbol-wise map/fold *)

let rec ity_s_fold fn fts acc ity = match ity.ity_node with
  | Ityvar _ -> acc
  | Itypur (ts, tl) -> List.fold_left (ity_s_fold fn fts) (fts acc ts) tl
  | Ityapp (f, tl, rl) ->
      let acc = List.fold_left (ity_s_fold fn fts) (fn acc f) tl in
      List.fold_left (fun acc r -> ity_s_fold fn fts acc r.reg_ity) acc rl

let ity_s_all pr pts ity = Util.alld ity_s_fold pr pts ity
let ity_s_any pr pts ity = Util.anyd ity_s_fold pr pts ity

(* traversal functions on type variables and regions *)

let rec ity_v_map fnv fnr ity = match ity.ity_node with
  | Ityvar v ->
      fnv v
  | Itypur (f,tl) ->
      ity_pur_unsafe f (List.map (ity_v_map fnv fnr) tl)
  | Ityapp (f,tl,rl) ->
      ity_app_unsafe f (List.map (ity_v_map fnv fnr) tl) (List.map fnr rl)

let ity_subst_unsafe mv mr ity =
  ity_v_map (fun v -> Mtv.find v mv) (fun r -> Mreg.find r mr) ity

let ity_closed ity = Stv.is_empty ity.ity_vars.vars_tv
let ity_immutable ity = Sreg.is_empty ity.ity_vars.vars_reg

let rec ity_has_inv ity = match ity.ity_node with
  | Ityapp (its,_,_) -> its.its_inv || ity_any ity_has_inv ity
  | _ -> ity_any ity_has_inv ity

let rec reg_fold fn vars acc =
  let on_reg r acc = reg_fold fn r.reg_ity.ity_vars (fn r acc) in
  Sreg.fold on_reg vars.vars_reg acc

let rec reg_all fn vars =
  let on_reg r = fn r && reg_all fn r.reg_ity.ity_vars in
  Sreg.for_all on_reg vars.vars_reg

let rec reg_any fn vars =
  let on_reg r = fn r || reg_any fn r.reg_ity.ity_vars in
  Sreg.exists on_reg vars.vars_reg

let rec reg_iter fn vars =
  let on_reg r = fn r; reg_iter fn r.reg_ity.ity_vars in
  Sreg.iter on_reg vars.vars_reg

let reg_occurs r vars = reg_any (reg_equal r) vars

(* detect non-ghost type variables and regions *)

let rec fold_nonghost on_reg acc ity =
  let fn = fold_nonghost on_reg in
  if ity_immutable ity then acc
  else match ity.ity_node with
  | Ityvar _ -> acc
  | Itypur (_,tl) ->
      List.fold_left fn acc tl
  | Ityapp ({ its_ghrl = ghrl },tl,rl) ->
      let acc = List.fold_left fn acc tl in
      List.fold_left2 (fun s gh ({ reg_ity = ity } as r) ->
        if gh then s else fn (on_reg r s) ity) acc ghrl rl

let ity_nonghost_reg regs ity = fold_nonghost Sreg.add regs ity

let lookup_nonghost_reg regs ity =
  if reg_any (fun r -> Sreg.mem r regs) ity.ity_vars
  then try fold_nonghost (fun r acc ->
    if Sreg.mem r regs then raise Util.FoldSkip else acc) false ity
  with Util.FoldSkip -> true
  else false

(* smart constructors *)

exception BadItyArity of itysymbol * int
exception BadRegArity of itysymbol * int

exception DuplicateRegion of region
exception UnboundRegion of region

type ity_subst = {
  ity_subst_tv  : ity Mtv.t;
  ity_subst_reg : region Mreg.t; (* must preserve ghost-ness *)
}

let ity_subst_empty = {
  ity_subst_tv  = Mtv.empty;
  ity_subst_reg = Mreg.empty;
}

exception RegionMismatch of region * region * ity_subst
exception TypeMismatch of ity * ity * ity_subst

let ity_equal_check ty1 ty2 =
  if not (ity_equal ty1 ty2) then raise (TypeMismatch (ty1,ty2,ity_subst_empty))

let reg_equal_check r1 r2 =
  if not (reg_equal r1 r2) then raise (RegionMismatch (r1,r2,ity_subst_empty))

let reg_full_inst s r = Mreg.find r s.ity_subst_reg

let ity_full_inst s ity =
  if ity_closed ity && ity_immutable ity then ity
  else ity_subst_unsafe s.ity_subst_tv s.ity_subst_reg ity

let rec ity_match s ity1 ity2 =
  let set = function
    | None -> Some ity2
    | Some ity3 as r when ity_equal ity3 ity2 -> r
    | _ -> raise Exit
  in
  match ity1.ity_node, ity2.ity_node with
  | Ityapp (s1, l1, r1), Ityapp (s2, l2, r2) when its_equal s1 s2 ->
      let s = List.fold_left2 ity_match s l1 l2 in
      List.fold_left2 reg_match s r1 r2
  | Itypur (s1, l1), Itypur (s2, l2) when ts_equal s1 s2 ->
      List.fold_left2 ity_match s l1 l2
  | Ityvar tv1, _ ->
      { s with ity_subst_tv = Mtv.change set tv1 s.ity_subst_tv }
  | _ ->
      raise Exit

and reg_match s r1 r2 =
  let is_new = ref false in
  let set = function
    | None -> is_new := true; Some r2
    | Some r3 as r when reg_equal r3 r2 -> r
    | _ -> raise Exit
  in
  let reg_map = Mreg.change set r1 s.ity_subst_reg in
  let s = { s with ity_subst_reg = reg_map } in
  if !is_new then ity_match s r1.reg_ity r2.reg_ity else s

let ity_match s ity1 ity2 =
  try ity_match s ity1 ity2
  with Exit -> raise (TypeMismatch (ity1,ity2,s))

let reg_match s r1 r2 =
  try reg_match s r1 r2
  with Exit -> raise (RegionMismatch (r1,r2,s))

let rec ty_of_ity ity = match ity.ity_node with
  | Ityvar v -> ty_var v
  | Itypur (s,tl) -> ty_app s (List.map ty_of_ity tl)
  | Ityapp (s,tl,_) -> ty_app s.its_ts (List.map ty_of_ity tl)

let rec ity_of_ty ty = match ty.ty_node with
  | Tyvar v -> ity_var v
  | Tyapp (s,tl) -> ity_pur_unsafe s (List.map ity_of_ty tl)

let rec ity_inst_fresh mv mr ity = match ity.ity_node with
  | Ityvar v ->
      mr, Mtv.find v mv
  | Itypur (s,tl) ->
      let mr,tl = Lists.map_fold_left (ity_inst_fresh mv) mr tl in
      mr, ity_pur_unsafe s tl
  | Ityapp (s,tl,rl) ->
      let mr,tl = Lists.map_fold_left (ity_inst_fresh mv) mr tl in
      let mr,rl = Lists.map_fold_left (reg_refresh mv) mr rl in
      mr, ity_app_unsafe s tl rl

and reg_refresh mv mr r = match Mreg.find_opt r mr with
  | Some r ->
      mr, r
  | None ->
      let mr,ity = ity_inst_fresh mv mr r.reg_ity in
      let id = id_clone r.reg_name in
      let reg = create_region id ity in
      Mreg.add r reg mr, reg

let ity_app_fresh s tl =
  (* type variable map *)
  let mv = try List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty with
    | Invalid_argument _ -> raise (BadItyArity (s, List.length tl)) in
  (* refresh regions *)
  let mr,rl = Lists.map_fold_left (reg_refresh mv) Mreg.empty s.its_regs in
  let sub = { ity_subst_tv = mv; ity_subst_reg = mr } in
  (* every top region in def is guaranteed to be in mr *)
  match s.its_def with
  | Some ity -> ity_full_inst sub ity
  | None -> ity_app_unsafe s tl rl

let ity_app s tl rl =
  (* type variable map *)
  let mv = try List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty with
    | Invalid_argument _ -> raise (BadItyArity (s, List.length tl)) in
  (* region map *)
  let sub = { ity_subst_tv = mv; ity_subst_reg = Mreg.empty } in
  let sub = try List.fold_left2 reg_match sub s.its_regs rl with
    | Invalid_argument _ -> raise (BadRegArity (s, List.length rl)) in
  (* every type var and top region in def are in its_ts.ts_args and its_regs *)
  match s.its_def with
  | Some ity -> ity_full_inst sub ity
  | None -> ity_app_unsafe s tl rl

let ity_pur s tl =
  (* type variable map *)
  let mv = try List.fold_right2 Mtv.add s.ts_args tl Mtv.empty with
    | Invalid_argument _ -> raise (Ty.BadTypeArity (s, List.length tl)) in
  let sub = { ity_subst_tv = mv; ity_subst_reg = Mreg.empty } in
  (* every top region in def is guaranteed to be in mr *)
  match s.ts_def with
  | Alias ty -> ity_full_inst sub (ity_of_ty ty)
  | _ -> ity_pur_unsafe s tl

(* itysymbol creation *)

let create_itysymbol_unsafe, restore_its =
  let ts_to_its = Wts.create 17 in
  (fun ts ~abst ~priv ~inv ~ghrl regs def ->
    let its = {
      its_ts    = ts;
      its_regs  = regs;
      its_def   = def;
      its_ghrl  = ghrl;
      its_inv   = inv;
      its_abst  = abst;
      its_priv  = priv;
    } in
    Wts.set ts_to_its ts its;
    its),
  Wts.find ts_to_its

let create_itysymbol name
      ?(abst=false) ?(priv=false) ?(inv=false) ?(ghost_reg=Sreg.empty)
      args regs def =
  let puredef = match def with
    | Some def -> Alias (ty_of_ity def)
    | None -> NoDef in
  let purets = create_tysymbol name args puredef in
  (* all regions *)
  let add s r = Sreg.add_new (DuplicateRegion r) r s in
  let sregs = List.fold_left add Sreg.empty regs in
  (* all type variables *)
  let sargs = List.fold_right Stv.add args Stv.empty in
  (* all type variables in [regs] must be in [args] *)
  let check dtvs = if not (Stv.subset dtvs sargs) then
    raise (UnboundTypeVar (Stv.choose (Stv.diff dtvs sargs))) in
  List.iter (fun r -> check r.reg_ity.ity_vars.vars_tv) regs;
  (* all regions in [def] must be in [regs] *)
  let check dregs = if not (Sreg.subset dregs sregs) then
    raise (UnboundRegion (Sreg.choose (Sreg.diff dregs sregs))) in
  Opt.iter (fun d -> check d.ity_vars.vars_reg) def;
  (* if a type is an alias then it cannot be abstract or private *)
  if def <> None then begin
    if abst then Loc.errorm "Type aliases cannot be abstract";
    if priv then Loc.errorm "Type aliases cannot be private";
    if inv  then Loc.errorm "Type aliases cannot have invariants"
  end;
  (* every ghost region argument must be in [regs] *)
  if not (Sreg.subset ghost_reg sregs) then
    invalid_arg "Mlw_ty.create_itysymbol";
  Opt.iter (fun ity ->
    let nogh = ity_nonghost_reg Sreg.empty ity in
    if Sreg.exists (fun r -> Sreg.mem r ghost_reg) nogh then
      invalid_arg "Mlw_ty.create_itysymbol") def;
  let ghrl = List.map (fun r -> Sreg.mem r ghost_reg) regs in
  (* create the type symbol *)
  create_itysymbol_unsafe purets ~abst ~priv ~inv ~ghrl regs def

let ts_unit = ts_tuple 0
let ty_unit = ty_tuple []

let ity_int  = ity_of_ty Ty.ty_int
let ity_real = ity_of_ty Ty.ty_real
let ity_bool = ity_of_ty Ty.ty_bool
let ity_unit = ity_of_ty ty_unit

let vars_freeze s =
  let sbs = Stv.fold (fun v -> Mtv.add v (ity_var v)) s.vars_tv Mtv.empty in
  let sbs = { ity_subst_tv = sbs ; ity_subst_reg = Mreg.empty } in
  Sreg.fold (fun r s -> reg_match s r r) s.vars_reg sbs

(** cloning *)

let its_clone sm =
  let itsh = Hits.create 3 in
  let regh = Hreg.create 3 in
  let rec add_ts oits nts =
    let nits = try restore_its nts with Not_found ->
      let abst = oits.its_abst in
      let priv = oits.its_priv in
      let ghrl = oits.its_ghrl in
      let inv  = oits.its_inv in
      let regs = List.map conv_reg oits.its_regs in
      let def  = Opt.map conv_ity oits.its_def in
      create_itysymbol_unsafe nts ~abst ~priv ~inv ~ghrl regs def
    in
    Hits.replace itsh oits nits;
    nits
  and conv_reg r =
    try Hreg.find regh r with Not_found ->
      let ity = conv_ity r.reg_ity in
      let nr = create_region (id_clone r.reg_name) ity in
      Hreg.replace regh r nr;
      nr
  and conv_ity ity = match ity.ity_node with
    | Ityapp (its,tl,rl) ->
        let tl = List.map conv_ity tl in
        let rl = List.map conv_reg rl in
        ity_app (conv_its its) tl rl
    | Itypur (ts,tl) ->
        let tl = List.map conv_ity tl in
        ity_pur (conv_ts ts) tl
    | Ityvar _ -> ity
  and conv_its its =
    try Hits.find itsh its with Not_found ->
      try add_ts its (Mts.find its.its_ts sm.Theory.sm_ts)
      with Not_found -> its
  and conv_ts ts =
    Mts.find_def ts ts sm.Theory.sm_ts
  in
  let add_ts ots nts =
    try ignore (add_ts (restore_its ots) nts)
    with Not_found -> ()
  in
  Mts.iter add_ts sm.Theory.sm_ts;
  Hits.fold Mits.add itsh Mits.empty,
  Hreg.fold Mreg.add regh Mreg.empty

(** computation types (with effects) *)

(* exception symbols *)
type xsymbol = {
  xs_name : ident;
  xs_ity  : ity; (* closed and pure *)
}

exception PolymorphicException of ident * ity
exception MutableException of ident * ity

let xs_equal : xsymbol -> xsymbol -> bool = (==)

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
  eff_writes : Sreg.t;
  eff_raises : Sexn.t;
  eff_ghostw : Sreg.t; (* ghost writes *)
  eff_ghostx : Sexn.t; (* ghost raises *)
  (* if r1 -> Some r2 then r1 appears in ty(r2) *)
  eff_resets : region option Mreg.t;
  eff_compar : Stv.t;
  eff_diverg : bool;
}

let eff_empty = {
  eff_writes = Sreg.empty;
  eff_raises = Sexn.empty;
  eff_ghostw = Sreg.empty;
  eff_ghostx = Sexn.empty;
  eff_resets = Mreg.empty;
  eff_compar = Stv.empty;
  eff_diverg = false;
}

let eff_is_empty e =
  Sreg.is_empty e.eff_writes &&
  Sexn.is_empty e.eff_raises &&
  Sreg.is_empty e.eff_ghostw &&
  Sexn.is_empty e.eff_ghostx &&
  Mreg.is_empty e.eff_resets &&
  (* eff_compar is not a side effect *)
  not e.eff_diverg

let eff_equal e1 e2 =
  Sreg.equal e1.eff_writes e2.eff_writes &&
  Sexn.equal e1.eff_raises e2.eff_raises &&
  Sreg.equal e1.eff_ghostw e2.eff_ghostw &&
  Sexn.equal e1.eff_ghostx e2.eff_ghostx &&
  Mreg.equal (Opt.equal reg_equal) e1.eff_resets e2.eff_resets &&
  Stv.equal e1.eff_compar e2.eff_compar &&
  e1.eff_diverg = e2.eff_diverg

let join_reset _key v1 v2 = match v1, v2 with
  | Some r1, Some r2 ->
      if reg_equal r1 r2 then Some v1 else
      if reg_occurs r1 r2.reg_ity.ity_vars then Some v2 else
      if reg_occurs r2 r1.reg_ity.ity_vars then Some v1 else
      Some None
  | _ -> Some None

let eff_union x y = {
  eff_writes = Sreg.union x.eff_writes y.eff_writes;
  eff_raises = Sexn.union x.eff_raises y.eff_raises;
  eff_ghostw = Sreg.union x.eff_ghostw y.eff_ghostw;
  eff_ghostx = Sexn.union x.eff_ghostx y.eff_ghostx;
  eff_resets = Mreg.union join_reset x.eff_resets y.eff_resets;
  eff_compar = Stv.union x.eff_compar y.eff_compar;
  eff_diverg = x.eff_diverg || y.eff_diverg;
}

exception GhostDiverg

let eff_ghostify e = {
  eff_writes = Sreg.empty;
  eff_raises = Sexn.empty;
  eff_ghostw = Sreg.union e.eff_writes e.eff_ghostw;
  eff_ghostx = Sexn.union e.eff_raises e.eff_ghostx;
  eff_resets = e.eff_resets;
  eff_compar = e.eff_compar;
    (* from the code extraction point of view, we can allow comparing
       opaque types in the ghost code, as it is never extracted.
       However, if we consider Coq realisations, we have to treat
       some pure types (e.g., maps) as opaque, too, and never compare
       them even in pure formulas. Therefore, we play safe and forbid
       comparison of opaque types in the ghost code. *)
  eff_diverg = if e.eff_diverg then raise GhostDiverg else false;
}

let eff_ghostify gh e = if gh then eff_ghostify e else e

let eff_write e ?(ghost=false) r = if ghost
  then { e with eff_ghostw = Sreg.add r e.eff_ghostw }
  else { e with eff_writes = Sreg.add r e.eff_writes }

let eff_raise e ?(ghost=false) x = if ghost
  then { e with eff_ghostx = Sexn.add x e.eff_ghostx }
  else { e with eff_raises = Sexn.add x e.eff_raises }

let eff_reset e r = { e with eff_resets = Mreg.add r None e.eff_resets }

let eff_compare e tv = { e with eff_compar = Stv.add tv e.eff_compar }

let eff_diverge e = { e with eff_diverg = true }

exception IllegalAlias of region
exception IllegalCompar of tvsymbol * ity

let eff_refresh e r u =
  if not (reg_occurs r u.reg_ity.ity_vars) then
    invalid_arg "Mlw_ty.eff_refresh";
  let reset = Mreg.singleton r (Some u) in
  { e with eff_resets = Mreg.union join_reset e.eff_resets reset }

let eff_assign e ?(ghost=false) r ty =
  let e = eff_write e ~ghost r in
  let sub = ity_match ity_subst_empty r.reg_ity ty in
  (* assignment cannot instantiate type variables *)
  let check tv ity = match ity.ity_node with
    | Ityvar tv' -> tv_equal tv tv'
    | _ -> false in
  if not (Mtv.for_all check sub.ity_subst_tv) then
    raise (TypeMismatch (r.reg_ity,ty,ity_subst_empty));
  (* r:t[r1,r2] <- t[r1,r1] introduces an alias *)
  let add_right _ v s = Sreg.add_new (IllegalAlias v) v s in
  ignore (Mreg.fold add_right sub.ity_subst_reg Sreg.empty);
  (* every region on the rhs must be erased *)
  let add_right k v m = if reg_equal k v then m else Mreg.add v None m in
  let reset = Mreg.fold add_right sub.ity_subst_reg Mreg.empty in
  (* ...except those which occur on the lhs : they are preserved under r *)
  let add_left k v m = if reg_equal k v then m else Mreg.add k (Some r) m in
  let reset = Mreg.fold add_left sub.ity_subst_reg reset in
  { e with eff_resets = Mreg.union join_reset e.eff_resets reset }

let eff_remove_raise e x = { e with
  eff_raises = Sexn.remove x e.eff_raises;
  eff_ghostx = Sexn.remove x e.eff_ghostx;
}

let eff_full_inst sbs e =
  let s = sbs.ity_subst_reg in
  (* modified or reset regions in e *)
  let wr = Mreg.map (Util.const ()) e.eff_resets in
  let wr = Sreg.union e.eff_writes wr in
  let wr = Sreg.union e.eff_ghostw wr in
  (* read-only regions in e *)
  let ro = Sreg.diff (Mreg.map (Util.const ()) s) wr in
  (* all modified or reset regions are instantiated into distinct regions *)
  let add_affected r acc =
    let r = Mreg.find r s in Sreg.add_new (IllegalAlias r) r acc in
  let wr = Sreg.fold add_affected wr Sreg.empty in
  (* all read-only regions are instantiated outside wr *)
  let add_readonly r =
    let r = Mreg.find r s in if Sreg.mem r wr then raise (IllegalAlias r) in
  Sreg.iter add_readonly ro;
  (* all type variables are instantiated outside wr *)
  let check_tv _ ity = Sreg.iter (fun r ->
    if reg_occurs r ity.ity_vars then raise (IllegalAlias r)) wr in
  Mtv.iter check_tv sbs.ity_subst_tv;
  (* calculate instantiated effect *)
  let add_sreg r acc = Sreg.add (Mreg.find r s) acc in
  let add_mreg r v acc =
    Mreg.add (Mreg.find r s) (Opt.map (fun v -> Mreg.find v s) v) acc in
  (* compute compared type variables *)
  let add_stv tv acc =
    let ity = Mtv.find tv sbs.ity_subst_tv in
    let check () _ = raise (IllegalCompar (tv,ity)) in
    ity_s_fold check (fun () _ -> ()) () ity;
    Stv.union acc ity.ity_vars.vars_tv in
  { e with
    eff_writes = Sreg.fold add_sreg e.eff_writes Sreg.empty;
    eff_ghostw = Sreg.fold add_sreg e.eff_ghostw Sreg.empty;
    eff_resets = Mreg.fold add_mreg e.eff_resets Mreg.empty;
    eff_compar = Stv.fold  add_stv  e.eff_compar Stv.empty;
  }

let eff_filter vars e =
  let check r = reg_occurs r vars in
  let reset r = function
    | _ when not (check r) -> None
    | Some u as v when check u -> Some v
    | _ -> Some None
  in
  { e with
    eff_writes = Sreg.filter check e.eff_writes;
    eff_ghostw = Sreg.filter check e.eff_ghostw;
    eff_resets = Mreg.mapi_filter reset e.eff_resets;
    eff_compar = Stv.inter vars.vars_tv e.eff_compar;
  }

let eff_stale_region eff vars =
  let check_reset r u =
    let rec check_reg reg =
      reg_equal r reg || match u with
        | Some u when reg_equal u reg -> false
        | _ -> Sreg.exists check_reg reg.reg_ity.ity_vars.vars_reg in
    Sreg.exists check_reg vars.vars_reg in
  Mreg.exists check_reset eff.eff_resets

(** specification *)

type pre = term          (* precondition: pre_fmla *)
type post = term         (* postcondition: eps result . post_fmla *)
type xpost = post Mexn.t (* exceptional postconditions *)

type variant = term * lsymbol option (* tau * (tau -> tau -> prop) *)

let create_post vs f = t_eps_close vs f

let open_post f = match f.t_node with
  | Teps bf -> t_open_bound bf
  | _ -> Loc.errorm "invalid post-condition"

let check_post ty f = match f.t_node with
  | Teps _ -> Ty.ty_equal_check ty (t_type f)
  | _ -> Loc.errorm "invalid post-condition"

type spec = {
  c_pre     : pre;
  c_post    : post;
  c_xpost   : xpost;
  c_effect  : effect;
  c_variant : variant list;
  c_letrec  : int;
}

let spec_empty ty = {
  c_pre     = t_true;
  c_post    = create_post (create_vsymbol (id_fresh "dummy") ty) t_true;
  c_xpost   = Mexn.empty;
  c_effect  = eff_empty;
  c_variant = [];
  c_letrec  = 0;
}

let spec_full_inst sbs tvm vsm c =
  let subst = t_ty_subst tvm vsm in {
    c_pre     = subst c.c_pre;
    c_post    = subst c.c_post;
    c_xpost   = Mexn.map subst c.c_xpost;
    c_effect  = eff_full_inst sbs c.c_effect;
    c_variant = List.map (fun (t,rel) -> subst t, rel) c.c_variant;
    c_letrec  = c.c_letrec;
  }

let spec_subst sbs c =
  let subst = t_subst sbs in {
    c_pre     = subst c.c_pre;
    c_post    = subst c.c_post;
    c_xpost   = Mexn.map subst c.c_xpost;
    c_effect  = c.c_effect;
    c_variant = List.map (fun (t,rel) -> subst t, rel) c.c_variant;
    c_letrec  = c.c_letrec;
  }

let spec_vsset c =
  let add f s = Mvs.set_union (t_vars f) s in
  let s = add c.c_pre (t_vars c.c_post) in
  let s = Mexn.fold (fun _ f s -> add f s) c.c_xpost s in
  List.fold_left (fun s (t,_) -> add t s) s c.c_variant

let spec_filter ghost svs vars c =
  let s = spec_vsset c in
  if not (Mvs.set_submap s svs) then
    Loc.errorm "Local variable %s escapes from its scope"
      (fst (Mvs.choose (Mvs.set_diff s svs))).vs_name.id_string;
  if not ghost && not (Sexn.is_empty c.c_effect.eff_ghostx) then
    Loc.errorm "Only ghost functions may raise ghost exceptions";
  { c with c_effect = eff_ghostify ghost (eff_filter vars c.c_effect) }

exception UnboundException of xsymbol

let spec_check ~full_xpost c ty =
  if c.c_pre.t_ty <> None then
    Loc.error ?loc:c.c_pre.t_loc (Term.FmlaExpected c.c_pre);
  check_post ty c.c_post;
  Mexn.iter (fun xs q -> check_post (ty_of_ity xs.xs_ity) q) c.c_xpost;
  (* we admit non-empty variant list even for null letrec,
     so that we can store there external variables from
     user-written effects to save them from spec_filter *)
  let check_variant (t,rel) = match rel with
    | Some ps -> ignore (ps_app ps [t;t])
    | None -> ignore (t_type t) in
  List.iter check_variant c.c_variant;
  if full_xpost && not (Mexn.set_submap c.c_effect.eff_raises c.c_xpost) then
    raise (UnboundException
      (Sexn.choose (Mexn.set_diff c.c_effect.eff_raises c.c_xpost)));
  if full_xpost && not (Mexn.set_submap c.c_effect.eff_ghostx c.c_xpost) then
    raise (UnboundException
      (Sexn.choose (Mexn.set_diff c.c_effect.eff_ghostx c.c_xpost)))

(** program variables *)

type pvsymbol = {
  pv_vs    : vsymbol;
  pv_ity   : ity;
  pv_ghost : bool;
}

module PVsym = MakeMSHW (struct
  type t = pvsymbol
  let tag pv = pv.pv_vs.vs_name.id_tag
end)

module Spv = PVsym.S
module Mpv = PVsym.M
module Hpv = PVsym.H
module Wpv = PVsym.W

let pv_equal : pvsymbol -> pvsymbol -> bool = (==)

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

let pvs_of_vss pvs vss =
  Mvs.fold (fun vs _ s -> Spv.add (restore_pv vs) s) vss pvs

let t_pvset pvs t = pvs_of_vss pvs (t_vars t)

let spec_pvset pvs spec = pvs_of_vss pvs (spec_vsset spec)

(** program types *)

type vty =
  | VTvalue of ity
  | VTarrow of aty

and aty = {
  aty_args   : pvsymbol list;
  aty_result : vty;
  aty_spec   : spec;
}

let rec aty_vars aty =
  let add_arg vars pv = vars_union vars pv.pv_ity.ity_vars in
  List.fold_left add_arg (vty_vars aty.aty_result) aty.aty_args

and vty_vars = function
  | VTvalue ity -> ity.ity_vars
  | VTarrow aty -> aty_vars aty

let rec aty_pvset aty =
  let spv = match aty.aty_result with
    | VTarrow a -> aty_pvset a
    | VTvalue _ -> Spv.empty in
  let spv = spec_pvset spv aty.aty_spec in
  List.fold_right Spv.remove aty.aty_args spv

let ity_of_vty = function
  | VTvalue ity -> ity
  | VTarrow _   -> ity_unit

let ty_of_vty = function
  | VTvalue ity -> ty_of_ity ity
  | VTarrow _   -> ty_unit

let spec_check ?(full_xpost=true) spec vty =
  spec_check ~full_xpost spec (ty_of_vty vty)

let vty_arrow_unsafe argl spec vty = {
  aty_args   = argl;
  aty_result = vty;
  aty_spec   = spec;
}

let vty_arrow argl ?spec vty =
  let exn = Invalid_argument "Mlw.vty_arrow" in
  (* the arguments must be all distinct *)
  if argl = [] then raise exn;
  let add_arg pvs pv = Spv.add_new exn pv pvs in
  ignore (List.fold_left add_arg Spv.empty argl);
  let spec = match spec with
    | Some spec -> spec_check spec vty; spec
    | None -> spec_empty (ty_of_vty vty) in
  vty_arrow_unsafe argl spec vty

(* this only compares the types of arguments and results, and ignores
   the spec. In other words, only the type variables and regions in
   [aty_vars aty] are matched. The caller should supply a "freezing"
   substitution that covers all external type variables and regions. *)
let rec aty_vars_match s a argl res =
  let rec match_args s l1 l2 = match l1, l2 with
    | v1::l1, v2::l2 -> match_args (ity_match s v1.pv_ity v2) l1 l2
    | [], l -> s, l
    | _, [] -> invalid_arg "Mlw_ty.aty_vars_match" in
  let s, argl = match_args s a.aty_args argl in
  match a.aty_result, argl with
  | VTvalue v, [] -> ity_match s v res
  | VTvalue _, _
  | VTarrow _, [] -> invalid_arg "Mlw_ty.aty_vars_match"
  | VTarrow a, _  -> aty_vars_match s a argl res

(* the substitution must cover not only [aty_vars aty] but
   also every type variable and every region in [aty_spec] *)
let aty_full_inst sbs aty =
  let tvm = Mtv.map ty_of_ity sbs.ity_subst_tv in
  let pv_inst { pv_vs = vs; pv_ity = ity; pv_ghost = ghost } =
    create_pvsymbol (id_clone vs.vs_name) ~ghost (ity_full_inst sbs ity) in
  let add_arg vsm pv =
    let nv = pv_inst pv in
    Mvs.add pv.pv_vs (t_var nv.pv_vs) vsm, nv in
  let rec aty_inst vsm aty =
    let vsm, args = Lists.map_fold_left add_arg vsm aty.aty_args in
    let spec = spec_full_inst sbs tvm vsm aty.aty_spec in
    let vty = match aty.aty_result with
      | VTarrow aty -> VTarrow (aty_inst vsm aty)
      | VTvalue ity -> VTvalue (ity_full_inst sbs ity) in
    vty_arrow_unsafe args spec vty
  in
  aty_inst Mvs.empty aty

(* remove from the given arrow every inner effect *)
let rec aty_filter ghost svs vars aty =
  let add svs pv = Svs.add pv.pv_vs svs in
  let svs = List.fold_left add svs aty.aty_args in
  let add vars pv = vars_union vars pv.pv_ity.ity_vars in
  let vars = List.fold_left add vars aty.aty_args in
  (* remove the effects that do not affect the context *)
  let spec = spec_filter ghost svs vars aty.aty_spec in
  (* reset every fresh region in the returned value *)
  let spec = match aty.aty_result with
    | VTvalue v ->
        let on_reg r e = if reg_occurs r vars then e else eff_reset e r in
        { spec with c_effect = reg_fold on_reg v.ity_vars spec.c_effect }
    | VTarrow _ -> spec in
  (* filter the result type *)
  let vty = match aty.aty_result with
    | VTarrow a -> VTarrow (aty_filter ghost svs vars a)
    | VTvalue _ -> aty.aty_result in
  vty_arrow_unsafe aty.aty_args spec vty

let aty_filter ?(ghost=false) pvs aty =
  let add pv svs = Svs.add pv.pv_vs svs in
  let svs = Spv.fold add pvs Svs.empty in
  let add pv vars = vars_union vars pv.pv_ity.ity_vars in
  let vars = Spv.fold add pvs vars_empty in
  aty_filter ghost svs vars aty

let aty_app aty pv =
  let arg, rest = match aty.aty_args with
    | arg::rest -> arg,rest | _ -> assert false in
  ity_equal_check arg.pv_ity pv.pv_ity;
  let sbs = Mvs.singleton arg.pv_vs (t_var pv.pv_vs) in
  let rec vty_subst = function
    | VTarrow a when not (List.exists (pv_equal arg) a.aty_args) ->
        let result = vty_subst a.aty_result in
        let spec = spec_subst sbs a.aty_spec in
        VTarrow (vty_arrow_unsafe a.aty_args spec result)
    | vty -> vty in
  let result = vty_subst aty.aty_result in
  let spec = spec_subst sbs aty.aty_spec in
  if not pv.pv_ghost && arg.pv_ghost then
    Loc.errorm "non-ghost value passed as a ghost argument";
  let ghost = pv.pv_ghost && not arg.pv_ghost in
  if rest = [] then
    spec, ghost, result
  else
    spec_empty ty_unit, ghost, VTarrow (vty_arrow_unsafe rest spec result)
