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
  its_mfields : pvsymbol Mvs.t; (** mutable fields *)
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
  | Itymut of itysymbol * ity list * region list * tvsymbol
    (** record with mutable fields and shareable components *)
  | Ityapp of itysymbol * ity list * region list
    (** algebraic type with shareable components *)
  | Itypur of itysymbol * ity list
    (** immutable type or a snapshot of a mutable type *)
  | Ityvar of tvsymbol
    (** type variable *)

and pvsymbol = {
  pv_vs    : vsymbol;
  pv_ity   : ity;
  pv_ghost : bool;
}

and region = ity (** regions are itys of the [Itymut] kind *)

module Itsym = MakeMSHW (struct
  type t = itysymbol
  let tag its = its.its_ts.ts_name.id_tag
end)

module Ity = MakeMSHW (struct
  type t = ity
  let tag ity = ity.ity_tag
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

module Sreg = Sity
module Mreg = Mity
module Hreg = Hity
module Wreg = Wity

module Spv = PVsym.S
module Mpv = PVsym.M
module Hpv = PVsym.H
module Wpv = PVsym.W

(* value type symbols *)

let its_equal : itysymbol -> itysymbol -> bool = (==)
let ity_equal : ity       -> ity       -> bool = (==)
let pv_equal  : pvsymbol  -> pvsymbol  -> bool = (==)

let its_hash its = id_hash its.its_ts.ts_name
let ity_hash ity = Weakhtbl.tag_hash ity.ity_tag
let pv_hash  pv  = id_hash pv.pv_vs.vs_name

exception NonUpdatable of itysymbol * ity

module Hsity = Hashcons.Make (struct
  type t = ity

  let equal ity1 ity2 = match ity1.ity_node, ity2.ity_node with
    | Itypur (s1,l1), Itypur (s2,l2) ->
        its_equal s1 s2 &&
        List.for_all2 ity_equal l1 l2
    | Ityapp (s1,l1,r1), Ityapp (s2,l2,r2) ->
        its_equal s1 s2 &&
        List.for_all2 ity_equal l1 l2 &&
        List.for_all2 ity_equal r1 r2
    | (Ityvar v1 | Itymut (_,_,_,v1)),
      (Ityvar v2 | Itymut (_,_,_,v2)) ->
        tv_equal v1 v2
    | _ -> false

  let hash ity = match ity.ity_node with
    | Itypur (s,tl) ->
        Hashcons.combine_list ity_hash (its_hash s) tl
    | Ityapp (s,tl,rl) ->
        Hashcons.combine_list ity_hash
          (Hashcons.combine_list ity_hash (its_hash s) tl) rl
    | Ityvar v | Itymut (_,_,_,v) ->
        tv_hash v

  let check_upd s acc upd ity =
    if not (upd || ity.ity_pure) then raise (NonUpdatable (s,ity));
    acc && ity.ity_pure

  let pure ity = match ity.ity_node with
    | Ityvar _ -> true
    | Itypur (s,tl) -> List.fold_left2 (check_upd s) true s.its_arg_upd tl
    | Ityapp (_,_,[]) -> assert false
    | Ityapp (s,tl,_) -> List.fold_left2 (check_upd s) false s.its_arg_upd tl
    | Itymut (s,tl,_,_) -> List.fold_left2 (check_upd s) false s.its_arg_upd tl

  let tag n ity = { ity with
    ity_pure = pure ity;
    ity_tag  = Weakhtbl.create_tag n }
end)

let mk_ity n = {
  ity_node = n;
  ity_pure = true;
  ity_tag  = Weakhtbl.dummy_tag;
}

let ity_var_unsafe n = Hsity.hashcons (mk_ity (Ityvar n))
let ity_pur_unsafe s tl = Hsity.hashcons (mk_ity (Itypur (s,tl)))
let ity_app_unsafe s tl rl = Hsity.hashcons (mk_ity (Ityapp (s,tl,rl)))
let ity_mut_unsafe s tl rl v = Hsity.hashcons (mk_ity (Itymut (s,tl,rl,v)))

let tv_of_region reg = match reg.ity_node with
  | Itymut (_,_,_,tv) -> tv
  | _ -> invalid_arg "Ity.tv_of_region"

let open_region reg = match reg.ity_node with
  | Itymut (s,tl,rl,tv) -> s,tl,rl,tv
  | _ -> invalid_arg "Ity.open_region"

let ity_mut_fresh_unsafe s tl rl =
  ity_mut_unsafe s tl rl (create_tvsymbol (id_fresh "rho"))

let ity_mut_known_unsafe s tl rl v =
  let ity = ity_mut_unsafe s tl rl v in
  match ity.ity_node with
  | Itymut (s',tl',rl',_)
    when its_equal s s' &&
         Lists.equal ity_equal tl tl' &&
         Lists.equal ity_equal rl rl' -> ity
  | _ -> invalid_arg "Ity.ity_mut"

(* generic traversal functions *)

let ity_fold fn acc ity = match ity.ity_node with
  | Ityvar _ -> acc
  | Itypur (_,tl)
  | Ityapp (_,tl,_)
  | Itymut (_,tl,_,_) -> List.fold_left fn acc tl

let ity_all pr ity =
  try ity_fold (Util.all_fn pr) true ity with Util.FoldSkip -> false

let ity_any pr ity =
  try ity_fold (Util.any_fn pr) false ity with Util.FoldSkip -> true

(* symbol-wise map/fold *)

let rec ity_s_fold fits acc ity =
  let fold acc ity = ity_s_fold fits acc ity in
  let fold acc ityl = List.fold_left fold acc ityl in
  match ity.ity_node with
  | Itymut (s,tl,rl,_) | Ityapp (s,tl,rl) -> fold (fold (fits acc s) tl) rl
  | Itypur (s,tl) -> fold (fits acc s) tl
  | Ityvar _ -> acc

let ity_s_all pits ity =
  try ity_s_fold (Util.all_fn pits) true ity with Util.FoldSkip -> false

let ity_s_any pits ity =
  try ity_s_fold (Util.any_fn pits) false ity with Util.FoldSkip -> true

(* traversal functions on type variables and regions *)

let rec ity_v_fold fn acc ity = match ity.ity_node with
  | Ityvar v -> fn acc v
  | _ -> ity_fold (ity_v_fold fn) acc ity

let ity_freevars s ity = ity_v_fold (fun s v -> Stv.add v s) s ity

let ity_v_all pr ity =
  try ity_v_fold (Util.all_fn pr) true ity with Util.FoldSkip -> false

let ity_v_any pr ity =
  try ity_v_fold (Util.any_fn pr) false ity with Util.FoldSkip -> true

let ity_v_occurs tv ity = ity_v_any (tv_equal tv) ity

let ity_closed ity = ity_v_all (fun _ -> false) ity

let rec ity_r_fold fn acc ity =
  let ffn acc ity = ity_r_fold fn acc ity in
  match ity.ity_node with
  | Ityvar _ -> acc
  | Itypur (_,tl) -> List.fold_left ffn acc tl
  | Ityapp (_,tl,rl) -> List.fold_left ffn (List.fold_left fn acc rl) tl
  | Itymut _ -> fn acc ity

let ity_r_all pr ity =
  try ity_r_fold (Util.all_fn pr) true ity with Util.FoldSkip -> false

let ity_r_any pr ity =
  try ity_r_fold (Util.any_fn pr) false ity with Util.FoldSkip -> true

let ity_r_occurs reg ity =
  let rec check r = ity_equal r reg ||
    let _,tl,rl,_ = open_region r in
    List.exists (ity_r_any check) tl ||
    List.exists check rl in
  ity_r_any check ity

let ity_r_stale reg sreg ity =
  let rec check r = ity_equal r reg ||
    if Sreg.mem r sreg then false else
    let _,tl,rl,_ = open_region r in
    List.exists (ity_r_any check) tl ||
    List.exists check rl in
  ity_r_any check ity

let ity_immutable ity = not ity.ity_pure

(* detect non-ghost type variables and regions *)

let rec fold_visible on_var on_reg acc ity =
  let fnt acc ity = fold_visible on_var on_reg acc ity in
  let fnr acc vis ity = if vis then fnt acc ity else acc in
  match ity.ity_node with
  | Ityvar tv ->
      on_var acc tv
  | Itypur (s,tl) ->
      List.fold_left2 fnr acc s.its_arg_vis tl
  | Ityapp (s,tl,rl) ->
      let acc = List.fold_left2 fnr acc s.its_reg_vis rl in
      List.fold_left2 fnr acc s.its_arg_vis tl
  | Itymut (s,tl,rl,_) ->
      let acc = on_reg acc ity in
      let acc = List.fold_left2 fnr acc s.its_reg_vis rl in
      List.fold_left2 fnr acc s.its_arg_vis tl

let ity_r_visible regs ity =
  fold_visible (fun s _ -> s) (fun s r -> Sreg.add r s) regs ity

let ity_v_visible vars ity =
  fold_visible (fun s v -> Stv.add v s) (fun s _ -> s) vars ity

(* smart constructors *)

exception BadItyArity of itysymbol * int
exception BadRegArity of itysymbol * int

exception DuplicateRegion of region
exception UnboundRegion of region

exception TypeMismatch of ity * ity * ity Mtv.t

let ity_equal_check ty1 ty2 =
  if not (ity_equal ty1 ty2) then raise (TypeMismatch (ty1,ty2,Mtv.empty))

let ity_full_inst s ity =
  if Mtv.is_empty s then ity else
  let rec inst ity = match ity.ity_node with
    | Ityapp (f,tl,rl) -> ity_app_unsafe f (List.map inst tl) (List.map inst rl)
    | Itypur (f,tl) -> ity_pur_unsafe f (List.map inst tl)
    | Ityvar v | Itymut (_,_,_,v) -> Mtv.find v s in
  inst ity

let rec ity_match sbs ity1 ity2 = match ity1.ity_node, ity2.ity_node with
  | (Itymut (_,_,_,v1)| Ityvar v1), _ when Mtv.mem v1 sbs ->
      if ity_equal (Mtv.find v1 sbs) ity2 then sbs else raise Exit
  | Itymut (s1,l1,r1,v1), Itymut (s2,l2,r2,_) when its_equal s1 s2 ->
      let sbs = List.fold_left2 ity_match sbs l1 l2 in
      let sbs = List.fold_left2 ity_match sbs r1 r2 in
      Mtv.add v1 ity2 sbs
  | Ityapp (s1,l1,r1), Ityapp (s2,l2,r2) when its_equal s1 s2 ->
      let sbs = List.fold_left2 ity_match sbs l1 l2 in
      List.fold_left2 ity_match sbs r1 r2
  | Itypur (s1, l1), Itypur (s2, l2) when its_equal s1 s2 ->
      List.fold_left2 ity_match sbs l1 l2
  | Ityvar v1, _ ->
      Mtv.add v1 ity2 sbs
  | _ -> raise Exit

let ity_match sbs ity1 ity2 =
  try ity_match sbs ity1 ity2
  with Exit -> raise (TypeMismatch (ity1,ity2,sbs))

let ity_freeze sbs ity = ity_match sbs ity ity

let rec ty_of_ity ity = match ity.ity_node with
  | Ityvar v -> ty_var v
  | Itypur (s,tl) | Ityapp (s,tl,_) | Itymut (s,tl,_,_) ->
      ty_app s.its_ts (List.map ty_of_ity tl)

let rec ity_purify ity = match ity.ity_node with
  | Ityvar _ -> ity
  | Itypur (s,tl) | Ityapp (s,tl,_) | Itymut (s,tl,_,_) ->
      ity_pur_unsafe s (List.map ity_purify tl)

let ity_var v =
  let ity = ity_var_unsafe v in
  match ity.ity_node with
  | Ityvar _ -> ity
  | _ -> invalid_arg "Ity.ity_var"

let ity_pur s tl =
  if List.length s.its_ts.ts_args <> List.length tl then
    raise (BadItyArity (s, List.length tl));
  match s.its_def with
  | Some ity ->
      let sbs = List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty in
      ity_full_inst sbs (ity_purify ity)
  | None ->
      ity_pur_unsafe s tl

let ity_mut s tl rl v =
  (* compute the substitution even for non-aliases to verify regions *)
  let sbs = try List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty
    with Invalid_argument _ -> raise (BadItyArity (s, List.length tl)) in
  let sbs = try List.fold_left2 ity_match sbs s.its_regions rl
    with Invalid_argument _ -> raise (BadRegArity (s, List.length rl)) in
  match s.its_def with
  | Some { ity_node = Itymut (s,tl,rl,_) } ->
      let tl = List.map (ity_full_inst sbs) tl in
      let rl = List.map (ity_full_inst sbs) rl in
      ity_mut_known_unsafe s tl rl v
  | None when s.its_mutable ->
      ity_mut_known_unsafe s tl rl v
  | _ -> invalid_arg "Ity.ity_mut"

let ity_app sbs s tl rl = match s.its_def with
  | Some { ity_node = Itymut (s,tl,rl,_) } ->
      let tl = List.map (ity_full_inst sbs) tl in
      let rl = List.map (ity_full_inst sbs) rl in
      ity_mut_fresh_unsafe s tl rl
  | None when s.its_mutable ->
      ity_mut_fresh_unsafe s tl rl
  | Some ity ->
      ity_full_inst sbs ity
  | None when rl = [] ->
      ity_pur_unsafe s tl
  | None ->
      ity_app_unsafe s tl rl

let rec ity_inst_fresh sbs ity = match ity.ity_node with
  | Ityvar v ->
      sbs, Mtv.find v sbs
  | Itypur (s,tl) ->
      let sbs,tl = Lists.map_fold_left ity_inst_fresh sbs tl in
      sbs, ity_pur_unsafe s tl
  | Ityapp (s,tl,rl) ->
      let sbs,tl = Lists.map_fold_left ity_inst_fresh sbs tl in
      let sbs,rl = Lists.map_fold_left ity_inst_fresh sbs rl in
      sbs, ity_app_unsafe s tl rl
  | Itymut (_,_,_,v) when Mtv.mem v sbs ->
      sbs, Mtv.find v sbs
  | Itymut (s,tl,rl,v) ->
      let sbs,tl = Lists.map_fold_left ity_inst_fresh sbs tl in
      let sbs,rl = Lists.map_fold_left ity_inst_fresh sbs rl in
      let ity = ity_mut_unsafe s tl rl (create_tvsymbol (id_clone v.tv_name)) in
      Mtv.add v ity sbs, ity

let ity_app_fresh s tl =
  let sbs = try List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty
    with Invalid_argument _ -> raise (BadItyArity (s, List.length tl)) in
  let sbs,rl = Lists.map_fold_left ity_inst_fresh sbs s.its_regions in
  ity_app sbs s tl rl

let ity_app s tl rl =
  (* compute the substitution even for non-aliases to verify regions *)
  let sbs = try List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty
    with Invalid_argument _ -> raise (BadItyArity (s, List.length tl)) in
  let sbs = try List.fold_left2 ity_match sbs s.its_regions rl
    with Invalid_argument _ -> raise (BadRegArity (s, List.length rl)) in
  ity_app sbs s tl rl

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
  Wts.find ts_to_its

let create_itysymbol name args pri mut regs fld def =
  (* prepare arguments *)
  let args, avis, aupd = List.fold_right
    (fun (tv,v,u) (args,avis,aupd) ->
      tv::args, v::avis, u::aupd) args ([],[],[]) in
  let regs, rvis = List.split regs in
  let fld = Spv.fold (fun pv acc ->
    Mvs.add pv.pv_vs pv acc) fld Mvs.empty in
  (* create_tysymbol checks that args contains no duplicates
     and covers every type variable in def *)
  let puredef = Opt.map ty_of_ity def in
  let ts = create_tysymbol name args puredef in
  (* all regions *)
  let add_r s r = match r.ity_node with
    | Itymut _ -> Sreg.add_new (DuplicateRegion r) r s
    | _ -> invalid_arg "Ity.create_itysymbol" in
  let sregs = List.fold_left add_r Sreg.empty regs in
  (* all type variables *)
  let sargs = List.fold_right Stv.add args Stv.empty in
  (* each type variable in [regs] and [fld] must be in [args] *)
  let check_v () v =
    if not (Stv.mem v sargs) then raise (Ty.UnboundTypeVar v) in
  let check_var ity = ity_v_fold check_v () ity in
  List.iter check_var regs;
  Mvs.iter (fun _ pv -> check_var pv.pv_ity) fld;
  (* each surface region in [fld] must be in [regs] *)
  let check_r () r =
    if not (Sreg.mem r sregs) then raise (UnboundRegion r) in
  let check_reg ity = ity_r_fold check_r () ity in
  Mvs.iter (fun _ pv -> check_reg pv.pv_ity) fld;
  (* each lower surface region in [def] must be in [regs] *)
  let check_reg () ity = match ity.ity_node with
    | Itymut (_,tl,rl,_) ->
        List.iter check_reg rl;
        List.iter check_reg tl
    | _ -> check_reg ity in
  Opt.fold check_reg () def;
  (* the alias is mutable if and only if the symbol is *)
  let check = function
    | Some {ity_node = Itymut _} -> mut
    | Some _ -> not mut
    | None -> true in
  if not (check def) then invalid_arg "Ity.create_itysymbol";
  (* if we have mutable fields then we are mutable *)
  if not (mut || Mvs.is_empty fld) then
    invalid_arg "Ity.create_itysymbol";
  (* if we are an alias then we are not private and have no fields *)
  if def <> None && (pri || not (Mvs.is_empty fld)) then
    invalid_arg "Ity.create_itysymbol";
  (* if we are private, we have no subregions and all args are non-updateble *)
  if pri && (regs <> [] || List.exists (fun u -> u) aupd) then
    invalid_arg "Ity.create_itysymbol";
  (* each invisible type variable and region must be invisible in [def] *)
  let v_visible = Opt.fold ity_v_visible Stv.empty def in
  let r_visible = Opt.fold ity_r_visible Sreg.empty def in
  let check_v vis v = if not vis && Stv.mem v v_visible then
      invalid_arg "Ity.create_itysymbol" in
  let check_r vis r = if not vis && Sreg.mem r r_visible then
      invalid_arg "Ity.create_itysymbol" in
  List.iter2 check_v avis args;
  List.iter2 check_r rvis regs;
  (* each updatable type variable is updatable in [regs], [fld], and [def] *)
  let rec nonupd acc upd ity = match ity.ity_node with
    | _ when not upd -> ity_freevars acc ity
    | Itypur (s,tl) | Ityapp (s,tl,_) | Itymut (s,tl,_,_) ->
        List.fold_left2 nonupd acc s.its_arg_upd tl
    | Ityvar _ -> acc in
  let nonupd acc ity = nonupd acc true ity in
  let nu = List.fold_left nonupd Stv.empty regs in
  let nu = Mvs.fold (fun _ pv s -> nonupd s pv.pv_ity) fld nu in
  let nu = Opt.fold nonupd nu def in
  List.iter2 (fun upd v -> if upd && Stv.mem v nu then
    invalid_arg "Ity.create_itysymbol") aupd args;
  (* NOTE: record/constructor fields must be pairwise separated,
     but this should be checked during the type declaration, [fld]
     is not enough *)
  (* create the type symbol *)
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

(** builtin symbols *)

let its_int = create_itysymbol_unsafe
    ~ts:ts_int ~pri:false ~mut:false ~fld:Mvs.empty
    ~regs:[] ~rvis:[] ~avis:[] ~aupd:[] ~def:None

let its_real = create_itysymbol_unsafe
    ~ts:ts_real ~pri:false ~mut:false ~fld:Mvs.empty
    ~regs:[] ~rvis:[] ~avis:[] ~aupd:[] ~def:None

let its_bool = create_itysymbol_unsafe
    ~ts:ts_bool ~pri:false ~mut:false ~fld:Mvs.empty
    ~regs:[] ~rvis:[] ~avis:[] ~aupd:[] ~def:None

let ity_int  = ity_pur its_int  []
let ity_real = ity_pur its_real []
let ity_bool = ity_pur its_bool []

let its_tuple = Hint.memo 17 (fun n ->
  let ts = ts_tuple n in
  let ll = List.map (fun _ -> true) ts.ts_args in
  create_itysymbol_unsafe
    ~ts:ts ~pri:false ~mut:false ~fld:Mvs.empty
    ~regs:[] ~rvis:[] ~avis:ll ~aupd:ll ~def:None)

let ity_tuple tl = ity_pur (its_tuple (List.length tl)) tl

let ts_unit  = ts_tuple  0
let its_unit = its_tuple 0

let ty_unit  = ty_tuple  []
let ity_unit = ity_tuple []

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

let eff_equal e1 e2 =
  Mreg.equal Spv.equal e1.eff_writes e2.eff_writes &&
  Mreg.equal Sreg.equal e1.eff_resets e2.eff_resets &&
  Sexn.equal e1.eff_raises e2.eff_raises &&
  e1.eff_diverg = e2.eff_diverg

let merge_fields _ f1 f2 = Some (Spv.union f1 f2)

let merge_covers reg c1 c2 = Some (Sreg.union
  (Sreg.filter (fun r -> not (ity_r_stale reg c1 r)) c2)
  (Sreg.filter (fun r -> not (ity_r_stale reg c2 r)) c1))

let eff_union x y = {
  eff_writes = Mreg.union merge_fields x.eff_writes y.eff_writes;
  eff_resets = Mreg.union merge_covers x.eff_resets y.eff_resets;
  eff_raises = Sexn.union x.eff_raises y.eff_raises;
  eff_diverg = x.eff_diverg || y.eff_diverg;
}

let eff_write e r f =
  begin match r.ity_node, f with
    | Itymut (s,_,_,_), Some f when Mvs.mem f.pv_vs s.its_mfields -> ()
    | Itymut _, None -> ()
    | _, _ -> invalid_arg "Ity.eff_write"
  end;
  let add fs = match f, fs with
    | Some f, Some fs -> Some (Spv.add f fs)
    | Some f, None    -> Some (Spv.singleton f)
    | None,   Some fs -> Some fs
    | None,   None    -> Some Spv.empty in
  { e with eff_writes = Mreg.change add r e.eff_writes }

let eff_raise e x = { e with eff_raises = Sexn.add x e.eff_raises }
let eff_catch e x = { e with eff_raises = Sexn.remove x e.eff_raises }

let eff_reset e r = match r.ity_node with
  | Itymut _ -> { e with eff_resets = Mreg.add r Sreg.empty e.eff_resets }
  | _ -> invalid_arg "Ity.eff_reset"

let eff_diverge e = { e with eff_diverg = true }

exception AssignPrivate of ity

(* freeze type variables and regions outside modified fields *)
let freeze_of_writes wr =
  let freeze_of_write r fs frz =
    let s,tl,rl,_ = open_region r in
    let frz = List.fold_left ity_freeze frz tl in
    let freeze_unhit frz r reg =
      (* fields are unaliased in [s], therefore if region [r] from
          [s.its_regions] occurs in [f.pv_ity], it cannot occur in
          any other field of [s], and therefore [reg] doesn't need
          to be frozen. If [reg] or subregions of [reg] are aliased
          with other fields of the modified value, they will occur
          in the instances of other regions in [s.its_regions], and
          will be frozen there. *)
      let hit f _ = ity_r_occurs r f.pv_ity in
      if Mpv.exists hit fs then frz else ity_freeze frz reg in
    List.fold_left2 freeze_unhit frz s.its_regions rl in
  Mreg.fold freeze_of_write wr Mtv.empty

let eff_assign e asl =
  let seen,e = List.fold_left (fun (seen,e) (r,f,ity) ->
    begin match r.ity_node with
      | Itymut (s,_,_,_) when s.its_private -> raise (AssignPrivate r)
      | Itymut (s,_,_,_) when Mvs.mem f.pv_vs s.its_mfields -> ()
      | _ -> invalid_arg "Ity.eff_assign"
    end;
    let seen = Mreg.change (fun fs -> Some (match fs with
      | Some fs -> Mpv.add_new (Invalid_argument "Ity.eff_assign") f ity fs
      | None    -> Mpv.singleton f ity)) r seen in
    seen, eff_write e r (Some f)) (Mreg.empty,e) asl in
  (* type variables and regions outside modified fields are frozen *)
  let frz = freeze_of_writes seen in
  (* non-frozen regions are allowed to be renamed, preserving aliases *)
  let sbst, sbsf = Mreg.fold (fun r fs acc ->
    let s,tl,rl,_ = open_region r in
    let sbs = List.fold_right2 Mtv.add s.its_ts.ts_args tl Mtv.empty in
    let sbs = List.fold_left2 ity_match sbs s.its_regions rl in
    (* TODO: catch the TypeMismatch exception and produce a reasonable
       error message *)
    Mpv.fold (fun pv ity (sbst,sbsf) ->
      let fity = ity_full_inst sbs pv.pv_ity in
      ity_match sbst fity ity,
      ity_match sbsf ity fity) fs acc) seen (frz,frz) in
  (* every RHS region is reset unless it is preserved *)
  let rst = Mtv.set_diff sbsf sbst in
  let e = Mtv.fold (fun v _ e ->
    (* since type variables are frozen, they can't appear in [rst].
       Thus, [v] has to be a region variable, and [ity_var_unsafe]
       will restore the corresponging region via hash-consing. *)
    eff_reset e (ity_var_unsafe v)) rst e in
  (* every region not instantiated to itself is refreshed *)
  let rfr = Mreg.fold (fun r _ rfr ->
    let sbst = Mtv.inter (fun v reg i -> match i.ity_node with
      | Itymut (_,_,_,u) when not (tv_equal u v) -> Some reg
      | _ -> None) (ity_freeze Mtv.empty r) sbst in
    let add_rfr _ reg rfr = Mreg.change (function
      | Some cvr -> Some (Sreg.add r cvr)
      | None     -> Some (Sreg.singleton r)) reg rfr in
    Mtv.fold add_rfr sbst rfr) seen Mreg.empty in
  { e with eff_resets = Mreg.union merge_covers e.eff_resets rfr }

let refresh_of_effect e =
  let frz = freeze_of_writes e.eff_writes in
  let rfr = Mreg.fold (fun r _ rfr ->
    let sbst = Mtv.set_diff (ity_freeze Mtv.empty r) frz in
    let add_rfr _ reg rfr = Mreg.change (function
      | Some cvr -> Some (Sreg.add r cvr)
      | None     -> Some (Sreg.singleton r)) reg rfr in
    Mtv.fold add_rfr sbst rfr) e.eff_writes Mreg.empty in
  { e with eff_resets = Mreg.union merge_covers e.eff_resets rfr }

exception IllegalAlias of region

let eff_full_inst sbs e =
  (* all modified or reset regions in e must be instantiated
     into distinct regions *)
  let inst fn src = Mreg.fold (fun r v acc ->
    let r = ity_full_inst sbs r in
    Mreg.add_new (IllegalAlias r) r (fn v) acc) src Mreg.empty in
  let writes = inst (fun fld -> fld) e.eff_writes in
  let resets = inst (inst (fun () -> ())) e.eff_resets in
  let impact = Mreg.merge (fun r fld cvr -> match fld, cvr with
    | Some _, Some _ -> raise (IllegalAlias r)
    | _ -> Some ()) writes resets in
  (* all type variables must be instantiated into types that are
     not affected by the effect, and all unaffected regions must
     be instantiated into regions outside [impact].

     Now, every region in the instantiated execution is either
     brought in by the type substitution and thus is unaffected,
     or instantiates one of the original regions and is affected
     if and only if the original one is. *)
  let check_inst v dst = match ity_var_unsafe v with
    | {ity_node = Ityvar _} -> Sreg.iter (fun r ->
        if ity_r_occurs r dst then raise (IllegalAlias r)) impact
    | reg when Mreg.mem reg e.eff_writes -> ()
    | reg when Mreg.mem reg e.eff_resets -> ()
    | _   when Sreg.mem dst impact -> raise (IllegalAlias dst)
    | _ -> () in
  Mtv.iter check_inst sbs;
  { e with eff_writes = writes; eff_resets = resets }

(*
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
*)
