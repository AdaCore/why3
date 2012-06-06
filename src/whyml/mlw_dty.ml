(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* destructive types for program type inference *)

open Why3
open Util
open Ident
open Ty
open Term
open Ptree
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_module

type dity = dity_desc ref

and dity_desc = {
  uid : int;
  node: dity_node;
  ity : ity Lazy.t;
}

and dity_node =
  | Duvar of Ptree.ident (* user type variable *)
  | Dvar
  | Dits of itysymbol * dity list * dreg list
  | Dts  of tysymbol  * dity list

and dreg = dreg_desc ref

and dreg_desc = {
  rid:   int;
  rity:  dity;
  ruser: bool;
  reg:   region Lazy.t;
}

let unique = let r = ref 0 in fun () -> incr r; !r

let create n l = ref { uid = unique (); node = n; ity = l }

let create_user_type_variable x =
  let id = id_user x.id x.id_loc in
  create (Duvar x) (lazy (ity_var (create_tvsymbol id)))

let create_type_variable () =
  let id = id_fresh "a" in
  create Dvar (lazy (ity_var (create_tvsymbol id)))

let ity_of_dity d = Lazy.force !d.ity

let reg_of_dreg d = Lazy.force !d.reg

let create_dreg ~user dity =
  ref { rid = unique (); rity = dity; ruser = user;
        reg = lazy (create_region (id_fresh "rho") (ity_of_dity dity)) }

let ts_app_real ts dl =
  create (Dts (ts, dl)) (lazy (ity_pur ts (List.map ity_of_dity dl)))

let its_app_real its dl rl =
  create (Dits (its, dl, rl))
    (lazy (ity_app its (List.map ity_of_dity dl) (List.map reg_of_dreg rl)))

let rec ity_inst_fresh ~user mv mr ity = match ity.ity_node with
  | Ityvar v ->
      mr, Mtv.find v mv
  | Itypur (s,tl) ->
      let mr,tl = Util.map_fold_left (ity_inst_fresh ~user mv) mr tl in
      mr, ts_app_real s tl
  | Ityapp (s,tl,rl) ->
      let mr,tl = Util.map_fold_left (ity_inst_fresh ~user mv) mr tl in
      let mr,rl = Util.map_fold_left (reg_refresh ~user mv) mr rl in
      mr, its_app_real s tl rl

and reg_refresh ~user mv mr r = match Mreg.find_opt r mr with
  | Some r ->
      mr, r
  | None ->
      let mr,ity = ity_inst_fresh ~user mv mr r.reg_ity in
      let reg = create_dreg ~user ity in
      Mreg.add r reg mr, reg

let its_app ~user s tl =
  let add m v t = Mtv.add v t m in
  let mv = try List.fold_left2 add Mtv.empty s.its_args tl
    with Invalid_argument _ ->
      raise (BadItyArity (s, List.length s.its_args, List.length tl))
  in
  match s.its_def with
  | Some ity ->
      snd (ity_inst_fresh ~user mv Mreg.empty ity)
  | None ->
      let _, rl =
        Util.map_fold_left (reg_refresh ~user mv) Mreg.empty s.its_regs in
      its_app_real s tl rl

let ts_app ts dl = match ts.ts_def with
  | Some ty ->
      let add m v t = Mtv.add v t m in
      let mv = try List.fold_left2 add Mtv.empty ts.ts_args dl
        with Invalid_argument _ ->
          raise (BadTypeArity (ts, List.length ts.ts_args, List.length dl)) in
      snd (ity_inst_fresh ~user:true mv Mreg.empty (ity_of_ty ty))
  | None ->
      ts_app_real ts dl

(* unification *)

let rec unify d1 d2 =
  if !d1.uid <> !d2.uid then begin
    begin match !d1.node, !d2.node with
    | Dvar, _ ->
        ()
    | _, Dvar ->
        d2 := !d1
    | Duvar s1, Duvar s2 when s1.id = s2.id ->
        ()
    | Dits (its1, dl1, rl1), Dits (its2, dl2, rl2) when its_equal its1 its2 ->
        assert (List.length rl1 = List.length rl2);
        assert (List.length dl1 = List.length dl2);
        List.iter2 unify dl1 dl2;
        List.iter2 unify_reg rl1 rl2
    | Dts (ts1, dl1), Dts (ts2, dl2) when ts_equal ts1 ts2 ->
        assert (List.length dl1 = List.length dl2);
        List.iter2 unify dl1 dl2
    | _ ->
        raise Exit
    end;
    d1 := !d2
  end

and unify_reg r1 r2 =
  if !r1.rid <> !r2.rid then
    if not !r1.ruser then begin
      unify !r1.rity !r2.rity;
      r1 := !r2
    end
    else if not !r2.ruser then begin
      unify !r1.rity !r2.rity;
      r2 := !r1
    end
    else begin (* two user regions *)
      if not (Lazy.lazy_is_val !r1.reg) then raise Exit;
      if not (Lazy.lazy_is_val !r2.reg) then raise Exit;
      if not (reg_equal (Lazy.force !r1.reg) (Lazy.force !r2.reg)) then
        raise Exit
    end

let unify d1 d2 =
  try unify d1 d2
  with Exit -> raise (TypeMismatch (ity_of_dity d1, ity_of_dity d2))

let ts_arrow =
  let v = List.map (fun s -> create_tvsymbol (Ident.id_fresh s)) ["a"; "b"] in
  Ty.create_tysymbol (Ident.id_fresh "arrow") v None

let rec vty_of_dity dity = match !dity.node with
  | Dts (ts, [d1; d2]) when ts_equal ts ts_arrow ->
      VTarrow (vty_arrow (vty_value (ity_of_dity d1)) (vty_of_dity d2))
  | _ ->
      VTvalue (vty_value (ity_of_dity dity))

type tvars = Sint.t (* a set of type variables *)
let empty_tvars = Sint.empty

let rec add_tvars tvs d = match !d.node with
  | Duvar _ | Dvar -> Sint.add !d.uid tvs
  | Dits (_, dl, rl) ->
      let add_reg tvs r = add_tvars (Sint.add !r.rid tvs) !r.rity in
      List.fold_left add_reg (List.fold_left add_tvars tvs dl) rl
  | Dts (_, dl) -> List.fold_left add_tvars tvs dl

let specialize_scheme tvs dity =
  let hv = Hashtbl.create 17 in
  let huv = Hashtbl.create 17 in
  let hr = Hashtbl.create 17 in
  let rec specialize d = match !d.node with
    | Duvar _ | Dvar when Sint.mem !d.uid tvs -> d
    | Duvar id -> begin
        try Hashtbl.find huv id.id
        with Not_found ->
          let v = create_type_variable () in Hashtbl.add huv id.id v; v
      end
    | Dvar -> begin
        try Hashtbl.find hv !d.uid
        with Not_found ->
          let v = create_type_variable () in Hashtbl.add hv !d.uid v; v
      end
    | Dits (its, dl, rl) ->
        its_app_real its (List.map specialize dl) (List.map spec_reg rl)
    | Dts (ts, dl) -> ts_app_real ts (List.map specialize dl)
  and spec_reg r =
    if Sint.mem !r.rid tvs then r
    else if !r.ruser && Lazy.lazy_is_val !r.reg then r
    else
      try Hashtbl.find hr !r.rid
      with Not_found ->
        let v = create_dreg ~user:false (specialize !r.rity) in
        Hashtbl.add hr !r.rid v; v
  in
  specialize dity

(* Specialization of symbols *)

let find_type_variable htv tv =
  try
    Htv.find htv tv
  with Not_found ->
    let dtv = create_type_variable () in
    Htv.add htv tv dtv;
    dtv

let rec dity_of_ity ~user htv hreg ity = match ity.ity_node with
  | Ityvar tv -> assert (not user); find_type_variable htv tv
  | Itypur (ts, ityl) -> ts_app ts (List.map (dity_of_ity ~user htv hreg) ityl)
  | Ityapp (its, ityl, rl) ->
      its_app_real its (List.map (dity_of_ity ~user htv hreg) ityl)
        (List.map (dreg_of_reg ~user htv hreg) rl)

and dreg_of_reg ~user htv hreg r =
  try
    Hreg.find hreg r
  with Not_found ->
    let dreg = create_dreg ~user (dity_of_ity ~user htv hreg r.reg_ity) in
    Hreg.add hreg r dreg;
    dreg

let dity_of_vtv ~user htv hreg v = dity_of_ity ~user htv hreg v.vtv_ity

let specialize_vtvalue ~user vtv =
  let htv = Htv.create 17 in
  let hreg = Hreg.create 17 in
  dity_of_vtv ~user htv hreg vtv

let specialize_pvsymbol pv =
  specialize_vtvalue ~user:true pv.pv_vtv

let make_arrow_type tyl ty =
  let arrow ty1 ty2 =
    create (Dts (ts_arrow, [ty1; ty2])) (lazy (invalid_arg "ity_of_dity")) in
  List.fold_right arrow tyl ty

let specialize_vtarrow vta =
  let htv = Htv.create 17 in
  let hreg = Hreg.create 17 in
  let rec specialize a =
    let arg = dity_of_vtv ~user:false htv hreg a.vta_arg in
    let res = match a.vta_result with
      | VTvalue v -> dity_of_vtv ~user:false htv hreg v
      | VTarrow a1 -> specialize a1
    in
    make_arrow_type [arg] res
  in
  specialize vta

let specialize_psymbol ps = specialize_vtarrow ps.ps_vta

let specialize_plsymbol pls =
  let htv = Htv.create 17 in
  let hreg = Hreg.create 17 in
  let args = List.map (dity_of_vtv ~user:false htv hreg) pls.pl_args in
  make_arrow_type args (dity_of_vtv ~user:false htv hreg pls.pl_value)

let dity_of_ty ~user htv hreg ty = dity_of_ity ~user htv hreg (ity_of_ty ty)

let specialize_lsymbol ls =
  let htv = Htv.create 17 in
  let hreg = Hreg.create 17 in
  let ty = match ls.ls_value with
    | None -> dity_of_ity ~user:false htv hreg ity_bool
    | Some ty -> dity_of_ty ~user:false htv hreg ty
  in
  let args = List.map (dity_of_ty ~user:false htv hreg) ls.ls_args in
  make_arrow_type args ty
