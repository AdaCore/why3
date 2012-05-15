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
open Ident
open Ty
open Term
open Ptree
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

type dity = dity_desc ref

and dity_desc = {
  node: dity_node;
  ity : ity Lazy.t;
}

and dity_node =
  | Duvar of string (* user type variable *)
  | Dvar
  | Dits of itysymbol * dity list
  | Dts  of tysymbol  * dity list

let create_user_type_variable x =
  let id = id_user x.id x.id_loc in
  ref { node = Duvar x.id; ity = lazy (ity_var (create_tvsymbol id)) }

let create_type_variable () =
  let id = id_fresh "a" in
  ref { node = Dvar; ity = lazy (ity_var (create_tvsymbol id)) }

let ity_of_dity d = Lazy.force !d.ity

let its_app its dl =
  ref { node = Dits (its, dl);
        ity = lazy (ity_app_fresh its (List.map ity_of_dity dl)) }

let ts_app ts dl =
  ref { node = Dts (ts, dl);
        ity = lazy (ity_pur ts (List.map ity_of_dity dl)) }

(* unification *)

let rec unify d1 d2 =
  if d1 != d2 then begin
    begin match !d1.node, !d2.node with
    | Dvar, _ | _, Dvar ->
        ()
    | Duvar s1, Duvar s2 when s1 = s2 ->
        ()
    | Dits (its1, dl1), Dits (its2, dl2) when its_equal its1 its2 ->
        if List.length dl1 <> List.length dl2 then raise Exit;
        List.iter2 unify dl1 dl2
    | Dts (ts1, dl1), Dts (ts2, dl2) when ts_equal ts1 ts2 ->
        if List.length dl1 <> List.length dl2 then raise Exit;
        List.iter2 unify dl1 dl2
    | _ ->
        raise Exit
    end;
    d1 := !d2
  end

let unify d1 d2 =
  try unify d1 d2
  with Exit -> raise (TypeMismatch (ity_of_dity d1, ity_of_dity d2))

let find_type_variable htv tv =
  try
    Htv.find htv tv
  with Not_found ->
    let dtv = create_type_variable () in
    Htv.add htv tv dtv;
    dtv

let rec dity_of_ity htv ity = match ity.ity_node with
  | Ityvar tv -> find_type_variable htv tv
  | Itypur (ts, ityl) -> ts_app ts (List.map (dity_of_ity htv) ityl)
  | Ityapp (its, ityl, _) -> its_app its (List.map (dity_of_ity htv) ityl)

let dity_of_vtv htv v = dity_of_ity htv v.vtv_ity

let specialize_psymbol ps =
  let htv = Htv.create 17 in
  let rec decompose args a =
    let args = dity_of_vtv htv a.vta_arg :: args in
    match a.vta_result with
    | VTvalue v -> List.rev args, dity_of_vtv htv v
    | VTarrow a1 -> decompose args a1
  in
  decompose [] ps.ps_vta

let specialize_plsymbol pls =
  let htv = Htv.create 17 in
  List.map (dity_of_vtv htv) pls.pl_args, dity_of_vtv htv pls.pl_value

let dity_of_ty htv ty = dity_of_ity htv (ity_of_ty ty)

let specialize_lsymbol ls =
  let htv = Htv.create 17 in
  let ty = match ls.ls_value with
    | None -> dity_of_ity htv ity_bool
    | Some ty -> dity_of_ty htv ty
  in
  List.map (dity_of_ty htv) ls.ls_args, ty

