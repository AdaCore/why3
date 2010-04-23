(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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

open Ident
open Term
open Decl
open Task

let log acc (ps,_) = create_logic_decl [ps, None] :: acc
let axm acc (pr,f) = create_prop_decl Paxiom pr f :: acc
let imp acc (_,al) = List.fold_left axm acc al

let exi vl (_,f) =
  let rec descend f = match f.f_node with
    | Fquant (Fforall,f) ->
        let vl,tl,f = f_open_quant f in
        f_exists vl tl (descend f)
    | Fbinop (Fimplies,g,f) ->
        f_and g (descend f)
    | Fapp (_,tl) ->
        let marry acc v t = f_and_simp acc (f_equ v t) in
        List.fold_left2 marry f_true vl tl
    | _ -> Trans.unsupportedExpression (Fmla f) "eliminate_inductive"
  in
  descend f

let inv acc (ps,al) =
  let vl = List.map (create_vsymbol (id_fresh "z")) ps.ls_args in
  let tl = List.map t_var vl in
  let hd = f_app ps tl in
  let dj = Util.map_join_left (exi tl) f_or al in
  let ax = f_forall vl [[Fmla hd]] (f_implies hd dj) in
  let nm = id_derive (ps.ls_name.id_long ^ "_inversion") ps.ls_name in
  create_prop_decl Paxiom (create_prsymbol nm) ax :: acc

let elim d = match d.d_node with
  | Dind il ->
      let dl = List.fold_left log [] il in
      let dl = List.fold_left imp dl il in
      let dl = List.fold_left inv dl il in
      List.rev dl
  | _ -> [d]

let elim = Register.store (fun () -> Trans.decl elim None)

let () = Register.register_transform "eliminate_inductive" elim

