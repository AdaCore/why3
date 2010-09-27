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

open Term
open Theory
open Task

let rec term acc t =
  match t.t_node with
  | Teps fb ->
      let fv = Svs.elements (t_freevars Svs.empty t) in
      let x, f = f_open_bound fb in
      let acc, f = form acc f in
      let tys = List.map (fun x -> x.vs_ty) fv in
      let xs = Ident.id_derive "epsilon" x.vs_name in
      let xl = create_fsymbol xs tys x.vs_ty in
      let acc = add_decl acc (Decl.create_logic_decl [xl,None]) in
      let axs =
        Decl.create_prsymbol (Ident.id_derive "epsilon_def" x.vs_name) in
      let xlapp = t_app xl (List.map (fun x -> t_var x) fv) t.t_ty in
      let f = f_forall_close_merge fv (f_subst_single x xlapp f) in
      let acc = add_decl acc (Decl.create_prop_decl Decl.Paxiom axs f) in
      acc, xlapp
  | _ -> t_map_fold term form acc t

and form acc f = f_map_fold term form acc f

let lift th acc =
  let th = th.task_decl in
  match th.td_node with
  | Decl d ->
      let acc, d = Decl.decl_map_fold term form acc d in
      add_decl acc d
  | _ -> add_tdecl acc th

let lift_epsilon = Trans.fold lift None

let () = Trans.register_transform "lift_epsilon" lift_epsilon

(* TODO different variants for εx.P(x) :
  * logic x + axiom P(x)
  * goal ∃x.P(x) + logic x + axiom P(x)
  * logic x + axiom (∃x.P(x)) => P(x)
  *)
