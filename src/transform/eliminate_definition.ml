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

let add_ls acc (ls,_) = create_logic_decl [ls,None] :: acc

let add_ld acc ls ld =
  let id = ls.ls_name.id_long ^ "_def" in
  let pr = create_prsymbol (id_derive id ls.ls_name) in
  create_prop_decl Paxiom pr (ls_defn_axiom ld) :: acc

let add_ld acc (ls,ld) = match ld with
  | None    -> acc
  | Some ld -> add_ld acc ls ld

let elim d = match d.d_node with
  | Dlogic ll ->
      let dl = List.fold_left add_ls [] ll in
      let dl = List.fold_left add_ld dl ll in
      List.rev dl
  | _ -> [d]

let elim = Register.store (fun () -> Trans.decl elim None)

let () = Driver.register_transform "eliminate_definition" elim

