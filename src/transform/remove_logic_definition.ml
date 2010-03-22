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

let decl d =
  match d.d_node with
    | Dtype _ -> [d]
    | Dlogic l -> 
        let f (accls,accdef) (ls,def) =
          let accls =(create_logic_decl [ls,None])::accls in
          match def with
            | None -> accls,accdef
            | Some ls_defn ->
                let fmla = ls_defn_axiom ls_defn in
                let prsymbol = create_prsymbol (id_clone ls.ls_name) in
                accls,(create_prop_decl Paxiom prsymbol fmla)::accdef in
        let accls,accdef = (List.fold_left f ([],[]) l) in
        (List.rev_append accls) accdef
    | Dind _ -> [d]
    | Dprop _ -> [d]


let t = Register.store (fun () -> Trans.decl decl None)

let () = Driver.register_transform "remove_logic_definition" t

