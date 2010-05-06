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
open Decl

let fmla_simpl f = f_map_simp (fun t -> t) (fun f -> f) f

let decl_l d =
  match d.d_node with
    | Dprop (k,pr,f) -> 
        let f = fmla_simpl f in
        begin match f.f_node, k with
          | Ftrue, Paxiom -> [[]]
          | Ffalse, Paxiom -> []
          | Ftrue, Pgoal -> []
          | _ -> [[create_prop_decl k pr f]]
        end
    | _ -> [[decl_map (fun t -> t) fmla_simpl d]]

let simplify_formula = Register.store (fun () -> Trans.decl_l decl_l None)


let () = Register.register_transform_l "simplify_formula" simplify_formula
