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

open Term
open Decl

let rec elim_quant pol f =
  match f.t_node with
  | Tquant _ ->
    if pol then t_true else t_false
  | _ ->
    try
      t_map_sign elim_quant pol f
    with
      Failure _ -> f

let elim_less (d:decl) =
  match d.d_node with
  | Dprop (p,_v,t) ->
      let pol = match p with | Paxiom | Plemma -> true | Pgoal -> false in
      let t = elim_quant pol t in
      if p <> Pgoal && t_equal t t_true then []
      else
        [decl_map (fun _ -> t) d]
  | _ -> [d]

let () =
  Trans.register_transform "abstract_quantifiers" (Trans.decl elim_less None)
    ~desc:"abstract@ quantifiers@ in@ the@ axioms@ of@ the@ context and the goals@."
