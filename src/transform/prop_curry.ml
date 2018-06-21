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

let rec curry t = match t.t_node with
  | Tbinop (Timplies, lhs, rhs) -> expand t lhs (curry rhs)
  | _ -> t_map curry t

and expand orig l r = match l.t_node with
  | Tbinop (Tand, a, b) -> expand orig a (expand orig b r)
  | _  -> t_attr_copy orig (t_implies (curry l) r)

let curry = Trans.goal (fun pr t -> [create_prop_decl Pgoal pr (curry t)])

let () =
  Trans.register_transform "prop_curry" curry
    ~desc:"Transform@ conjunctions@ in@ implication@ premises@ into@ \
      sequences@ of@ premises."

