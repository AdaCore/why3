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

(* eliminate let *)

let rec elim_t func pred t = match t.t_node with
  | Tlet (t1,tb) when (if t.t_ty = None then pred else func) ->
      let t1 = elim_t func pred t1 in
      elim_t func pred (t_open_bound_with t1 tb)
  | _ ->
      t_map (elim_t func pred) t

let eliminate_let_term = Trans.rewrite (elim_t true false) None
let eliminate_let_fmla = Trans.rewrite (elim_t false true) None
let eliminate_let      = Trans.rewrite (elim_t true true) None

let () =
  Trans.register_transform "eliminate_let_term" eliminate_let_term
    ~desc:"Eliminate@ let-expressions@ in@ terms.";
  Trans.register_transform "eliminate_let_fmla" eliminate_let_fmla
    ~desc:"Eliminate@ let-expressions@ in@ formulas.";
  Trans.register_transform "eliminate_let" eliminate_let
    ~desc:"Eliminate@ all@ let-expressions.";
