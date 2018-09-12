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

let congruence pr f =
  match f.t_node with
  | Tapp (eq, [{ t_node = Tapp (f1, l1) }; { t_node = Tapp (f2, l2) }])
       when ls_equal eq ps_equ && ls_equal f1 f2 ->
     (* f a1 b1 c1... = f a2 b2 c2... *)
     let ts = List.map2 t_equ_simp l1 l2 in
     (* a1 = a2, b1 = b2... *)
     let goal_of_t t =
       let pr = create_prsymbol (Ident.id_fresh "G") in
       [create_prop_decl Pgoal pr t] in
     List.map goal_of_t ts
  | _ -> [[create_prop_decl Pgoal pr f]] (* no progress *)

let t = Trans.goal_l congruence

let () = Trans.register_transform_l "congruence" t
           ~desc:"Replace@ equality@ between@ two@ results@ of@ a@ function@ by@ equalities@ between@ parameters."
