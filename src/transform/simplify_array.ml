(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Term
open Theory
open Env

let prelude = ["map"]
let array = "Map"
let store = ["set"]
let select = ["get"]

let make_rt_rf env =
  let array  =
    try
      read_theory ~format:"why" env prelude array
    with TheoryNotFound (_,s) ->
      Format.eprintf "The theory %s is unknown" s;
      exit 1 in
  let store  = (ns_find_ls array.th_export store).ls_name in
  let select = (ns_find_ls array.th_export select).ls_name in
  let rec rt t =
    let t = TermTF.t_map rt rf t in
    match t.t_node with
      | Tapp (lselect,[{t_node=Tapp(lstore,[_;a1;b])};a2])
          when lselect.ls_name == select &&
            lstore.ls_name == store &&
            t_equal_alpha a1 a2 -> b
      | _ -> t
  and rf f = TermTF.t_map rt rf f  in
  rt,rf

let t env = let rt,rf = make_rt_rf env in Trans.rewriteTF rt rf None

let () = Trans.register_env_transform "simplify_array" t
  ~desc:"Apply,@ wherever@ possible,@ the@ axiom@ 'Select_eq'@ of@ \
         the@ library@ theory@ map.Map."
