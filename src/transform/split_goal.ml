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

let apply_append  fn = List.fold_left (fun l e -> fn e :: l)
let apply_append2 fn = Util.list_fold_product (fun l e1 e2 -> fn e1 e2 :: l)

let rec split_pos acc f = match f.f_node with
  | Ftrue -> acc
  | Ffalse -> f::acc
  | Fapp _ -> f::acc
  | Fbinop (Fand,f1,f2) ->
      split_pos (split_pos acc f2) f1
  | Fbinop (Fimplies,f1,f2) ->
      apply_append2 f_implies acc (split_neg [] f1) (split_pos [] f2)
  | Fbinop (Fiff,f1,f2) ->
      split_pos (split_pos acc (f_implies f1 f2)) (f_implies f2 f1)
  | Fbinop (For,f1,f2) ->
      apply_append2 f_or acc (split_pos [] f1) (split_pos [] f2)
  | Fnot f ->
      apply_append f_not acc (split_neg [] f)
  | Fif (fif,fthen,felse) ->
      split_pos (split_pos acc (f_implies fif fthen)) (f_or fif felse)
  | Flet (t,fb) -> let vs,f = f_open_bound fb in
      apply_append (f_let vs t) acc (split_pos [] f)
  | Fcase _ -> (* TODO better *) f::acc
  | Fquant (Fforall,fq) -> let vsl,trl,f = f_open_quant fq in
      (* TODO : Remove unused variable *)
      apply_append (f_forall vsl trl) acc (split_pos [] f)
  | Fquant (Fexists,_) -> f::acc

and split_neg acc f = match f.f_node with
  | Ftrue -> f::acc
  | Ffalse -> acc
  | Fapp _ -> f::acc
  | Fbinop (Fand,f1,f2) ->
      apply_append2 f_and acc (split_neg [] f1) (split_neg [] f2)
  | Fbinop (Fimplies,f1,f2) ->
      split_neg (split_neg acc f2) (f_not f1)
  | Fbinop (Fiff,f1,f2) ->
      split_neg (split_neg acc (f_and (f_not f1) (f_not f2))) (f_and f2 f1)
  | Fbinop (For,f1,f2) ->
      split_neg (split_neg acc f2) f1
  | Fnot f ->
      apply_append f_not acc (split_pos [] f)
  | Fif (fif,fthen,felse) ->
      split_neg (split_neg acc (f_and fif fthen)) (f_and (f_not fif) felse)
  | Flet (t,fb) -> let vs,f = f_open_bound fb in
      apply_append (f_let vs t) acc (split_neg [] f)
  | Fcase _ -> (* TODO better *) f::acc
  | Fquant (Fexists,fq) -> let vsl,trl,f = f_open_quant fq in
      (* TODO : Remove unused variable *)
      apply_append (f_exists vsl trl) acc (split_neg [] f)
  | Fquant (Fforall,_) -> f::acc

let make_prop k pr f = [create_prop_decl k pr f]

let split_goal  pr f = List.map (make_prop Pgoal  pr) (split_pos [] f)
let split_axiom pr f = List.map (make_prop Paxiom pr) (split_neg [] f)

let split_decl d = match d.d_node with
  | Dprop (Pgoal, pr,f) -> split_goal  pr f
  | Dprop (Paxiom,pr,f) -> split_axiom pr f
  | _ -> [[d]]

let split_goal = Trans.goal_l split_goal
let split_all  = Trans.decl_l split_decl None

let () = Trans.register_transform_l "split_goal" split_goal
let () = Trans.register_transform_l "split_all"  split_all

