(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* useful combinators *)

let const f _ = f

let const2 f _ _ = f

let const3 f _ _ _ = f

let flip f x y = f y x

(* useful iterator on int *)
let rec foldi f acc min max =
  if min > max then acc else foldi f (f acc min) (succ min) max

let mapi f = foldi (fun acc i -> f i::acc) []

(* useful iterator on float *)
let rec iterf f min max step =
  if min > max then () else
    (f min; iterf f (min+.step) max step)

(* boolean fold accumulators *)

exception FoldSkip

let all_fn pr = (fun _ x -> pr x || raise FoldSkip)
let any_fn pr = (fun _ x -> pr x && raise FoldSkip)

let all2_fn pr = (fun _ x y -> pr x y || raise FoldSkip)
let any2_fn pr = (fun _ x y -> pr x y && raise FoldSkip)

type ('z,'a,'c) fold = ('z -> 'a -> 'z) -> 'z -> 'c -> 'z

let all fold pr x = try fold (all_fn pr) true x with FoldSkip -> false
let any fold pr x = try fold (any_fn pr) false x with FoldSkip -> true

type ('z,'a,'b,'c,'d) fold2 = ('z -> 'a -> 'b -> 'z) -> 'z -> 'c -> 'd -> 'z

let all2 fold pr x y = try fold (all2_fn pr) true x y with FoldSkip -> false
let any2 fold pr x y = try fold (any2_fn pr) false x y with FoldSkip -> true

type ('z,'a,'b,'c) foldd =
  ('z -> 'a -> 'z) -> ('z -> 'b -> 'z) -> 'z -> 'c -> 'z

let alld fold pr1 pr2 x =
  try fold (all_fn pr1) (all_fn pr2) true x with FoldSkip -> false

let anyd fold pr1 pr2 x =
  try fold (any_fn pr1) (any_fn pr2) false x with FoldSkip -> true

(* constant boolean function *)
let ttrue _ = true
let ffalse _ = false

let is_sexp_simple_token s =
  let rec loop i =
    i < 0 || (
      match s.[i] with
      | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' | '-' ->
          (* Very conservative for compatiblity with python's sexpdata in bench/test_mlw_printer *)
          loop (pred i)
      | _ -> false ) in
  String.length s > 0 && loop (pred (String.length s))
