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

let last_timing = ref 0.

let timing_map : (string, float) Hashtbl.t = Hashtbl.create 17

let init_timing () =
  last_timing := (Unix.times ()).Unix.tms_utime

let timing_step_completed str =
  let now = (Unix.times ()).Unix.tms_utime in
  let consumed = now -. !last_timing in
  last_timing := now;
  try
    let cur = Hashtbl.find timing_map str in
    Hashtbl.replace timing_map str (cur +. consumed)
  with Not_found ->
    Hashtbl.add timing_map str consumed

let get_timings () = timing_map

