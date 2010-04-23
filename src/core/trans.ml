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

open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task

(** Task transformation *)

type 'a trans = task -> 'a
type 'a tlist = 'a list trans

let identity   x = x
let identity_l x = [x]

let conv_res c f x = c (f x)

let singleton f x = [f x]

let compose f g x = g (f x)

let compose_l f g x = list_apply g (f x)

let apply f x = f x

module WHtask = Hashweak.Make (struct
  type t = task_hd
  let tag t = t.task_tag
end)

let store fn = WHtask.memoize_option 63 fn

let fold fn v =
  let h = WHtask.create 63 in
  let rewind acc task =
    let acc = fn task acc in
    WHtask.set h task acc;
    acc
  in
  let current task =
    try Some (WHtask.find h task)
    with Not_found -> None
  in
  let rec accum todo = function
    | None -> List.fold_left rewind v todo
    | Some task -> begin match current task with
        | Some v -> List.fold_left rewind v todo
        | None   -> accum (task::todo) task.task_prev
      end
  in
  accum []

let fold_l fn v = fold (fun task -> list_apply (fn task)) [v]

let fold_map   fn v t = conv_res snd                (fold   fn (v, t))
let fold_map_l fn v t = conv_res (List.rev_map snd) (fold_l fn (v, t))

let map   fn = fold   (fun t1 t2 -> fn t1 t2)
let map_l fn = fold_l (fun t1 t2 -> fn t1 t2)

module WHdecl = Hashweak.Make (struct
  type t = decl
  let tag d = d.d_tag
end)

let decl fn =
  let fn = WHdecl.memoize 63 fn in
  let fn task acc = match task.task_decl with
    | Decl d -> List.fold_left add_decl acc (fn d)
    | td -> add_tdecl acc td
  in
  map fn

let decl_l fn =
  let fn = WHdecl.memoize 63 fn in
  let fn task acc = match task.task_decl with
    | Decl d -> List.rev_map (List.fold_left add_decl acc) (fn d)
    | td -> [add_tdecl acc td]
  in
  map_l fn

let rewrite fnT fnF = decl (fun d -> [decl_map fnT fnF d])

(** exception to use in a transformation *)

type error =
  | UnsupportedExpression of expr * string
  | UnsupportedDeclaration of decl * string
  | NotImplemented of string

exception Error of error

let error e = raise (Error e)

let unsupportedExpression e s = error (UnsupportedExpression (e,s))
let unsupportedDeclaration e s = error (UnsupportedDeclaration (e,s))
let notImplemented s = error (NotImplemented s)

let report fmt = function
  | UnsupportedExpression (e,s) ->
      Format.fprintf fmt
        "@[<hov 3> The transformation doesn't support this expression :@\n\
%a@\n\
%s@]@\n" Pretty.print_expr e s
  | UnsupportedDeclaration (d,s) ->
      Format.fprintf fmt
        "@[<hov 3> The transformation doesn't support this declaration :@\n\
%a@\n\
%s@]@\n" Pretty.print_decl d s
  | NotImplemented (s) ->
      Format.fprintf fmt
        "@[<hov 3> Unimplemented features :@\n%s@]@\n" s
