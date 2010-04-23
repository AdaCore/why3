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
open Task

(** Task transformation *)

type 'a trans
type 'a tlist = 'a list trans

val identity   : task trans
val identity_l : task tlist

val apply : 'a trans -> (task -> 'a)
val store : (task -> 'a) -> 'a trans

val singleton : 'a trans -> 'a tlist

val compose   : task trans -> 'a trans -> 'a trans
val compose_l : task tlist -> 'a tlist -> 'a tlist

(* Should be only used with functions working in constant time *)
(* val conv_res : ('a -> 'b) -> 'a trans -> 'b trans *)

val fold   : (task_hd -> 'a -> 'a     ) -> 'a -> 'a trans
val fold_l : (task_hd -> 'a -> 'a list) -> 'a -> 'a tlist

val fold_map   : (task_hd -> 'a * task -> ('a * task)) ->
                                      'a -> task -> task trans

val fold_map_l : (task_hd -> 'a * task -> ('a * task) list) ->
                                      'a -> task -> task tlist

val map   : (task_hd -> task -> task     ) -> task -> task trans
val map_l : (task_hd -> task -> task list) -> task -> task tlist

val decl   : (decl -> decl list     ) -> task -> task trans
val decl_l : (decl -> decl list list) -> task -> task tlist

val tdecl   : (decl -> tdecl list     ) -> task -> task trans
val tdecl_l : (decl -> tdecl list list) -> task -> task tlist

val rewrite : (term -> term) -> (fmla -> fmla) -> task -> task trans

(** exception to use in a transformation *)

type error =
  | UnsupportedExpression of expr * string
  | UnsupportedDeclaration of decl * string
  | NotImplemented of string

exception Error of error

val unsupportedExpression : expr -> string -> 'a
val unsupportedDeclaration : decl -> string -> 'a
(** - [expr] is the problematic formula
    - [string] explain the problem and
      possibly a way to solve it (such as applying another
      transforamtion) *)

val notImplemented : string -> 'a
(** [string] explain what is not implemented *)

val report : Format.formatter -> error -> unit

