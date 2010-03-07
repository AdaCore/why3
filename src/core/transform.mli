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
open Theory

(* Tranformation on context with some memoisations *)

(* The type of transformation from list of 'a to list of 'b *)
type 'a  t

(* compose two transformations, the underlying datastructures for
   the memoisation are shared *)
val compose : context t -> 'a t -> 'a t

(* apply a transformation and memoise *)
val apply : 'a t -> context -> 'a

(* clear the datastructures used to store the memoisation *)
val clear : 'a t -> unit

(* the general tranformation only one memoisation is performed at the
   beginning *)
val all :
  ?clear:(unit -> unit) ->
  (context -> 'a) -> 'a t

(* map the element of the list from the first to the last. only one
   memoisation is performed at the beginning. But if a tag function is
   given a memoisation is performed at each step *)
val fold_map_bottom :
  ?tag:('a -> int) ->
  ?clear:(unit -> unit) ->
  (context -> 'a -> decl -> 'a * decl list) -> 'a -> context t

(* map the element of the list from the last to the first.
   A memoisation is performed at each step *)
val fold_map_up :
  ?clear:(unit -> unit) ->
  (context -> 'a -> context -> decl -> ('a * context)) -> 'a -> context t

(* map the element of the list without an environnment.
   A memoisation is performed at each step, and for each elements *)
val elt :
  ?clear:(unit -> unit) ->
  (decl -> decl list) -> context t


val fold_bottom :
  ?tag:('a -> int) ->
  ?clear:(unit -> unit) ->
  (context -> 'a  -> decl -> 'a) -> 'a -> 'a t


val fold_up :
  ?clear:(unit -> unit) ->
  (context -> 'a -> decl -> 'a) -> 'a -> 'a t



(*type odecl =
  | Otype of ty_decl
  | Ologic of logic_decl
  | Oprop of prop_decl
  | Ouse   of theory
  | Oclone of (ident * ident) list
*)
val elt_of_oelt :
  ty:(ty_decl -> ty_decl) ->
  logic:(logic_decl -> logic_decl) ->
  ind:(ind_decl -> ind_decl) ->
  prop:(prop_decl -> decl list) ->
  use:(theory -> decl list) ->
  clone:((ident * ident) list -> decl list) ->
  (decl -> decl list)


val fold_context_of_decl:
  (context -> 'a -> decl -> 'a * decl list) ->
  context -> 'a -> context -> decl -> ('a * context)

