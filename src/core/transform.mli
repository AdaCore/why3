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

(** General functions *)

(* The type of transformation from list of 'a to list of 'b *)
type ('a,'b) t

(* compose two transformations, the underlying datastructures for
   the memoisation are shared *)
val compose : ('a,'b) t -> ('b,'c) t -> ('a,'c) t

(* apply a transformation and memoise *)
val apply : ('a,'b) t -> 'a -> 'b

(* convert the argument of a transformation without memoisation *)
val conv_arg : ('a,'b) t -> ('c -> 'a) -> ('c,'b) t

(* convert the result of a transformation without memoisation *)
val conv_res : ('a,'b) t -> ('b -> 'c) -> ('a,'c) t

val conv : ('a,'b) t -> ('c -> 'a * 'e)  -> ('b * 'e -> 'd) -> ('c,'d) t

val conv_map : ('a,'b) t -> (('a -> 'b) -> 'c -> 'd) -> ('c,'d) t

val conv_memo : ('a,'b) t -> ('a -> int) -> ('a,'b) t

(* clear the datastructures used to store the memoisation *)
val clear : ('a,'b) t -> unit

(** General constructors *)
val fold_up :
  ?clear:(unit -> unit) ->
  (context -> 'a -> decl -> 'a) -> 'a -> (context,'a) t


val fold_bottom :
  ?tag:('a -> int) ->
  ?clear:(unit -> unit) ->
  (context -> 'a  -> decl -> 'a) -> 'a -> (context,'a) t


val fold_bottom_up :
  ?tag:('a -> int) ->
  ?clear:(unit -> unit) ->
  top:('a -> 'c) ->
  down:('c -> 'b -> 'c) ->
  (context -> 'a  -> decl -> 'a * 'b) -> 'a -> (context,'c) t




(* the general tranformation only one memoisation is performed at the
   beginning *)
val all :
  ?clear:(unit -> unit) ->
  (context -> 'a) -> (context,'a) t

(* map the element of the list from the first to the last. only one
   memoisation is performed at the beginning. But if a tag function is
   given a memoisation is performed at each step *)
val fold_map_bottom :
  ?tag:('a -> int) ->
  ?clear:(unit -> unit) ->
  (context -> 'a -> decl -> 'a * decl list) -> 'a -> (context,context) t

(* map the element of the list from the last to the first.
   A memoisation is performed at each step *)
val fold_map_up :
  ?clear:(unit -> unit) ->
  (context -> 'a -> context -> decl -> ('a * context)) -> 'a -> 
  (context,context) t

(* map the element of the list without an environnment.
   A memoisation is performed at each step, and for each elements *)
val elt :
  ?clear:(unit -> unit) ->
  (decl -> decl list) -> (context,context) t



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
  ind:(ind_decl list -> decl list) ->
  prop:(prop_decl -> decl list) ->
  use:(theory -> decl list) ->
  clone:(theory -> (ident * ident) list -> decl list) ->
  (decl -> decl list)


val fold_context_of_decl:
  (context -> 'a -> decl -> 'a * decl list) ->
  context -> 'a -> context -> decl -> ('a * context)

(* Utils *)
val unit_tag : unit -> int

val split_goals : (context,context list) t

val extract_goals : (context,(Ident.ident * Term.fmla * context) list) t

val identity : ('a,'a) t
