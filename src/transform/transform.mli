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
type 'a t
type ctxt_t = context t

(* compose two transformations, the underlying datastructures for
   the memoisation are shared *)
val compose : context t -> 'a t -> 'a t

(* apply a transformation and memoise *)
val apply : 'a t -> context -> 'a

(** General constructors *)
(* create a transformation with only one memoisation *)
val register : (context -> 'a) -> 'a t

(* Fold from the first declaration to the last with a memoisation at
   each step *)
val fold : (context -> 'a -> 'a) -> 'a -> 'a t

val fold_env : (context -> 'a -> 'a) -> (env -> 'a) -> 'a t

val fold_map : (context -> 'a * context -> 'a * context) -> 'a -> context t

val map : (context -> context -> context) -> context t

val map_concat : (context -> decl list) -> context t


(* map the element of the list without an environnment.
   A memoisation is performed at each step, and for each elements *)
val elt : (decl -> decl list) -> context t


(** Utils *)

(* Utils *)

val split_goals : context list t

val remove_lemma : context t

exception NotGoalContext
val goal_of_ctxt : context -> prop
(* goal_of_ctxt ctxts return the goal of a goal context
   the ctxt must end with a goal.*)

val identity : context t


val rewrite_elt : 
  (Term.term -> Term.term) -> 
  (Term.fmla -> Term.fmla) -> context t

val rewrite_map : 
  (context -> Term.term -> Term.term) -> 
  (context -> Term.fmla -> Term.fmla) -> context t


val cloned_from : context -> ident -> ident -> bool 

val find_ty : namespace -> string list -> Ty.tysymbol
val find_l : namespace -> string list -> Term.lsymbol
val find_pr : namespace -> string list -> prop
