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
type ctxt_list_t = context list t

(* compose two transformations, the underlying datastructures for
   the memoisation are shared *)
val compose : context t -> 'a t -> 'a t

val compose' : context list t -> 'a list t -> 'a list t

val singleton : 'a t -> 'a list t 


(* apply a transformation and memoise *)
val apply : 'a t -> context -> 'a

(** General constructors *)
(* create a transformation with only one memoisation *)
val register : (context -> 'a) -> 'a t

(* Fold from the first declaration to the last with a memoisation at
   each step *)
(* val fold : (context -> 'a -> 'a) -> 'a -> 'a t *)

val fold : (context -> 'a -> 'a) -> (env -> 'a) -> 'a t

val fold' : (context -> 'a -> 'a list) -> (env -> 'a) -> 'a list t

val fold_map : (context -> 'a * context -> 'a * context) 
  -> (env -> 'a) -> context t
(* via fold *)

val fold_map' : (context -> 'a * context -> ('a * context) list) 
  -> (env -> 'a) -> context list t

val map : (context -> context -> context) -> context t
(* via fold *)

val map' : (context -> context -> context list) -> context list t
(*
val map_concat : (context -> decl list) -> context t

val map_concat' : (context -> decl list list) -> context list t
*)

(* map the element of the list without an environnment.
   A memoisation is performed at each step, and for each elements *)
val elt : (decl -> decl list) -> context t
(* via map *)

val elt' : (decl -> decl list list) -> context list t

val elt_env : (env -> (decl -> decl list)) -> context t
(* via map *)

val elt_env' : (env -> (decl -> decl list list)) -> context list t


(** Utils *)

(* Utils *)

val split_goals : unit -> context list t

exception NotGoalContext
val goal_of_ctxt : context -> prop
(* goal_of_ctxt ctxts return the goal of a goal context
   the ctxt must end with a goal.*)

val identity : context t


val rewrite_elt : 
  (Term.term -> Term.term) -> 
  (Term.fmla -> Term.fmla) -> context t
(* via elt *) 

val rewrite_env : 
  (env -> Term.term -> Term.term) -> 
  (env -> Term.fmla -> Term.fmla) -> context t
(* via elt_env *)

(*val rewrite_map : 
  (context -> Term.term -> Term.term) -> 
  (context -> Term.fmla -> Term.fmla) -> context t
(* via map *)
*)

val cloned_from : context -> ident -> ident -> bool 

val find_ts : namespace -> string list -> Ty.tysymbol
val find_ls : namespace -> string list -> Term.lsymbol
val find_pr : namespace -> string list -> prop
