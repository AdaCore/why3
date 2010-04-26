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

(** Register printers and registered transformations, and create
    registered transformations *)

open Env
open Task
open Trans

type 'a trans_reg
type 'a tlist_reg = 'a list trans_reg

val identity   : task trans_reg
val identity_l : task tlist_reg

(** [compose f g] applies [f], then [g] *)
val compose   : task trans_reg -> 'a trans_reg -> 'a trans_reg
val compose_l : task tlist_reg -> 'a tlist_reg -> 'a tlist_reg

val singleton : 'a trans_reg -> 'a tlist_reg

(** Use only with functions working in constant time *)
val conv_res : ('a -> 'b) -> 'a trans_reg -> 'b trans_reg

val clear : 'a trans_reg -> unit

(** {2 Store and apply} *)

type query = Driver.driver_query
type clone = Theory.clone_map
type use   = Theory.use_map

val store       : (unit ->                  'a trans) -> 'a trans_reg
val store_env   : (env  ->                  'a trans) -> 'a trans_reg
val store_use   : (env  -> use           -> 'a trans) -> 'a trans_reg
val store_clone : (env  ->         clone -> 'a trans) -> 'a trans_reg
val store_both  : (env  -> use  -> clone -> 'a trans) -> 'a trans_reg

val store_goal  : (env  ->          task -> 'a trans) -> 'a trans_reg
val store_query : (        query ->         'a trans) -> 'a trans_reg
val store_full  : (        query -> task -> 'a trans) -> 'a trans_reg

exception ArgumentNeeded

val apply_driver : 'a trans_reg -> Driver.driver -> task -> 'a
val apply_env : 'a trans_reg -> env -> task -> 'a
val apply : 'a trans_reg -> task -> 'a

(** {2 Registration} *)

type printer = query -> Format.formatter -> task -> unit

val register_printer     : string -> printer -> unit
val register_transform   : string -> task trans_reg -> unit
val register_transform_l : string -> task tlist_reg -> unit

val lookup_printer     : string -> printer
val lookup_transform   : string -> task trans_reg
val lookup_transform_l : string -> task tlist_reg

val list_printers     : unit -> string list
val list_transforms   : unit -> string list
val list_transforms_l : unit -> string list

(** {2 exceptions to use in transformations and printers } *)

type error =
  | UnsupportedType        of Ty.ty     * string
  | UnsupportedExpression  of Term.expr * string
  | UnsupportedDeclaration of Decl.decl * string
  | NotImplemented         of             string

exception Error of error

val unsupportedType        : Ty.ty     -> string -> 'a
(** [unsupportedType ty s] 
    - [ty] is the problematic formula
    - [s] explain the problem and
      possibly a way to solve it (such as applying another
      transforamtion) *)

val unsupportedExpression  : Term.expr -> string -> 'a

val unsupportedDeclaration : Decl.decl -> string -> 'a

val notImplemented : string -> 'a
(** [notImplemented s]. [s] explains what is not implemented *)

val report : Format.formatter -> error -> unit
(** Pretty print an error *)

(** {3 functions which catch inner error} *)

exception Unsupported of string
(** This exception must be raised only in a inside call of one of the above
    catch_* function *)

val unsupported : string -> 'a
(** convenient function to raise the {! Unsupported} exception *)

val catch_unsupportedtype        : (Ty.ty     -> 'a) -> (Ty.ty     -> 'a)
(** [catch_unsupportedtype f] return a function which applied on [arg] : 
    - return [f arg] if [f arg] doesn't raise the {!
Unsupported} exception.
    -  raise [Error (unsupportedType (arg,s))] if [f arg] 
    raises [Unsupported s]*)

val catch_unsupportedterm        : (Term.term -> 'a) -> (Term.term -> 'a)
  (** same as {! catch_unsupportedtype} but use [UnsupportedExpression]
      instead of [UnsupportedType]*)

val catch_unsupportedfmla        : (Term.fmla -> 'a) -> (Term.fmla -> 'a)
  (** same as {! catch_unsupportedtype} but use [UnsupportedExpression] 
      instead of [UnsupportedType]*)

val catch_unsupportedDeclaration : (Decl.decl -> 'a) -> (Decl.decl -> 'a)
(** same as {! catch_unsupportedtype} but use
    [UnsupportedDeclaration] instead of [UnsupportedType] *)
