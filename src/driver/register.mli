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
type clone = Ident.Sid.t Ident.Mid.t
type use   = Theory.theory Ident.Mid.t

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
  | UnsupportedType of Ty.ty     * string
  | UnsupportedExpr of Term.expr * string
  | UnsupportedDecl of Decl.decl * string
  | NotImplemented  of             string

exception Error of error

val unsupportedType : Ty.ty -> string -> 'a
(** [unsupportedType ty s]
    - [ty] is the problematic type
    - [s] explain the problem and
      possibly a way to solve it (such as applying another
      transforamtion) *)

val unsupportedTerm : Term.term -> string -> 'a
val unsupportedFmla : Term.fmla -> string -> 'a
val unsupportedExpr : Term.expr -> string -> 'a
val unsupportedDecl : Decl.decl -> string -> 'a
val notImplemented  : string -> 'a
(** [notImplemented s]. [s] explains what is not implemented *)

val report : Format.formatter -> error -> unit
(** Pretty print an error *)

(** {3 functions which catch inner error} *)

exception Unsupported of string
(** This exception must be raised only inside a call
    of one of the catch_* functions below *)

val unsupported : string -> 'a
(** convenient function to raise the {! Unsupported} exception *)

val catch_unsupportedType : (Ty.ty -> 'a) -> (Ty.ty -> 'a)
(** [catch_unsupportedType f] return a function which applied on [arg]:
    - return [f arg] if [f arg] does not raise {!Unsupported} exception
    - raise [Error (unsupportedType (arg,s))] if [f arg]
    raises [Unsupported s]*)

val catch_unsupportedTerm : (Term.term -> 'a) -> (Term.term -> 'a)
(** same as {! catch_unsupportedType} but use [UnsupportedExpr]
    instead of [UnsupportedType]*)

val catch_unsupportedFmla : (Term.fmla -> 'a) -> (Term.fmla -> 'a)
(** same as {! catch_unsupportedType} but use [UnsupportedExpr]
    instead of [UnsupportedType]*)

val catch_unsupportedExpr : (Term.expr -> 'a) -> (Term.expr -> 'a)
(** same as {! catch_unsupportedType} but use [UnsupportedExpr]
    instead of [UnsupportedType]*)

val catch_unsupportedDecl : (Decl.decl -> 'a) -> (Decl.decl -> 'a)
(** same as {! catch_unsupportedType} but use [UnsupportedDecl]
    instead of [UnsupportedType] *)

