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
open Ty
open Term
open Decl
open Theory
open Task

(** Register printers *)

type prelude = string list
type prelude_map = prelude Mid.t

type 'a pp = Format.formatter -> 'a -> unit

type printer = prelude -> prelude_map -> task pp

val register_printer : string -> printer -> unit

val lookup_printer : string -> printer

val list_printers : unit -> string list

(** {2 use printers} *)

val print_prelude : prelude pp
val print_th_prelude : task -> prelude_map pp

val meta_remove_type : string
val meta_remove_logic : string
val meta_remove_prop : string

val meta_syntax_type : string
val meta_syntax_logic : string

val remove_type : tysymbol -> tdecl
val remove_logic : lsymbol -> tdecl
val remove_prop : prsymbol -> tdecl

val syntax_type : tysymbol -> string -> tdecl
val syntax_logic : lsymbol -> string -> tdecl

val get_remove_set : task -> Sid.t
val get_syntax_map : task -> string Mid.t

val syntax_arguments : string -> 'a pp -> 'a list pp
(** (syntax_arguments templ print_arg fmt l) prints in the formatter fmt
     the list l using the template templ and the printer print_arg *)

(** {2 exceptions to use in transformations and printers} *)

exception UnsupportedType of ty   * string
exception UnsupportedExpr of expr * string
exception UnsupportedDecl of decl * string
exception NotImplemented  of        string

val unsupportedType : ty   -> string -> unit
val unsupportedTerm : term -> string -> unit
val unsupportedFmla : fmla -> string -> unit
val unsupportedExpr : expr -> string -> unit
val unsupportedDecl : decl -> string -> unit
val notImplemented  :         string -> unit

(** {3 functions that catch inner error} *)

exception Unsupported of string
(** This exception must be raised only inside a call
    of one of the catch_* functions below *)

val unsupported : string -> unit

val catch_unsupportedType : (ty -> 'a) -> (ty -> 'a)
(** [catch_unsupportedType f] return a function which applied on [arg]:
    - return [f arg] if [f arg] does not raise {!Unsupported} exception
    - raise [UnsupportedType (arg,s)] if [f arg] raises [Unsupported s]*)

val catch_unsupportedTerm : (term -> 'a) -> (term -> 'a)
(** same as {! catch_unsupportedType} but use [UnsupportedExpr]
    instead of [UnsupportedType]*)

val catch_unsupportedFmla : (fmla -> 'a) -> (fmla -> 'a)
(** same as {! catch_unsupportedType} but use [UnsupportedExpr]
    instead of [UnsupportedType]*)

val catch_unsupportedExpr : (expr -> 'a) -> (expr -> 'a)
(** same as {! catch_unsupportedType} but use [UnsupportedExpr]
    instead of [UnsupportedType]*)

val catch_unsupportedDecl : (decl -> 'a) -> (decl -> 'a)
(** same as {! catch_unsupportedType} but use [UnsupportedDecl]
    instead of [UnsupportedType] *)

