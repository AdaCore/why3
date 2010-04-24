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

(** Useful functions for printer *)

(** {2 exception to use in a transformation } *)

type error =
  | UnsupportedType        of Ty.ty     * string
  | UnsupportedExpression  of Term.expr * string
  | UnsupportedDeclaration of Decl.decl * string
  | NotImplemented         of             string

exception Error of error

val unsupportedType        : Ty.ty     -> string -> 'a
val unsupportedExpression  : Term.expr -> string -> 'a
val unsupportedDeclaration : Decl.decl -> string -> 'a
(** - [expr] is the problematic formula
    - [string] explain the problem and
      possibly a way to solve it (such as applying another
      transforamtion) *)

val notImplemented : string -> 'a
(** [string] explain what is not implemented *)

val report : Format.formatter -> error -> unit

(** function which cath inner error *)
exception Unsupported of string

val unsupported : string -> 'a

val catch_unsupportedtype        : (Ty.ty     -> 'a) -> (Ty.ty     -> 'a)

val catch_unsupportedterm        : (Term.term -> 'a) -> (Term.term -> 'a)

val catch_unsupportedfmla        : (Term.fmla -> 'a) -> (Term.fmla -> 'a)

val catch_unsupportedDeclaration : (Decl.decl -> 'a) -> (Decl.decl -> 'a)
