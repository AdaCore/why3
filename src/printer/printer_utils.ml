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
open Ty

(** exception to use in a printer *)

type error =
  | UnsupportedType        of ty    * string
  | UnsupportedExpression  of expr  * string
  | UnsupportedDeclaration of decl  * string
  | NotImplemented         of         string

exception Error of error

let error e = raise (Error e)

let unsupportedType e s = error (UnsupportedType (e,s))
let unsupportedExpression e s = error (UnsupportedExpression (e,s))
let unsupportedDeclaration e s = error (UnsupportedDeclaration (e,s))
let notImplemented s = error (NotImplemented s)

let report fmt = function
  | UnsupportedType (e,s) ->
      let msg = "The printer doesn't support this type" in
      Format.fprintf fmt
        "@[<hov 3> %s:@\n%a@\n%s@]@\n" msg Pretty.print_ty e s
  | UnsupportedExpression (e,s) ->
      let msg = "The printer doesn't support this expression" in
      Format.fprintf fmt
        "@[<hov 3> %s:@\n%a@\n%s@]@\n" msg Pretty.print_expr e s
  | UnsupportedDeclaration (d,s) ->
      let msg = "The printer doesn't support this declaration" in
      Format.fprintf fmt
        "@[<hov 3> %s:@\n%a@\n%s@]@\n" msg Pretty.print_decl d s
  | NotImplemented (s) ->
      Format.fprintf fmt "@[<hov 3> Unimplemented feature:@\n%s@]@\n" s

(** function which cath inner error *)
exception Unsupported of string

let unsupported s = raise (Unsupported s)

let catch_unsupportedtype f ty =
  try f ty with Unsupported s -> unsupportedType ty s 

let catch_unsupportedterm f t =
  try f t with Unsupported s -> unsupportedExpression (Term t) s 

let catch_unsupportedfmla f t =
  try f t with Unsupported s -> unsupportedExpression (Fmla t) s 

let catch_unsupportedDeclaration f d =
  try f d with Unsupported s -> unsupportedDeclaration d s 
