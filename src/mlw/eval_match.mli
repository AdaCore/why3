(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ty
open Term
open Pdecl

val ts_constructors : known_map -> tysymbol -> Decl.constructor list
val ty_constructors : known_map -> ty -> Decl.constructor list
val cs_fields : known_map -> lsymbol -> lsymbol option list
val select_field : lsymbol -> lsymbol option list -> 'a list -> 'a

val eval_match : known_map -> term -> term
