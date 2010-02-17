(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Francois Bobot, Jean-Christophe Filliatre,              *)
(*  Johannes Kanig and Andrei Paskevich.                                  *)
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

(*s Parse trees. *)

type loc = Loc.position

(*s Logical expressions (for both terms and predicates) *)

type real_constant = 
  | RConstDecimal of string * string * string option (* int / frac / exp *)
  | RConstHexa of string * string * string

type constant =
  | ConstInt of string
  | ConstFloat of real_constant

type pp_infix = 
  PPand | PPor | PPimplies | PPiff |
  PPlt | PPle | PPgt | PPge | PPeq | PPneq |
  PPadd | PPsub | PPmul | PPdiv | PPmod

type pp_prefix = 
  PPneg | PPnot

type ident = { id : string; id_loc : loc }

type qualid =
  | Qident of ident
  | Qdot of ident * ident

type ppure_type =
(*
  | PPTint
  | PPTbool
  | PPTreal
  | PPTunit
*)
  | PPTvarid of ident
  | PPTexternal of ppure_type list * qualid

type lexpr = 
  { pp_loc : loc; pp_desc : pp_desc }

and pp_desc =
  | PPvar of qualid
  | PPapp of qualid * lexpr list
  | PPtrue
  | PPfalse
  | PPconst of constant
  | PPinfix of lexpr * pp_infix * lexpr
  | PPprefix of pp_prefix * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of ident * ppure_type * lexpr list list * lexpr
  | PPexists of ident * ppure_type * lexpr
  | PPnamed of string * lexpr
  | PPlet of ident* lexpr * lexpr
  | PPmatch of lexpr * ((qualid * ident list * loc) * lexpr) list

(*s Declarations. *)

type external_ = bool

type plogic_type =
  | PPredicate of ppure_type list
  | PFunction of ppure_type list * ppure_type

type uses = ident

type logic_decl = 
  | Logic of loc * external_ * ident list * plogic_type
  | Predicate_def of loc * ident * (loc * ident * ppure_type) list * lexpr
  | Inductive_def of loc * ident * plogic_type * (loc * ident * lexpr) list
  | Function_def 
      of loc * ident * (loc * ident * ppure_type) list * ppure_type * lexpr
  | Axiom of loc * ident * lexpr
  | Goal of loc * ident * lexpr
  | TypeDecl of loc * external_ * ident list * ident
  | AlgType of (loc * ident list * ident
      * (loc * ident * ppure_type list) list) list
  | Theory of loc * ident * uses list * logic_decl list

type logic_file = logic_decl list
