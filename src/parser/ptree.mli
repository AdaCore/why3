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

(*s Parse trees. *)

type loc = Loc.position

(*s Logical expressions (for both terms and predicates) *)

type real_constant = Term.real_constant
type constant = Term.constant

type pp_quant =
  | PPforall | PPexists

type pp_infix = 
  | PPand | PPor | PPimplies | PPiff 

type pp_prefix = 
  | PPnot

type ident = { id : string; id_loc : loc }

type qualid =
  | Qident of ident
  | Qdot of qualid * ident

type pty =
  | PPTtyvar of ident
  | PPTtyapp of pty list * qualid

type pattern =
  { pat_loc : loc; pat_desc : pat_desc }

and pat_desc =
  | PPpwild
  | PPpvar of ident
  | PPpapp of qualid * pattern list
  | PPpas of pattern * ident

type uquant =
  ident list * pty

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
  | PPquant of pp_quant * uquant list * lexpr list list * lexpr
  | PPnamed of string * lexpr
  | PPlet of ident * lexpr * lexpr
  | PPmatch of lexpr * (pattern * lexpr) list

(*s Declarations. *)

type plogic_type =
  | PPredicate of pty list
  | PFunction  of pty list * pty

type imp_exp =
  | Import | Export | Nothing

type use = {
  use_theory  : qualid;
  use_as      : ident option;
  use_imp_exp : imp_exp;
}

type clone_subst = {
  ts_subst : (qualid * qualid) list;
  ls_subst : (qualid * qualid) list;
}

type param = ident option * pty

type type_def = 
  | TDabstract
  | TDalias     of pty
  | TDalgebraic of (loc * ident * param list) list

type type_decl = {
  td_loc    : loc;
  td_ident  : ident;
  td_params : ident list;
  td_def    : type_def;
}

type logic_decl = { 
  ld_loc    : loc;
  ld_ident  : ident;
  ld_params : param list;
  ld_type   : pty option;
  ld_def    : lexpr option;
}

type prop_kind =
  | Kaxiom | Klemma | Kgoal

type decl = 
  | TypeDecl of loc * type_decl list
  | Logic of loc * logic_decl list
  | Inductive_def of loc * ident * pty list * (loc * ident * lexpr) list
  | Prop of loc * prop_kind * ident * lexpr
  | UseClone of loc * use * clone_subst option
  | Namespace of loc * ident * decl list

type theory = {
  pt_loc  : loc;
  pt_name : ident;
  pt_decl : decl list;
}

type logic_file = theory list

