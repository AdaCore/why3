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

type pp_binop =
  | PPand | PPor | PPimplies | PPiff

type pp_unop =
  | PPnot

type ident = { id : string; id_loc : loc }

type qualid =
  | Qident of ident
  | Qdot of qualid * ident

type pty =
  | PPTtyvar of ident
  | PPTtyapp of pty list * qualid
  | PPTtuple of pty list

type param = ident option * pty

type pattern =
  { pat_loc : loc; pat_desc : pat_desc }

and pat_desc =
  | PPpwild
  | PPpvar of ident
  | PPpapp of qualid * pattern list
  | PPptuple of pattern list
  | PPpor of pattern * pattern
  | PPpas of pattern * ident

type lexpr =
  { pp_loc : loc; pp_desc : pp_desc }

and pp_desc =
  | PPvar of qualid
  | PPapp of qualid * lexpr list
  | PPtrue
  | PPfalse
  | PPconst of constant
  | PPinfix of lexpr * ident * lexpr
  | PPbinop of lexpr * pp_binop * lexpr
  | PPunop of pp_unop * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPquant of pp_quant * param list * lexpr list list * lexpr
  | PPnamed of string * lexpr
  | PPlet of ident * lexpr * lexpr
  | PPeps of ident * pty * lexpr
  | PPmatch of lexpr * (pattern * lexpr) list
  | PPcast of lexpr * pty
  | PPtuple of lexpr list

(*s Declarations. *)

type plogic_type =
  | PPredicate of pty list
  | PFunction  of pty list * pty

type imp_exp =
  | Import | Export | Nothing

type use = {
  use_theory  : qualid;
  use_as      : ident option option;
  use_imp_exp : imp_exp;
}

type clone_subst =
  | CStsym  of qualid * qualid
  | CSlsym  of qualid * qualid
  | CSlemma of qualid
  | CSgoal  of qualid

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

type ind_decl = {
  in_loc    : loc;
  in_ident  : ident;
  in_params : param list;
  in_def    : (loc * ident * lexpr) list;
}

type prop_kind =
  | Kaxiom | Klemma | Kgoal

type metarg =
  | PMAts  of qualid
  | PMAls  of qualid
  | PMApr  of qualid
  | PMAstr of string
  | PMAint of string

type decl =
  | TypeDecl of type_decl list
  | LogicDecl of logic_decl list
  | IndDecl of ind_decl list
  | PropDecl of loc * prop_kind * ident * lexpr
  | UseClone of loc * use * clone_subst list option
  | Namespace of loc * bool * ident option * decl list
  | Meta of loc * ident * metarg list

type theory = {
  pt_loc  : loc;
  pt_name : ident;
  pt_decl : decl list;
}

type logic_file = theory list

