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

type loc = Loc.position

type ident = Ptree.ident

type qualid = Ptree.qualid

type constant = Term.constant

type assertion_kind = Aassert | Aassume | Acheck

type lexpr = Ptree.lexpr

type loop_annotation = {
  loop_invariant : lexpr option;
  loop_variant   : lexpr option;
}

type expr = {
  expr_desc : expr_desc;
  expr_loc  : loc;
}

and expr_desc =
  | Econstant of constant
  | Eident of qualid
  | Eapply of expr * expr
  | Esequence of expr * expr
  | Eif of expr * expr * expr
  | Eskip 
  | Eassert of assertion_kind * lexpr
  | Elazy_and of expr * expr
  | Elazy_or of expr * expr
  | Elet of ident * expr * expr
  | Eghost of expr
  | Elabel of ident * expr
  | Ewhile of expr * loop_annotation * expr

type decl =
  | Dcode  of ident * expr
  | Dlogic of Ptree.decl list

type file = decl list

