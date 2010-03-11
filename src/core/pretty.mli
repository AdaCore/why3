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

open Format
open Ident
open Ty
open Term
open Theory

val printer : unit -> ident_printer

val forget_tvs : ?printer:ident_printer -> unit -> unit     
  (* flush id_unique for type vars *)
val forget_var : ?printer:ident_printer -> vsymbol -> unit 
  (* flush id_unique for a variable *)

val print_id : ?printer:ident_printer ->          (* ident *)
  formatter -> ident -> unit         
val print_tv : ?printer:ident_printer ->          (* type variable *)
formatter -> tvsymbol -> unit
val print_ts : ?printer:ident_printer ->          (* type symbol *)
  formatter -> tysymbol -> unit
val print_ty : ?printer:ident_printer ->          (* type *)
  formatter -> ty -> unit
val print_vs : ?printer:ident_printer ->          (* variable *)
  formatter -> vsymbol -> unit
val print_vsty : ?printer:ident_printer ->        (* variable : type *)
  formatter -> vsymbol -> unit
val print_ls : ?printer:ident_printer ->          (* logic symbol *)
  formatter -> lsymbol -> unit
val print_const : formatter -> constant -> unit   (* int/real constant *)
val print_pat : ?printer:ident_printer ->         (* pattern *)
  formatter -> pattern -> unit
val print_term : ?printer:ident_printer ->        (* term *)
  formatter -> term -> unit
val print_fmla : ?printer:ident_printer ->        (* formula *)
  formatter -> fmla -> unit

val print_type_decl : ?printer:ident_printer ->
  formatter -> ty_decl -> unit
val print_logic_decl : ?printer:ident_printer ->
  formatter -> logic_decl -> unit
val print_ind_decl : ?printer:ident_printer ->
  formatter -> ind_decl -> unit

val print_pkind : formatter -> prop_kind -> unit
val print_prop : ?printer:ident_printer ->
  formatter -> prop -> unit

val print_decl : ?printer:ident_printer ->
  formatter -> decl -> unit
val print_decls : ?printer:ident_printer ->
  formatter -> decl list -> unit
val print_context : ?printer:ident_printer ->
  formatter -> context -> unit
val print_theory : ?printer:ident_printer ->
  formatter -> theory -> unit

val print_named_context : ?printer:ident_printer ->
  formatter -> string -> context -> unit

