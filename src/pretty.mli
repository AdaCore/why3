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
open Ty
open Term
open Theory

val print_ty : formatter -> ty -> unit

val print_term : formatter -> term -> unit

val print_fmla : formatter -> fmla -> unit

val print_decl : formatter -> decl -> unit

val print_decl_or_use : formatter -> decl_or_use -> unit

val print_decl_or_use_list : formatter -> decl_or_use list -> unit

val print_theory : formatter -> theory -> unit
