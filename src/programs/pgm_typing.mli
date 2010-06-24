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

open Why
open Theory

val debug : bool ref

type error

exception Error of error

val report : Format.formatter -> error -> unit

(* val errorm : ?loc:Loc.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a *)

val decl : 
  Env.env -> Pgm_env.env -> Pgm_ptree.decl -> Pgm_env.env * Pgm_ttree.decl list

(* TODO: move elsewhere? *)
val reference_of_term : Term.term -> Pgm_effect.reference
