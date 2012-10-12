(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

open Why3

val debug : Debug.flag

type program_decl =
  | PDdecl of Ptree.decl
  | PDpdecl of Ptree.pdecl
  | PDuseclone of Ptree.use_clone
  | PDnamespace of string * bool * (Ptree.loc * program_decl) list

val decl :
  wp:bool -> Pgm_module.t Util.Mstr.t Env.library ->
  Theory.theory Util.Mstr.t ->
  Pgm_module.t Util.Mstr.t ->
  Pgm_module.uc -> (Ptree.loc * program_decl) -> Pgm_module.uc
