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

val qualid_of_lstring : string list -> Ptree.qualid

val cloned_from_ts : Typing.env -> Theory.context -> 
  string list -> string -> Ty.tysymbol -> bool

val cloned_from_ls : Typing.env -> Theory.context -> 
  string list -> string -> Term.lsymbol -> bool

val cloned_from_pr : Typing.env -> Theory.context -> 
  string list -> string -> Theory.prop -> bool
