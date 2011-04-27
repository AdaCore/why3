(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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

open Env
open Theory
open Task
open Trans

val debug : Debug.flag

val meta_kept : meta
val meta_kept_array : meta
val meta_base : meta

val ft_enco_select : (env,task) Trans.flag_trans
val ft_enco_kept   : (env,task) Trans.flag_trans
val ft_enco_poly   : (env,task) Trans.flag_trans

val monomorphise_goal : Task.task Trans.trans
val encoding_smt  : Env.env -> Task.task Trans.trans
val encoding_tptp : Env.env -> Task.task Trans.trans

