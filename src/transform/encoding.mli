(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
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

val meta_base          : Theory.meta
val meta_lsinst        : Theory.meta
val meta_kept          : Theory.meta
val meta_lskept        : Theory.meta

val ft_select_lsinst    : (env,task) Trans.flag_trans
val ft_select_kept      : (env,task) Trans.flag_trans
val ft_select_lskept    : (env,task) Trans.flag_trans
val ft_completion_mode  : (env,task) Trans.flag_trans

val ft_enco_kept : (env,task) Trans.flag_trans
val ft_enco_poly : (env,task) Trans.flag_trans

val monomorphise_goal : Task.task Trans.trans

val encoding_smt  : Env.env -> Task.task Trans.trans
val encoding_tptp : Env.env -> Task.task Trans.trans
