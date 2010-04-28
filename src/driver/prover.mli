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

(** Apply printers and registered transformations mentionned in drivers *)

val print_task : Driver.driver -> Format.formatter -> Task.task -> unit

val prove_task :
  ?debug    : bool ->
  command   : string ->
  ?timelimit : int ->
  ?memlimit  : int ->
  Driver.driver -> Task.task -> unit -> Call_provers.prover_result

(** {2 error reporting} *)

type error

exception Error of error

val report : Format.formatter -> error -> unit

