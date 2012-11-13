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

(** Make protocol for parallelism **)
type pipe = { pin : Unix.file_descr;
              pout: Unix.file_descr }

type t =
 | Sequential
 | Parallel of pipe

val print_pipe: Format.formatter -> pipe -> unit
val print_fd: Format.formatter -> Unix.file_descr -> unit

val read_makeflags: unit -> t
(** Get from the environnement the jobserver created by make *)

val make_jobserver: int -> pipe
(** create a jobserver with the given number of worker *)

val wait_worker: pipe -> unit
(** wait for a free worker *)

val release_worker: pipe -> unit
(** release a worker *)

val from_fd_id : int -> int -> pipe

exception Invalid_fd of Unix.file_descr * pipe
exception Bad_IO of Unix.file_descr * pipe

val print_error: Format.formatter -> exn -> unit
(** print the exceptions of this module *)
