(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Managing the drivers for external provers *)

(** {2 Create a driver} *)

type driver

val load_driver_absolute :  Env.env -> string -> string list -> driver
(** loads a driver from a file
    @param env    environment to interpret theories
    @param string driver file name (absolute path name)
    @param string list additional driver files containing only theories
*)

(** {2 Use a driver} *)

val file_of_task : driver -> string -> string -> Task.task -> string
(** [file_of_task d f th t] produces a filename
    for the prover of driver [d], for a task [t] generated
    from  a goal in theory named [th] of filename [f]
*)

val get_extension : driver -> string
(* return the file extension which is used for this driver *)

val file_of_theory : driver -> string -> Theory.theory -> string
(** [file_of_theory d f th] produces a filename
    for the prover of driver [d], for a theory [th] from filename [f] *)

val call_on_buffer :
  command      : string ->
  limit        : Call_provers.resource_limit ->
  gen_new_file : bool ->
  ?inplace     : bool ->
  filename     : string ->
  printer_mapping : Printer.printer_mapping ->
  driver -> Buffer.t -> Call_provers.server_id


val print_task :
  ?old        : in_channel ->
  driver -> Format.formatter -> Task.task -> unit

val print_theory :
  ?old       : in_channel ->
  driver -> Format.formatter -> Theory.theory -> unit
  (** produce a realization of the given theory using the given driver *)

val prove_task :
  command      : string ->
  limit        : Call_provers.resource_limit ->
  ?old         : string ->
  ?inplace     : bool ->
  ?interactive : bool ->
  driver -> Task.task -> Call_provers.prover_call

(** Split the previous function in two simpler functions *)

(* Apply driver's transformations to the task *)
val prepare_task : driver -> Task.task -> Task.task

val print_task_prepared :
  ?old       : in_channel ->
  driver -> Format.formatter -> Task.task -> Printer.printer_mapping

val prove_task_prepared :
  command      : string ->
  limit        : Call_provers.resource_limit ->
  ?old         : string ->
  ?inplace     : bool ->
  ?interactive : bool ->
  driver -> Task.task -> Call_provers.prover_call

(** Traverse all metas from a driver *)

val syntax_map: driver -> Printer.syntax_map
