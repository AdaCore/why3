(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Managing the drivers for external provers *)

(** {2 Create a driver} *)

type driver

(** Loading drivers *)

val load_driver_file_and_extras :
  Whyconf.main -> Env.env -> extra_dir:string option ->
  string -> (string * string list) list -> driver
(** [load_driver_file_and_extras main env ~extra_dir file extras]
   loads the driver in file [file] and with additional drivers in list
   [extras], in the context of the configuration [main] and
   environment [env]. When not [None], [extra_dir] is an additional
   directory where to look for [file] *)

val load_driver_for_prover :
  Whyconf.main -> Env.env -> Whyconf.config_prover -> driver
(** [load_driver main env p] loads the driver for prover [p], in the
   context of the configuration [main] and environment [env].*)

val resolve_driver_name : Whyconf.main -> string -> extra_dir:string option -> string -> string
(** [resolve_driver_name main dir ?extra_dir name] resolves the driver
   name [name] into a file name. [dir] is the name of the subdirectory
   of DATADIR where driver files are expected to be. [extra_dir] is
   an optional extra directory to search into.  *)

(** {2 Use a driver} *)

val file_of_task : driver -> string -> string -> Task.task -> string
(** [file_of_task d f th t] produces a filename
    for the prover of driver [d], for a task [t] generated
    from  a goal in theory named [th] of filename [f]
*)

val file_of_theory : driver -> string -> Theory.theory -> string
(** [file_of_theory d f th] produces a filename
    for the prover of driver [d], for a theory [th] from filename [f] *)

val get_filename : driver ->
  input_file:string ->
  theory_name:string ->
  goal_name:string ->
  string
(** Mangles a filename for the prover of the given driver *)

val print_task :
  ?old       : in_channel ->
  driver -> Format.formatter -> Task.task -> unit
(** Prepare the task for the prover and prints it *)

val print_theory :
  ?old       : in_channel ->
  driver -> Format.formatter -> Theory.theory -> unit
  (** produce a realization of the given theory using the given driver *)

val prove_task :
  command      : string ->
  config       : Whyconf.main ->
  limits       : Call_provers.resource_limits ->
  ?old         : string ->
  ?inplace     : bool ->
  ?interactive : bool ->
  driver -> Task.task -> Call_provers.prover_call

(** Split the previous function in two simpler functions *)

(** Apply driver's transformations to the task *)
val prepare_task : driver -> Task.task -> Task.task

val print_task_prepared :
  ?old       : in_channel ->
  driver -> Format.formatter -> Task.task -> Printer.printing_info

(** Call prover on a task prepared by [prepare_task]. *)
val prove_task_prepared :
  command      : string ->
  config       : Whyconf.main ->
  limits       : Call_provers.resource_limits ->
  ?old         : string ->
  ?inplace     : bool ->
  ?interactive : bool ->
  driver -> Task.task -> Call_provers.prover_call

(** Call prover on a task already prepared and printed in the buffer.

    The task shall be prepared by [prepare_task] and printed with
    [print_task_prepared]; the buffer shall contain nothing else.

    Parameters [input_file], [theory_name] and [goal_name] are used
    to generate canonical temporary files for the prover according to its driver
    definition. They are purely informative and their respective default
    values are ["f"], ["T"] and ["vc"].

    Parameter [get_model] shall be passed to obtain couter examples.
    The printing-infos are those obtained from task preparation.
*)
val prove_buffer_prepared :
  command      : string ->
  config       : Whyconf.main ->
  limits       : Call_provers.resource_limits ->
  ?input_file  : string ->
  ?theory_name : string ->
  ?goal_name   : string ->
  ?get_model   : Printer.printing_info ->
  driver -> Buffer.t -> Call_provers.prover_call

(** Traverse all metas from a driver *)

val syntax_map: driver -> Printer.syntax_map

(** Information on counterexample generation *)

val meta_get_counterexmp : Theory.meta
(** Set in drivers that generate counterexamples *)

val get_counterexmp : Task.task -> bool
(** Returns true if counterexample should be get for the task (according to
    [meta_get_counterexmp]. *)
