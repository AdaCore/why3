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

open Model_parser

(** {1 Call provers and parse their outputs} *)

(** {2 data types for prover answers} *)

type prover_answer =
  | Valid
      (** The task is valid according to the prover *)
  | Invalid
      (** The task is invalid *)
  | Timeout
      (** the task timeouts, ie it takes more time than specified *)
  | OutOfMemory
      (** the task runs out of memory *)
  | StepLimitExceeded
      (** the task required more steps than the limit provided *)
  | Unknown of string
      (** The prover can't determine if the task is valid *)
  | Failure of string
      (** The prover reports a failure *)
  | HighFailure
      (** An error occured during the call to the prover or none
          of the given regexps match the output of the prover *)

type prover_result = {
  pr_answer : prover_answer;
  (** The answer of the prover on the given task *)
  pr_status : Unix.process_status;
  (** The process exit status *)
  pr_output : string;
  (** The output of the prover currently stderr and stdout *)
  pr_time   : float;
  (** The time taken by the prover *)
  pr_steps  : int;
  (** The number of steps taken by the prover (-1 if not available) *)
  pr_model  : model;
  (** The model produced by a the solver *)
}

val print_prover_answer : Format.formatter -> prover_answer -> unit
(** Pretty-print a {! prover_answer} *)

val print_prover_result : Format.formatter -> prover_result -> unit
(** Pretty-print a prover_result. The answer and the time are output.
    The output of the prover is printed if and only if the answer is
    a [HighFailure] *)

val debug : Debug.flag
(** debug flag for the calling procedure (option "--debug call_prover")
    If set [call_on_buffer] prints on stderr the commandline called
    and the output of the prover. *)

type timeregexp
(** The type of precompiled regular expressions for time parsing *)

type stepregexp
(** The type of precompiled regular expressions for parsing of steps *)

val timeregexp : string -> timeregexp
(** Converts a regular expression with special markers '%h','%m',
    '%s','%i' (for milliseconds) into a value of type [timeregexp] *)

val stepregexp : string -> int -> stepregexp
(** [stepregexp s n] creates a regular expression to match the number of steps.
    [s] is a regular expression, [n] is the group number with steps number. *)

type prover_result_parser = {
  prp_regexps     : (string * prover_answer) list;
  prp_timeregexps : timeregexp list;
  prp_stepregexps : stepregexp list;
  prp_exitcodes   : (int * prover_answer) list;
  (* The parser for a model returned by the solver. *)
  prp_model_parser : Model_parser.model_parser;
}
(*
    if the first field matches the prover output,
    the second field is the answer. Regexp groups present in
    the first field are substituted in the second field (\0,\1,...).
    The regexps are tested in the order of the list.

    @param timeregexps : a list of regular expressions with special
    markers '%h','%m','%s','%i' (for milliseconds), constructed with
    [timeregexp] function, and used to extract the time usage from
    the prover's output. If the list is empty, wallclock is used.
    The regexps are tested in the order of the list.

    @param exitcodes : if the first field is the exit code, then
    the second field is the answer. Exit codes are tested in the order
    of the list and before the regexps.
*)

(** {2 Functions for calling external provers} *)

type resource_limit = {
  limit_time  : int;
  limit_mem   : int;
  limit_steps : int;
}
(* represents the three ways a prover run can be limited: in time, memory
   and/or steps *)

val empty_limit : resource_limit
(* the limit object which imposes no limits. Use this object to impose no
   limits, but also to know if some concrete time, steps or memlimit actually
   means "no limit" *)

val limit_max : resource_limit -> resource_limit -> resource_limit
(* return the limit object whose components represent the maximum of the
   corresponding components of the arguments *)

type server_id = int
type editor_id

type prover_call =
  | ServerCall of server_id
  | EditorCall of editor_id

val call_editor : command : string -> string -> prover_call

(* internal use only
val call_on_file :
  command         : string ->
  limit           : resource_limit ->
  res_parser      : prover_result_parser ->
  printer_mapping : Printer.printer_mapping ->
  ?inplace        : bool ->
  string -> int
*)

val call_on_buffer :
  command         : string ->
  limit           : resource_limit ->
  res_parser      : prover_result_parser ->
  filename        : string ->
  printer_mapping : Printer.printer_mapping ->
  gen_new_file    : bool ->
  ?inplace        : bool ->
  Buffer.t -> server_id
(** Build a prover call on the task already printed in the {!type: Buffer.t} given.

    @param limit : set the available time limit (def. 0 : unlimited), memory
    limit (def. 0 : unlimited) and step limit (def. -1 : unlimited)

    @param res_parser : prover result parser

    @param filename : the suffix of the proof task's file, if the prover
    doesn't accept stdin.

    @param inplace : it is used to make a save of the file on which the
    prover was called. It is renamed as %f.save if inplace=true and the command
    [actualcommand] fails

    @param gen_new_file: When set, this generates a new temp file to run the
    prover on. Otherwise it reuses the filename already given.

*)

type prover_update =
  | NoUpdates
  | ProverInterrupted
  | InternalFailure of exn
  | ProverStarted
  | ProverFinished of prover_result

val get_new_results: blocking:bool -> (prover_call * prover_update) list
(** returns new results from why3server, in an unordered fashion. *)

val query_call : prover_call -> prover_update
(** non-blocking function that reports any new updates
    from the server related to a given prover call. *)

val interrupt_call : prover_call -> unit
(** non-blocking function that asks for prover interruption *)

val wait_on_call : prover_call -> prover_result
(** blocking function that waits until the prover finishes. *)

val wait_for_server_result :
  blocking:bool -> (server_id * prover_result option) list
