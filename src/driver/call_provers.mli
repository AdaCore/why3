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

(** Call provers and parse there outputs *)

type prover_answer =
  | Valid
      (** The task is valid according to the prover *)
  | Invalid
      (** The task is invalid *)
  | Timeout
      (** the task timeout, ie it takes more time than specified *)
  | Unknown of string
      (** The prover can't determine if the task is valid *)
  | Failure of string
      (** The prover reports a failure *)
  | HighFailure
      (** An error occured during the call to the prover or none
          of the given regexps match the output of the prover *)

type prover_result = {
  pr_answer : prover_answer;
  (* The answer of the prover on the given task *)
  pr_output : string;
  (* The output of the prover currently stderr and stdout *)
  pr_time   : float;
  (* The time taken by the prover *)
}

val print_prover_answer : Format.formatter -> prover_answer -> unit
(** Pretty-print a {! prover_answer} *)

val print_prover_result : Format.formatter -> prover_result -> unit
(** Pretty-print a prover_result. The answer and the time are output.
    The output of the prover is printed if and only if the answer is
    a [HighFailure] *)

val debug : Debug.flag
(** debug flag for the calling procedure (option "--debug
    call_prover")
    If set [call_on_buffer] prints on stderr the commandline called
    and the output of the prover.
*)

val call_on_buffer :
  command    : string ->
  ?timelimit : int ->
  ?memlimit  : int ->
  regexps    : (Str.regexp * prover_answer) list ->
  exitcodes  : (int * prover_answer) list ->
  filename   : string ->
  Buffer.t -> unit -> prover_result
(** Call a prover on the task printed in the {!type: Buffer.t} given.

    @param timelimit : set the available time limit (default 0 : unlimited)
    @param memlimit : set the available time limit (default 0 :
    unlimited)

    @param regexps : if the first field match the prover output the
    second field is the answer. Regexp groups present in the first field are
    substituted in the second field (\0,\1,...). The regexp are tested in the
    order of the list.
    @param exitcodes : if the first field is the exit code the second
    field is the answer. No subtitution are done. Exit codes are tested
    in the order of the list and before the regexps.

    @param filename : if the prover doesn't accept stdin, a temporary
    file is used. In the case the suffix of the temporary file is
    [filename] *)

