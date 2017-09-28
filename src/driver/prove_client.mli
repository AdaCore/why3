(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

exception NotConnected
exception AlreadyConnected
exception InvalidAnswer of string

val connect_external : string -> unit
val connect_internal : unit -> unit

val disconnect : unit -> unit

val is_connected : unit -> bool

val send_request :
  id:int ->
  timelimit:int ->
  memlimit:int ->
  use_stdin:string option ->
  cmd:string list ->
  unit

type final_answer = {
  id        : int;
  time      : float;
  timeout   : bool;
  out_file  : string;
  exit_code : int64;
}

type answer =
  | Started of int
  | Finished of final_answer

val read_answers : blocking:bool -> answer list

val set_max_running_provers : int -> unit
