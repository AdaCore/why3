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

exception AlreadyConnected
exception ConnectionError of string

val connect_external : string -> unit
(** connects to an already running server, with the given socket name

  raise AlreadyConnected if a server is already running
 *)

val connect_internal : unit -> unit
(** starts a new process for a server and connects to it

   raise AlreadyConnected if a server is already running
 *)


val is_connected : unit -> bool
(** checks if a server is already running *)

exception NotConnected
(** all functions below will raise NotConnected if no server is running *)

val disconnect : unit -> unit

val set_max_running_provers : int -> unit

val send_request :
  id:int ->
  timelimit:int ->
  memlimit:int ->
  use_stdin:string option ->
  cmd:string list ->
  unit

val send_interrupt : id:int -> unit

type final_answer = {
  id        : int;
  time      : float;
  timeout   : bool;
  out_file  : string;
  exit_code : int64;
}

type answer =
  | Started of int   (* the request with given id is running but not finished yet *)
  | Finished of final_answer

exception InvalidAnswer of string

val read_answers : blocking:bool -> answer list
