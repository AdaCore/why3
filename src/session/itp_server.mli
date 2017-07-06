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

open Itp_communication

val print_request: Format.formatter -> ide_request -> unit
val print_msg: Format.formatter -> message_notification -> unit
val print_notify: Format.formatter -> notification -> unit

(* The server part of the protocol *)
module type Protocol = sig

  val get_requests : unit -> ide_request list
  val notify : notification -> unit

end

module Make (S:Controller_itp.Scheduler) (P:Protocol) : sig

  type focus =
  | Unfocused
  | Focus_on of Session_itp.any
  | Wait_focus

  (* This is used to externally assert the focused mode *)
  val focused_node: focus ref

  (* This function is used to change the registered function for label detection
   and focusing. This is used for a feature which allows to focus automatically
   on a node whose task contains a specific label. So, the registered function
   typically returns true if the label is detected in the task and false
   otherwise.
   By default, no such functions are provided nor needed for classic behavior.
  *)
  val register_label_detection: (Task.task -> bool) -> unit


  (* Initialize server with the given config, env and filename for the session *)
  val init_server: Whyconf.config -> Env.env -> string -> unit

end
