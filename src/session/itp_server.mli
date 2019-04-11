(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2019   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** Server for a client/server communication with an external graphical interface *)

open Itp_communication

(* The server part of the protocol *)
module type Protocol = sig

  val get_requests : unit -> ide_request list
  val notify : notification -> unit

end

module Make (S:Controller_itp.Scheduler) (P:Protocol) : sig

  (* This function is used to change the registered function for
     focus_on_loading. It focuses on the first goal that satisfies the given
     predicate. *)
  val focus_on_loading: (Task.task -> bool) -> unit

  (* Initialize server with the given config, env and filename for the session.
     If send_source is set to true the source mlw files will be sent to the ide
     as notifications. *)
  val init_server:
      ?send_source:bool -> Whyconf.config -> Env.env -> string -> unit

end
