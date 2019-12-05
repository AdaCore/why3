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
open Pretty

(* The server part of the protocol *)
module type Protocol = sig

  (* Getting request *)
  val get_requests : unit -> ide_request list
  (* Notify *)
  val notify : notification -> unit

end

(* A specific external way to print task. This registered an external printer
   for printing tasks. This is combined with the standard printer (see Pretty).
*)
val add_registered_lang: string -> (Task.task -> any_pp Pp.pp -> any_pp Pp.pp) -> unit

(* Used to update the config after preferences are changed in the ide.
   This is not usable by other IDEs (webide): in the long term a
   request/notification could be added for this kind of interaction. *)
val set_partial_config: Whyconf.config -> unit

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
