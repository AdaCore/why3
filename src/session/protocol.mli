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

open Itp_server

module Protocol_why3ide : sig


  val get_requests: unit -> ide_request list
  val send_request: ide_request -> unit

  val notify: notification -> unit
  val get_notified: unit -> notification list

end
