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

open Itp_communication

(** Print in Json format *)
val print_request: Format.formatter -> ide_request -> unit
val print_notification: Format.formatter -> notification -> unit

val print_list_request: Format.formatter -> ide_request list -> unit
val print_list_notification: Format.formatter -> notification list -> unit

(** Parse from Json format *)
val parse_request: string -> ide_request
val parse_notification: string -> notification

val parse_list_request: string -> ide_request list
val parse_list_notification: string -> notification list
