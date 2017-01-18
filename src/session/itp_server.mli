
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

(*
  val get_configs: unit -> Whyconf.config * Whyconf.config
 *)
  (* Initialize server_data *)
  val init_server: Whyconf.config -> Env.env -> unit

  (* Nothing ! *)

end
