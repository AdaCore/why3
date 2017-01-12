open Itp_server

(** Print in Json format *)
val print_request: Format.formatter -> ide_request -> unit
val print_notification: Format.formatter -> notification -> unit

(** Parse from Json format *)
val parse_request: string -> ide_request
val parse_notification: string -> notification
