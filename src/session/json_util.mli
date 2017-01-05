open Itp_server

(* Simplified json value *)
type json_object =
  | Assoc of (string * json_object) list
  | Array of json_object list
  | Int of int
  | Bool of bool
  | Float of float
  | String of string
  | Empty

val print_request: Format.formatter -> ide_request -> unit
val print_notification: Format.formatter -> notification -> unit

val parse_request: json_object -> ide_request
val parse_notification: json_object -> notification
