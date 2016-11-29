
open Itp_server

module Protocol_why3ide : sig


  val get_requests: unit -> ide_request list
  val send_request: ide_request -> unit

  val notify: notification -> unit
  val get_notified: unit -> notification list

end
