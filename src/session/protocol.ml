
open Itp_server

module Protocol_why3ide  = struct

  let list_requests: ide_request list ref = ref []

  let get_requests () = let l = List.rev !list_requests in list_requests := []; l
  let send_request r = list_requests := r :: !list_requests

  let notification_list: notification list ref = ref []

  let notify r = notification_list := r :: !notification_list
  let get_notified () = let l = List.rev !notification_list in notification_list := []; l

end
