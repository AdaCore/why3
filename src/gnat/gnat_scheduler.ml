module Gnat_scheduler = struct

    let blocking = true

    (* Put an arbitrarily high multiplier here to pass more task to the
       why3server when in gnatwhy3 mode
    *)
    let multiplier = 50

    let idle ~(prio:int) f =
      while f () do ()
      done

    let timeout_handler : (unit -> bool) option ref = ref None

    let timeout ~ms f = timeout_handler := Some f

     let main_loop ending =
       try
         while true do
          match !timeout_handler with
          | None -> raise Exit
          | Some f -> if f () then () else timeout_handler := None
         done;
         raise Exit
       with Exit -> ending ()

end
