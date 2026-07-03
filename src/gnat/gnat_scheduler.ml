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

    let timeout ~ms f =
      ignore ms;
      timeout_handler := Some f

    let timers : (float * (unit -> unit)) list ref = ref []

    let register_timer delay cb =
      timers := (Unix.gettimeofday () +. delay, cb) :: !timers

    let fire_due_timers () =
      let now = Unix.gettimeofday () in
      let due, rest = List.partition (fun (deadline, _) -> deadline <= now) !timers in
      timers := rest;
      List.iter (fun (_, cb) -> cb ()) due

    let next_timer_delay () =
      match !timers with
      | [] -> None
      | (deadline, _) :: rest ->
          let next =
            List.fold_left
              (fun acc (deadline, _) -> min acc deadline)
              deadline rest
          in
          Some (Float.max 0. (next -. Unix.gettimeofday ()))

     let main_loop ending =
       let finished = ref false in
       while not !finished do
         fire_due_timers ();
         match !timeout_handler, next_timer_delay () with
         | None, None ->
             finished := true
         | None, Some d ->
             if d > 0. then Unix.sleepf d
         | Some f, delay ->
             Why3.Prove_client.set_block_timeout delay;
             if f () then () else timeout_handler := None
       done;
       ending ()

end
