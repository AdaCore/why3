module Gnat_scheduler = struct

  (* TODO For idle, we currently still use wait_for_idle and idle list because
     in schedule_transformation, there is probably a callback just after the
     call to idle which needs to be performed *before* actually calling the
     idled function
   *)

    let blocking = true

    (* Put an arbitrarily high multiplier here to pass more task to the
       why3server when in gnatwhy3 mode
    *)
    let multiplier = 50

    (* the private list of functions to call on idle. *)
    let idle_handler : (unit -> bool) list ref = ref []

    (* [insert_idle_handler p f] inserts [f] as a new function to call
       on idle. *)
    let insert_idle_handler f =
      idle_handler := !idle_handler @ [f]

    let wait_for_idle () =
      try
        while true do
          match !idle_handler with
          | f :: rem ->
              idle_handler := rem;
              let b = f () in
              if b then insert_idle_handler f
          | [] -> raise Exit
        done
      with Exit -> ()

    (* Idle corresponds to transformations. In this mode, we want
       transformations to be executed directly, thats why we use wait_for_idle.
    *)
    let idle ~(prio:int) f =
      insert_idle_handler f;
      wait_for_idle ()

    (* the private list of functions to call on timeout. *)
    let timeout_handler : (float * float * (unit -> bool)) list ref = ref []

    let insert_timeout_handler ms t f =
      let rec aux l =
       match l with
          | [] -> [ms,t,f]
          | (_,t1,_) as hd :: rem ->
             if t < t1 then (ms,t,f) :: l else hd :: aux rem
      in
      timeout_handler := aux !timeout_handler

    (* public function to register a task to run on timeout. We still need to
       have this kind of function because we cannot run everything just once, we
       apparently need to reschedule a pass with counterexamples for example.  *)
    let timeout ~ms f =
      assert (ms > 0);
      let ms = float ms /. 1000.0 in
      let time = Unix.gettimeofday () in
      insert_timeout_handler ms (time +. ms) f

     let main_loop ending =
       try
         if !timeout_handler = [] && !idle_handler = [] then
           raise Exit;

         (* This is not an infinite loop because the observer registered in
            gnat_objectives (register_observer) also raise Exit when nothing is
            left to do. *)
         while true do
           (* In this mode we only run timeout handler. *)
           let time = Unix.gettimeofday () in
           match !timeout_handler with
           | (ms,t,f) :: rem when t <= time ->
              timeout_handler := rem;
              let b = f () in
              let time = Unix.gettimeofday () in
              if b then insert_timeout_handler ms (ms +. time) f
           | _ ->
             (* TODO arbitrary delay *)
             (*let (_: _ * _ * _) = (Unix.select [] [] [] 0.1) in*) ()

         done
       with Exit -> ending ()

end
