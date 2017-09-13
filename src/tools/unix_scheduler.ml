(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

module Unix_scheduler = struct

    (* TODO temporary. This scheduler should be split *)
    let blocking = false

    let multiplier = 3

    (* the private list of functions to call on idle, sorted higher
       priority first. *)
    let idle_handler : (int * (unit -> bool)) list ref = ref []

    (* [insert_idle_handler p f] inserts [f] as a new function to call
       on idle, with priority [p] *)
    let insert_idle_handler p f =
      let rec aux l =
        match l with
          | [] -> [p,f]
          | (p1,_) as hd :: rem ->
             if p > p1 then (p,f) :: l else hd :: aux rem
      in
      idle_handler := aux !idle_handler

    (* the private list of functions to call on timeout, sorted on
       earliest trigger time first. *)
    let timeout_handler : (float * float * (unit -> bool)) list ref = ref []

    (* [insert_timeout_handler ms t f] inserts [f] as a new function to call
       on timeout, with time step of [ms] and first call time as [t] *)
    let insert_timeout_handler ms t f =
      let rec aux l =
        match l with
          | [] -> [ms,t,f]
          | (_,t1,_) as hd :: rem ->
             if t < t1 then (ms,t,f) :: l else hd :: aux rem
      in
      timeout_handler := aux !timeout_handler

    (* public function to register a task to run on idle *)
    let idle ~(prio:int) f = insert_idle_handler prio f

    (* public function to register a task to run on timeout *)
    let timeout ~ms f =
      assert (ms > 0);
      let ms = float ms /. 1000.0 in
      let time = Unix.gettimeofday () in
      insert_timeout_handler ms (time +. ms) f

     (* buffer for storing character read on stdin *)
     let buf = Bytes.create 256

     let prompt_delay = ref 0
     let print_prompt = ref true
     let prompt_string = ref "> "

     (* [main_loop interp] starts the scheduler. On idle, standard input is
        read.  When a complete line is read from stdin, it is passed
        as a string to the function [interp] *)
     let main_loop ?prompt interp =
       begin match prompt with
       | None -> ()
       | Some s -> prompt_string := s
       end;
       try
         while true do
           if !print_prompt then begin
             prompt_delay := !prompt_delay + 1;
             if !prompt_string <> "" && !prompt_delay = 1 then begin
               Format.printf "%s@?" !prompt_string;
               prompt_delay := 0;
               print_prompt := false;
             end
           end;
           (* attempt to run the first timeout handler *)
           (let time = Unix.gettimeofday () in
           match !timeout_handler with
           | (ms,t,f) :: rem when t <= time ->
              timeout_handler := rem;
              let b = f () in
              let time = Unix.gettimeofday () in
              if b then insert_timeout_handler ms (ms +. time) f
           | _ ->
              (* time is not yet passed *)
              (* attempt to run the first idle handler *)
              match !idle_handler with
              | (p,f) :: rem ->
                 idle_handler := rem;
                 let b = f () in
                 if b then insert_idle_handler p f
              | [] ->
                 (* no idle handler *)
                 (* check stdin for a some delay *)
                 let delay =
                   match !timeout_handler with
                   | [] -> 0.125
                   (* 1/8 second by default *)
                   | (_,t,_) :: _ -> t -. time
                   (* or the time left until the next timeout otherwise *)
                 in
                 let a,_,_ = Unix.select
                               (if !prompt_string <> "" then [Unix.stdin] else []) [] [] delay in
                 match a with
                 | [_] ->
                    let n = Unix.read Unix.stdin buf 0 256 in
                    interp (Bytes.sub_string buf 0 (n-1));
                    print_prompt := true
                 | [] -> () (* nothing read *)
                 | _ -> assert false);
         done
       with Exit -> ()

end
