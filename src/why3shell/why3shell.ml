

module Unix_scheduler = struct

    (* the private list of functions to call on idle, sorted higher
       priority first. *)
    let idle_handler = ref []

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

    (* the private list of functions to call on idle, sorted on
       earliest trigger time first. *)
    let timeout_handler = ref []

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

     (* [main_loop interp] starts the scheduler. On idle, standard input is
        read.  When a complete line is read from stdin, it is passed
        as a string to the function [interp] *)
     let main_loop interp =
       try
         while true do
           (* attempt to run the first timeout handler *)
           let time = Unix.gettimeofday () in
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
                 let a,_,_ = Unix.select [Unix.stdin] [] [] delay in
                 match a with
                 | [_] -> let n = Unix.read Unix.stdin buf 0 256 in
                          interp (Bytes.sub_string buf 0 (n-1))
                 | [] -> () (* nothing read *)
                 | _ -> assert false
         done
       with Exit -> ()

end



(************************)
(* parsing command line *)
(************************)

let files = Queue.create ()

let spec = Arg.align [
]

let usage_str = Format.sprintf
  "Usage: %s [options] <project directory>"
  (Filename.basename Sys.argv.(0))

let config, base_config, env =
  Why3.Whyconf.Args.initialize spec (fun f -> Queue.add f files) usage_str

let ses =
  if Queue.is_empty files then Why3.Whyconf.Args.exit_with_usage spec usage_str;
  let fname = Queue.pop files in
  ref (Why3.Session_itp.load_session fname)

module C = Why3.Controller_itp.Make(Unix_scheduler)

open Why3.Session_itp
open Format

let interp s =
  match s with
    | "?" ->
       printf "Commands@\n";
       printf "a : run a simple test of Unix_scheduler.timeout@\n";
       printf "i : run a simple test of Unix_scheduler.idle@\n";
       printf "ls : list current directory@\n";
       printf "p : print the session in raw form@\n";
       printf "q : exit the shell@\n";
       printf "@."
    | "a" ->
       Unix_scheduler.timeout
         ~ms:1000
         (let c = ref 10 in
          fun () -> decr c;
                    if !c > 0 then
                      (printf "%d@." !c; true)
                    else
                      (printf "boom!@."; false))
    | "i" ->
       Unix_scheduler.idle
         ~prio:0
         (fun () -> printf "idle@."; false)
    | "p" ->
       printf "%a@." print_session !ses
    | "q" -> exit 0
    | "ls" ->
       let t = get_theories !ses in
       List.iter
         (fun (s,l) ->
          printf "File: %s@\n" s;
          List.iter
            (fun (th,_) ->
             printf "  Theory: %s@\n" th)
            l)
         t;
       printf "@?"
    | _ -> printf "unknown command `%s`@." s


let () =
  printf "Welcome to Why3 shell. Type '?' for help.@.";
  Unix_scheduler.main_loop interp
