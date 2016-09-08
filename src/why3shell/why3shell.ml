

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

open Why3
open Format

let files = Queue.create ()

let spec = Arg.align [
]

let usage_str = Format.sprintf
  "Usage: %s [options] <project directory>"
  (Filename.basename Sys.argv.(0))


let config, base_config, _env =
  Why3.Whyconf.Args.initialize spec (fun f -> Queue.add f files) usage_str

let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

(* loading the drivers *)
let provers =
  Whyconf.Mprover.fold
    (fun _ p acc ->
      try
        let d = Driver.load_driver env p.Whyconf.driver [] in
        (p,d)::acc
      with e ->
        let p = p.Whyconf.prover in
        eprintf "Failed to load driver for %s %s: %a@."
          p.Whyconf.prover_name p.Whyconf.prover_version
          Exn_printer.exn_printer e;
        acc)
    provers
    []

(* One prover named Alt-Ergo in the config file *)
let alt_ergo =
  let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
  (** all provers that have the name "Alt-Ergo" *)
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else
    snd (Whyconf.Mprover.choose provers)


let ses =
  if Queue.is_empty files then Why3.Whyconf.Args.exit_with_usage spec usage_str;
  let fname = Queue.pop files in
  ref (Why3.Session_itp.load_session fname)

let cont = Controller_itp.{
    controller_session = !ses;
    controller_provers = Whyconf.Hprover.create 7;
  }

module C = Why3.Controller_itp.Make(Unix_scheduler)

exception Error of string

let resolve _ses _path = assert false (* TODO *)

let curdir = ref []


let interp s =
  let cmd,args =
    match Strings.split ' ' s with
    | [] -> assert false
    | a::b -> a,b
  in
  match cmd with
    | "?" ->
       printf "Commands@\n";
       printf "a : run a simple test of Unix_scheduler.timeout@\n";
       printf "i : run a simple test of Unix_scheduler.idle@\n";
       printf "ls : list current directory@\n";
       printf "p : print the session in raw form@\n";
       printf "q : exit the shell@\n";
       printf "t : test schedule_proof_attempt on the first goal@\n";
       printf "@."
    | "t" ->
       let id =
         match Session_itp.get_theories !ses with
         | (_n, (_thn, x::_)::_)::_ -> x
         | _ -> assert false
       in
       let callback status =
         printf "status: %a@."
                Controller_itp.print_status status
       in
       let limit = Call_provers.{
           limit_time = 5 ;
           limit_mem  = 1000;
           limit_steps = -1;
         }
       in
       C.schedule_proof_attempt
         cont id alt_ergo.Whyconf.prover
         ~limit ~callback
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
       printf "%a@." Session_itp.print_session !ses
    | "cd" ->
       begin
         match args with
         | [d] ->
            begin
              try
                let path = Strings.split '/' d in
                let path =
                  if String.get d 0 = '/' then path
                  else !curdir @ path
                in
                let dir = resolve !ses path in
                curdir := dir
              with Error s ->
                printf "command cd failed: %s@." s
            end
         | _ -> printf "command cd expects exactly one argument@."
       end
    | "pwd" -> printf "/%a@." (Pp.print_list Pp.slash Pp.string) !curdir
    | "q" -> exit 0
    | "ls" ->
       let t = Session_itp.get_theories !ses in
       List.iter
         (fun (s,l) ->
          printf "File: %s@\n" (Filename.basename s);
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
