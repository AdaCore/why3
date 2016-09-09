

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

     let show_prompt = ref true
     let prompt = ref "> "

     (* [main_loop interp] starts the scheduler. On idle, standard input is
        read.  When a complete line is read from stdin, it is passed
        as a string to the function [interp] *)
     let main_loop interp =
       try
         while true do
           if !show_prompt then begin
               Format.printf "%s@?" !prompt;
               show_prompt := false;
             end;
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
                 | [_] ->
                    let n = Unix.read Unix.stdin buf 0 256 in
                    interp (Bytes.sub_string buf 0 (n-1));
                    show_prompt := true
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

let ses =
  if Queue.is_empty files then Why3.Whyconf.Args.exit_with_usage spec usage_str;
  let fname = Queue.pop files in
  ref (Why3.Session_itp.load_session fname)

let cont = Controller_itp.{
    controller_session = !ses;
    controller_provers = Whyconf.Hprover.create 7;
}

(* loading the drivers *)
let () =
  Whyconf.Mprover.iter
    (fun _ p ->
      try
        let d = Driver.load_driver env p.Whyconf.driver [] in
        Whyconf.Hprover.add cont.Controller_itp.controller_provers p.Whyconf.prover (p,d)
      with e ->
        let p = p.Whyconf.prover in
        eprintf "Failed to load driver for %s %s: %a@."
          p.Whyconf.prover_name p.Whyconf.prover_version
          Exn_printer.exn_printer e)
    provers

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


module C = Why3.Controller_itp.Make(Unix_scheduler)

let test_idle fmt _args =
  Unix_scheduler.idle
    ~prio:0
    (fun () -> fprintf fmt "idle@."; false)

let test_timeout fmt _args =
  Unix_scheduler.timeout
    ~ms:1000
    (let c = ref 10 in
     fun () -> decr c;
               if !c > 0 then
                 (fprintf fmt "%d@." !c; true)
               else
                 (fprintf fmt "boom!@."; false))

let list_provers _fmt _args =
  let l =
    Whyconf.Hprover.fold
      (fun p _ acc -> (Pp.sprintf "%a" Whyconf.print_prover p)::acc)
      cont.Controller_itp.controller_provers
      []
  in
  let l = List.sort String.compare l in
  printf "@[<hov 2>== Known provers ==@\n%a@]@."
          (Pp.print_list Pp.newline Pp.string) l

let sort_pair (x,_) (y,_) = String.compare x y

let list_transforms _fmt _args =
  let l =
    List.rev_append (Trans.list_transforms ()) (Trans.list_transforms_l ())
  in
  let print_trans_desc fmt (x,r) =
    fprintf fmt "@[<hov 2>%s@\n@[<hov>%a@]@]" x Pp.formatted r in
  printf "@[<hov 2>== Known transformations ==@\n%a@]@\n@."
         (Pp.print_list Pp.newline2 print_trans_desc)
         (List.sort sort_pair l)

let dump_session_raw fmt _args =
  fprintf fmt "%a@." Session_itp.print_session !ses

let test_schedule_proof_attempt fmt _args =
  (* temporary : get the first goal *)
  let id =
    match Session_itp.get_theories !ses with
    | (_n, (_thn, x::_)::_)::_ -> x
    | _ -> assert false
  in
  let callback status =
    fprintf fmt "status: %a@."
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

let commands =
  [
    "list-provers", "list available provers", list_provers;
    "list-transforms", "list available transformations", list_transforms;
    (* temporary *)
    "i", "run a simple test of Unix_scheduler.idle", test_idle;
    "a", "run a simple test of Unix_scheduler.timeout", test_timeout;
    "p", "print the session in raw form", dump_session_raw;
    "t", "test schedule_proof_attempt on the first goal", test_schedule_proof_attempt;
(*
  printf "ls : list current directory@\n";
 *)
  ]

let commands_table = Stdlib.Hstr.create 17
let () =
  List.iter
    (fun (c,_,f) -> Stdlib.Hstr.add commands_table c f)
    commands

let help () =
  printf "== Available commands ==@\n";
  let l = ("q", "exit the shell") ::
            List.rev_map (fun (c,h,_) -> (c,h)) commands
  in
  let l = List.sort sort_pair l in
  List.iter (fun (c,help) -> printf "%20s : %s@\n" c help) l;
  printf "@."


let interp chout fmt s =
  let cmd,args =
    match Strings.split ' ' s with
    | [] -> assert false
    | a::b -> a,b
  in
  match cmd with
    | "?" -> help ()
    | "q" ->
       fprintf fmt "Shell exited@.";
       close_out chout;
       exit 0
    | _ ->
       try
         let f = Stdlib.Hstr.find commands_table cmd in
         f fmt args
       with Not_found ->
         printf "unknown command `%s`@." s

(*
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
    | "ls" ->
       let t = Session_itp.get_theories !ses in
       List.iter
         (fun (s,l) ->
          fprintf fmt "File: %s@\n" (Filename.basename s);
          List.iter
            (fun (th,_) ->
             fprintf fmt "  Theory: %s@\n" th)
            l)
         t;
       fprintf fmt "@?"
 *)

let () =
  printf "Welcome to Why3 shell. Type '?' for help.@.";
  let chout = open_out "why3shell.out" in
  let fmt = formatter_of_out_channel chout in
  Unix_scheduler.main_loop (interp chout fmt)
