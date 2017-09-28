open Why3
open Format
open Json_util

let debug = false

module Gnat_Protocol = struct

  let notification_queue = Queue.create ()
  let requests = ref []

  let push_one_request_string (s: string) =
    let r = parse_request s in
    requests := r :: !requests

  (* In a string, there can be several requests separated by ">>>>". *)
  let push_request_string (s: string) =
    let list_request = Str.split (Str.regexp ">>>>") s in
    List.iter push_one_request_string list_request

  let push_request r =
    requests := r :: !requests

  (* A disavantage is that we only treat one request at a time *)
  let get_requests () =
    let l = !requests in
    requests := [];
    List.rev l

  let length_notif () : int =
    Queue.length notification_queue

  let notify n =
    Queue.add n notification_queue

  (* Communicate n notifications *)
  let communicate_notification () =
    try
      let n = Queue.pop notification_queue in
(* TODO think of a better way of separating stuff than > *)
      Format.printf "%a>>>>@." print_notification n
    with
    _ -> ()

end

module Gnat_Scheduler = struct

let blocking = false

(* Same arbitrary value as in Why3 *)
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

(* buffer for storing character read on stdin.
   4096 is arbitrary (cf spark plugin) *)
let buf = Bytes.create 4096

let main_loop treat_requests length_notif communicate_notification =

  let delay_comm = ref 0 in
  (* attempt to run the first timeout handler *)
  while true do
    delay_comm := !delay_comm + 1;
    try (
      (* We want to avoid too many communications. We use delay_comm to avoid
         selecting on stdin/stdout too often. TODO there must be a better way
         for this. 10 is arbitrary *)
      (* Communications *)
      if !delay_comm = 10 then
        begin
          delay_comm := 0;
          (* TODO why 0.1 ? *)
          let (todo, _, _) = Unix.select [Unix.stdin] [] [] 0.1 in
          if todo != [] then
            let n = try Unix.read Unix.stdin buf 0 4096 with _ -> 0 in
            if n < 1 then
              ()
            else
              let s = Bytes.sub_string buf 0 (n-1) in
              (* TODO: Note that, here, we probably assume that stdin is of size
                 less than 4096. If requests are sent really fast (or ITP server
                 is busy doing something else), this could not be true. So, we
                 should change this on the long term. Easy to end up with
                 partial requests which we do not want here. *)
              treat_requests s
          else
            ();
          (* Here we only query stdout if we have something to write *)
          if length_notif () > 0 then
            (* TODO why 0.1 ? *)
            let (_, tonotify, _) = Unix.select [] [Unix.stdout] [] 0.1 in
            if tonotify != [] then
              for _i = 0 to length_notif() do
                try communicate_notification () with _ -> ()
              done
            else
              ()
          else
            ()
        end;
      let time = Unix.gettimeofday () in
      match !timeout_handler with
      | (ms,t,f) :: rem when t <= time ->
          timeout_handler := rem;
          let b = f () in
          let time = Unix.gettimeofday () in
          if b then insert_timeout_handler ms (ms +. time) f
      | _ ->
          (* no idle handler *)
          begin
            (* attempt to run the first idle handler *)
            match !idle_handler with
            | (p,f) :: rem ->
                idle_handler := rem;
                let b = f () in
                if b then insert_idle_handler p f
            | [] -> ()
          end
     ) with e ->  Format.printf "FAIL TODO %a>>>>@." Exn_printer.exn_printer e;
       if debug then
         raise e
  done
end

module Server = Itp_server.Make (Gnat_Scheduler) (Gnat_Protocol)

(************************)
(* parsing command line *)
(************************)

let files : string Queue.t = Queue.create ()
let opt_parser = ref None

let spec = Arg.align [
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
(*
  "-f",
   Arg.String (fun s -> input_files := s :: !input_files),
   "<file> add file to the project (ignored if it is already there)";
*)
  Termcode.arg_extra_expl_prefix
]

let usage_str = sprintf
  "Usage: %s [options] [<file.why>|<project directory>]..."
  (Filename.basename Sys.argv.(0))

let env, gconfig =
  Gnat_config.env, Gnat_config.config

(* Initialization of config, provers, task_driver and controller in the server *)
let () =
  let session_dir = Gnat_objectives.get_session_dir () in
  Queue.add session_dir files;
 (* Queue.add Gnat_config.filename files*);
  let session_dir = Server_utils.get_session_dir ~allow_mkdir:true files in
(*
    try
      Server_utils.get_session_dir ~allow_mkdir:true files
    with Invalid_argument s ->
      Format.eprintf "Error: %s@." s;
      Whyconf.Args.exit_with_usage spec usage_str
  in
*)
  (match Gnat_config.limit_line with

  | Some (Gnat_config.Limit_Check check) ->
      let f task : bool =
        let fml = Task.task_goal_fmla task in
        let expl = Gnat_expl.search_labels fml in
        match expl with
        | None -> false
        | Some expl ->
        (check.Gnat_expl.reason = Gnat_expl.get_reason expl)
        && (Gnat_loc.equal_orig_loc check.Gnat_expl.sloc (Gnat_expl.get_loc expl))
      in
      Server.focus_on_loading f
  (* TODO None and _ cases should be exit with errors *)
  | None -> ()
  | _ -> ()
  );
  Server.init_server ~send_source:false gconfig env session_dir


(***********************)
(* start the server    *)
(***********************)

let () =
  Gnat_Scheduler.main_loop Gnat_Protocol.push_request_string Gnat_Protocol.length_notif Gnat_Protocol.communicate_notification
