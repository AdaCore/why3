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

  let push_request r =
    requests := r :: !requests

  (* A disavantage is that we only treat one request at a time *)
  let get_requests () =
    let l = !requests in
    requests := [];
    List.rev l

  let has_notification () : bool =
    not (Queue.is_empty notification_queue)

  let notify n =
    Queue.add n notification_queue

  (* Communicate n notifications *)
  let communicate_notification () =
      let n = Queue.pop notification_queue in
(* TODO think of a better way of separating stuff than > *)
      Format.printf "%a>>>>@." print_notification n

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

let read_from_client fd =
  let buf = Bytes.make 4096 ' ' in
  fun blocking ->
      let do_read =
        blocking ||
        (let l,_,_ = Unix.select [fd] [] [] 0.0 in l <> [])
      in
      if do_read then
        let read = Unix.read fd buf 0 1024 in
        Bytes.sub_string buf 0 read
      else ""

let read_lines fd =
  let filter l =
    List.filter (fun y -> String.length y > 0) l
  in
  let recv_buf : Buffer.t = Buffer.create 65536 in
  let read_from_client = read_from_client fd in
  let rec aux blocking =
    let s = read_from_client blocking in
    (* TODO: should we detect and handle EOF here? *)
    if s = "" then [] else
    if String.contains s '\n' then begin
      let s = Buffer.contents recv_buf ^ s in
      Buffer.clear recv_buf;
      let l = Strings.rev_split '\n' s in
      match l with
      | [] -> assert false
      | [x] when x = "" -> []
      | [x] -> [x]
      | x::xs ->
        if x = "" then List.rev (filter xs) else
(* ??? This case cannot happen  if x.[String.length x - 1] = '\n'
then List.rev (filter l) *)
        begin
          Buffer.add_string recv_buf x;
          List.rev (filter xs)
        end
    end else begin
      Buffer.add_string recv_buf s;
      aux blocking
    end
  in aux

let main_loop () =

  let read_lines = read_lines Unix.stdin in
  (* attempt to run the first timeout handler *)
  while true do
    try
      let time = Unix.gettimeofday () in
      let delay =
        match !timeout_handler, !idle_handler with
        | _, [_] -> 0.0
        | [], _ -> 1.0
        | (_, t, _) :: _ , _ -> min (time -. t) 0.0
      in
      let output =
        if Gnat_Protocol.has_notification () then [Unix.stdout] else [] in
      let l1, l2, _ = Unix.select [Unix.stdin] output [] delay in
      if l1 <> [] then
          List.iter Gnat_Protocol.push_one_request_string (read_lines true);
      if l2 <> [] then
          while Gnat_Protocol.has_notification () do
            Gnat_Protocol.communicate_notification ()
          done;
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
    with e ->
      Format.printf "{ Failure: \"%a\"}>>>>@." Exn_printer.exn_printer e;
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
  Gnat_Scheduler.main_loop ()
