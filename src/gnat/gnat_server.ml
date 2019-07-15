open Why3
open Json_util

(* Initialization: Add all libexec executables to PATH (to be able to launch
   cvc4, z3, altergo etc) *)
let () =
  let path_separator =
    match Sys.os_type with
    | "Unix" | "Cygwin" -> ":"
    | "Win32" -> ";"
    | _ -> assert false in
  (* ??? This does not always return the absolute location of gnat_server but
     this use case should be ok (see documentation of Ocaml
     Sys.executable_name). *)
  let gnat_server_path = Filename.dirname (Sys.executable_name) in
  let cur_env = Unix.getenv "PATH" in
  let new_env = cur_env ^ path_separator ^ gnat_server_path in
  Unix.putenv "PATH" new_env

let debug_server = Debug.register_flag ~desc:"Debug gnat_server" "gnat_server"
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

let debug_to_file s =
  if Debug.test_flag debug_server then
    begin
      let oc = open_out_gen [Open_append] 0 "/tmp/gnat_server.log" in
      Printf.fprintf oc "%s" s;
      close_out oc
    end

let main_loop () =

  let read_lines = read_lines Unix.stdin in
  (* attempt to run the first timeout handler *)
  while true do
    try
      debug_to_file "[gnat_server loop]\n";
      let time = Unix.gettimeofday () in
      let timeout =
        match !timeout_handler, !idle_handler with
        (* When a transformation has been triggered by the user, we don't want
           to wait during Unix.select because we already want to execute the
           transformation. *)
        | _, _ :: _ -> 0.0
        (* The value 1.0 is a random choice which does not respond to a clear
           specification requirement. *)
        | [], [] -> 1.0
        (* We allow the delay given to select to be at most the time remaining
           before the next timeout function wants to be executed.
        *)
        | (_, t, _) :: _ , _ -> max (t -. time) 0.0
      in
      let output =
        if Gnat_Protocol.has_notification () then [Unix.stdout] else [] in
      debug_to_file ("[Begin selecting with timeout: " ^
                     (string_of_float timeout) ^ "]\n");
      let l1, l2, _ = Unix.select [Unix.stdin] output [] timeout in
      debug_to_file "[End selecting]\n";
      debug_to_file "[Trying to handle request]\n@.";
      if l1 <> [] then
        begin
          let () = debug_to_file "[Trying to read_lines]\n@." in
          let rl = read_lines true in
          let () = debug_to_file "[Successfully read_lines]\n@." in
          List.iter Gnat_Protocol.push_one_request_string rl;
        end;
      debug_to_file "[Trying to handle notifications]\n@.";
      if l2 <> [] then
          while Gnat_Protocol.has_notification () do
            Gnat_Protocol.communicate_notification ()
          done;

      let time = Unix.gettimeofday () in
      debug_to_file "[timeout_handler]\n";
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
            debug_to_file "[idle_handler]\n";
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

let () = Gnat_util.set_debug_flags_gnatprove ()


let files : string Queue.t = Queue.create ()

let opt_session_dir : string option ref = ref None
let opt_proof_dir : string option ref = ref None
let opt_limit_line : Gnat_expl.limit_mode option ref = ref None

let set_limit_line s = opt_limit_line := Some (Gnat_expl.parse_line_spec s)

let debug_gnat_server () = Debug.set_flag debug_server

let set_filename s =
   if !opt_session_dir = None then
      opt_session_dir := Some s
   else
      Gnat_util.abort_with_message ~internal:true
      "Only one file name should be given."

let set_proof_dir s = opt_proof_dir := Some  s

let usage_msg =
  "Usage: gnat_server [options] mlw-file"

let options = Arg.align [
   "--limit-line", Arg.String set_limit_line,
          " Limit proof to a file and line, given \
           by \"file:line[:column:checkkind]\"";
   "--debug-stack-trace",
            Arg.Unit (fun () -> Debug.set_flag Debug.stack_trace;
                                Printexc.record_backtrace true),
          " Enable debug mode; and gives stack_trace on any exception raised";
   "--debug-gnat-server", Arg.Unit debug_gnat_server,
          " Enable debug mode for gnat_server";
   "--proof-dir", Arg.String set_proof_dir,
          " Specify directory to save session and manual proofs files";
   ]

let () = Arg.parse options set_filename usage_msg

let session_dir =
   match !opt_session_dir with
   | None -> Gnat_util.abort_with_message ~internal:true "No file given."
   | Some s -> s

let env, gconfig =
  let config =
   Gnat_util.get_gnatprove_config
     (Whyconf.read_config (Some Gnat_util.gnatprove_why3conf_file)) in
  let env = Gnat_util.build_env_from_config ~load_plugins:true
                                            ~proof_dir:!opt_proof_dir
                                            config in
  env, config

(* Initialization of config, provers, task_driver and controller in the server *)
let () =
  Queue.add session_dir files;
  let session_dir = Server_utils.get_session_dir ~allow_mkdir:true files in
  (match !opt_limit_line with

  | Some (Gnat_expl.Limit_Check check) ->
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
