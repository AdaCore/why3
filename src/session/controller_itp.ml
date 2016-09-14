


open Format
open Session_itp

(** State of a proof *)
type proof_attempt_status =
    | Unedited (** editor not yet run for interactive proof *)
    | JustEdited (** edited but not run yet *)
    | Interrupted (** external proof has never completed *)
    | Scheduled (** external proof attempt is scheduled *)
    | Running (** external proof attempt is in progress *)
    | Done of Call_provers.prover_result (** external proof done *)
    | InternalFailure of exn (** external proof aborted by internal error *)

let print_status fmt st =
  match st with
  | Unedited -> fprintf fmt "Unedited"
  | JustEdited -> fprintf fmt "JustEdited"
  | Interrupted -> fprintf fmt "Interrupted"
  | Scheduled -> fprintf fmt "Scheduled"
  | Running -> fprintf fmt "Running"
  | Done r -> fprintf fmt "Done(%a)" Call_provers.print_prover_result r
  | InternalFailure e -> fprintf fmt "InternalFailure(%a)" Exn_printer.exn_printer e

type transformation_status =
  | TSscheduled | TSdone | TSfailed

let print_trans_status fmt st =
  match st with
  | TSscheduled -> fprintf fmt "TScheduled"
  | TSdone -> fprintf fmt "TSdone"
  | TSfailed -> fprintf fmt "TSfailed"

type controller =
  { mutable controller_session : Session_itp.session;
    controller_env : Env.env;
    controller_provers : (Whyconf.config_prover * Driver.driver) Whyconf.Hprover.t;
  }

let create_controller env s = {
    controller_session = s;
    controller_env = env;
    controller_provers = Whyconf.Hprover.create 7;
}



module type Scheduler = sig
  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: prio:int -> (unit -> bool) -> unit
end


module Make(S : Scheduler) = struct

let scheduled_proof_attempts = Queue.create ()

let prover_tasks_in_progress = Queue.create ()

let timeout_handler_running = ref false

let max_number_of_running_provers = ref 1

let number_of_running_provers = ref 0
module Hprover = Whyconf.Hprover

(*
let dummy_result =
  {
    pr_answer = Call_provers.Unknown ("I'm dumb", None);
    pr_status = Unix.WEXITED 0;
    pr_output = "";
    pr_time   = 3.14;
    pr_steps  = 42;
    pr_model  = Model_parser.default_model;
}
 *)

let build_prover_call c id pr limit callback =
  let (config_pr,driver) = Hprover.find c.controller_provers pr in
  let command =
    Whyconf.get_complete_command config_pr
          ~with_steps:Call_provers.(limit.limit_steps <> empty_limit.limit_steps) in
  let task = Session_itp.get_task c.controller_session id in
  let call =
    Driver.prove_task ?old:None ~cntexample:false ~inplace:false ~command
                      ~limit driver task
  in
  let pa = (c.controller_session,id,pr,callback,false,call) in
  Queue.push pa prover_tasks_in_progress

let timeout_handler () =
  (* examine all the prover tasks in progress *)
  let q = Queue.create () in
  while not (Queue.is_empty prover_tasks_in_progress) do
    let (ses,id,pr,callback,started,call) as c = Queue.pop prover_tasks_in_progress in
    match Call_provers.query_call call with
    | Call_provers.NoUpdates -> Queue.add c q
    | Call_provers.ProverStarted ->
       assert (not started);
       callback Running;
       incr number_of_running_provers;
       Queue.add (ses,id,pr,callback,true,call) q
    | Call_provers.ProverFinished res ->
       if started then decr number_of_running_provers;
       (* update the session *)
       update_proof_attempt ses id pr res;
       (* inform the callback *)
       callback (Done res)
  done;
  Queue.transfer q prover_tasks_in_progress;
  (* if the number of prover tasks is less than 3 times the maximum
     number of running provers, then we heuristically decide to add
     more tasks *)
  try
    for _i = Queue.length prover_tasks_in_progress
        to 3 * !max_number_of_running_provers do
      let (c,id,pr,timelimit,callback) = Queue.pop scheduled_proof_attempts in
      try
        build_prover_call c id pr timelimit callback
      with e when not (Debug.test_flag Debug.stack_trace) ->
        Format.eprintf
          "@[Exception raised in Controller_itp.build_prover_call:@ %a@.@]"
          Exn_printer.exn_printer e;
        callback (InternalFailure e)
    done;
    true
  with Queue.Empty -> true

let run_timeout_handler () =
  if not !timeout_handler_running then
    begin
      timeout_handler_running := true;
      S.timeout ~ms:125 timeout_handler;
    end

let schedule_proof_attempt c id pr ~limit ~callback =
  graft_proof_attempt c.controller_session id pr ~timelimit:5;
  Queue.add (c,id,pr,limit,callback) scheduled_proof_attempts;
  callback Scheduled;
  run_timeout_handler ()

let schedule_transformation c id name args ~callback =
  let apply_trans () =
    let task = get_task c.controller_session id in
    try
      let subtasks = Trans.apply_transform name c.controller_env task in
      let _tid = graft_transf c.controller_session id name args subtasks in
      callback TSdone;
      false
    with e when not (Debug.test_flag Debug.stack_trace) ->
      Format.eprintf
        "@[Exception raised in Trans.apply_transform %s:@ %a@.@]"
          name Exn_printer.exn_printer e;
        callback TSfailed;
        false
  in
  S.idle ~prio:0 apply_trans;
  callback TSscheduled

let read_file env ?format fn =
  let theories = Env.read_file Env.base_language env ?format fn in
  let ltheories =
    Stdlib.Mstr.fold
      (fun name th acc ->
        (* Hack : with WP [name] and [th.Theory.th_name.Ident.id_string] *)
        let th_name =
          Ident.id_register (Ident.id_derive name th.Theory.th_name) in
         match th.Theory.th_name.Ident.id_loc with
           | Some l -> (l,th_name,th)::acc
           | None   -> (Loc.dummy_position,th_name,th)::acc)
      theories []
  in
  let th =  List.sort
      (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
      ltheories
  in
  List.map (fun (_,_,a) -> a) th

let add_file c ?format fname =
  let theories = read_file c.controller_env ?format fname in
  add_file_section c.controller_session fname theories None

(** reload files, associating old proof attempts and transformations
    to the new goals.  old theories and old goals for which we cannot
    find a corresponding new theory resp. old goal are kept, with
    tasks associated to them *)

let merge_file (_old_ses : session) (c : controller) _ file =
  try
    let theories =
      read_file c.controller_env file.file_name ?format:file.file_format
    in
    add_file_section c.controller_session file.file_name theories None;

  with _ -> (* TODO: filter only syntax error and typing errors *)
    (* TODO: copy the old session with empty tasks *)
    add_file_section c.controller_session file.file_name [] None

let reload_files (c : controller)  =
  let old_ses = c.controller_session in
  c.controller_session <- empty_session ();
  Stdlib.Hstr.iter (merge_file old_ses c) (get_files old_ses)

end
