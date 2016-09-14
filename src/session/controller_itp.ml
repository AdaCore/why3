


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
  | TSscheduled of transID | TSdone of transID | TSfailed

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
          ~with_steps:(limit.Call_provers.limit_steps <>
                       Call_provers.empty_limit.Call_provers.limit_steps) in
  let task = Session_itp.get_task c.controller_session id in
  let call =
    Driver.prove_task ?old:None ~cntexample:false ~inplace:false ~command
                      ~limit driver task
  in
(*
  let c = ref 0 in
  let call () =
    incr c;
    if !c = 10 then Call_provers.ProverStarted else
      if !c = 20 then Call_provers.ProverFinished dummy_result
      else Call_provers.NoUpdates
 *)
(*
  match find_prover eS a with
  | None ->
    callback a a.proof_prover Call_provers.empty_limit None Starting;
    (* nothing to do *)
    callback a a.proof_prover Call_provers.empty_limit None MissingProver
  | Some(ap,npc,a) ->
    callback a ap Call_provers.empty_limit None Starting;
    let itp = npc.prover_config.Whyconf.interactive in
    if itp && a.proof_edited_as = None then begin
      callback a ap Call_provers.empty_limit None (MissingFile "unedited")
    end else begin
      let previous_result = a.proof_state in
      let limit = adapt_limits ~interactive:itp ~use_steps a in
      let inplace = npc.prover_config.Whyconf.in_place in
      let command =
        Whyconf.get_complete_command npc.prover_config
          ~with_steps:(limit.Call_provers.limit_steps <>
                       Call_provers.empty_limit.Call_provers.limit_steps) in
      let cb result =
        let result = fuzzy_proof_time result previous_result in
        callback a ap limit
          (match previous_result with Done res -> Some res | _ -> None)
          (StatusChange result) in
      try
        let old =
          match get_edited_as_abs eS.session a with
          | None -> None
          | Some f ->
            if Sys.file_exists f then Some f
            else raise (NoFile f) in
        schedule_proof_attempt
          ~cntexample ~limit
          ?old ~inplace ~command
          ~driver:npc.prover_driver
          ~callback:cb
          eT
          (goal_task_or_recover eS a.proof_parent)
      with NoFile f ->
        callback a ap Call_provers.empty_limit None (MissingFile f)
    end

        let call =
          Driver.prove_task ?old:None ~cntexample:false ~inplace:false ~command
                            ~limit driver goal
        in
 *)
  let pa = (callback,false,call) in
  Queue.push pa prover_tasks_in_progress

let timeout_handler () =
  (* examine all the prover tasks in progress *)
  let q = Queue.create () in
  while not (Queue.is_empty prover_tasks_in_progress) do
    let (callback,started,call) as c = Queue.pop prover_tasks_in_progress in
    match Call_provers.query_call call with
    | Call_provers.NoUpdates -> Queue.add c q
    | Call_provers.ProverStarted ->
       assert (not started);
       callback Running;
       incr number_of_running_provers;
       Queue.add (callback,true,call) q
    | Call_provers.ProverFinished res ->
       if started then decr number_of_running_provers;
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

let schedule_transformations c id name args ~callback =
  let tid = graft_transf c.controller_session id name args in
  callback (TSscheduled tid)

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
