


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
    | Uninstalled of Whyconf.prover (** prover is uninstalled *)

let print_status fmt st =
  match st with
  | Unedited -> fprintf fmt "Unedited"
  | JustEdited -> fprintf fmt "JustEdited"
  | Interrupted -> fprintf fmt "Interrupted"
  | Scheduled -> fprintf fmt "Scheduled"
  | Running -> fprintf fmt "Running"
  | Done r -> fprintf fmt "Done(%a)" Call_provers.print_prover_result r
  | InternalFailure e -> fprintf fmt "InternalFailure(%a)" Exn_printer.exn_printer e
  | Uninstalled pr -> fprintf fmt "Prover %a is uninstalled" Whyconf.print_prover pr

type transformation_status =
  | TSscheduled | TSdone of transID | TSfailed

let print_trans_status fmt st =
  match st with
  | TSscheduled -> fprintf fmt "TScheduled"
  | TSdone _tid -> fprintf fmt "TSdone" (* TODO print tid *)
  | TSfailed -> fprintf fmt "TSfailed"

type strategy_status = STSgoto of proofNodeID * int | STShalt

let print_strategy_status fmt st =
  match st with
  | STSgoto(id,n) -> fprintf fmt "goto step %d in proofNode %a" n print_proofNodeID id
  | STShalt -> fprintf fmt "halt"


open Ident

type proof_state = {
    th_state: bool Hid.t;
    tn_state: bool Htn.t;
    pn_state : bool Hpn.t;
  }

let init_proof_state _ses =
  {th_state = Hid.create 7;
   tn_state = Htn.create 42;
   pn_state = Hpn.create 42}

type controller =
  { mutable controller_session : Session_itp.session;
    proof_state : proof_state;
    controller_env : Env.env;
    controller_provers : (Whyconf.config_prover * Driver.driver) Whyconf.Hprover.t;
  }

let create_controller env s = {
    controller_session = s;
    proof_state = init_proof_state s;
    controller_env = env;
    controller_provers = Whyconf.Hprover.create 7;
}

let tn_proved c tid = Htn.find_def c.proof_state.tn_state false tid
let pn_proved c pid = Hpn.find_def c.proof_state.pn_state false pid
let th_proved c th  =
  if (theory_goals th = []) then
    Hid.find_def c.proof_state.th_state true (theory_name th)
  else
    Hid.find_def c.proof_state.th_state false (theory_name th)

(* Update the result of the theory according to its children *)
let update_theory th ps =
  let goals = theory_goals th in
  Hid.replace ps.th_state (theory_name th)
    (List.for_all (fun id -> Hpn.find_def ps.pn_state false id) goals)

let rec propagate_proof c (id: Session_itp.proofNodeID) =
  let tr_list = get_transformations c.controller_session id in
  let new_state = List.exists (fun id -> tn_proved c id) tr_list in
  if new_state != pn_proved c id then
    begin
      Hpn.replace c.proof_state.pn_state id new_state;
      update_proof c id
    end

and propagate_trans c (tid: Session_itp.transID) =
  let proof_list = get_sub_tasks c.controller_session tid in
  let cur_state = tn_proved c tid in
  let new_state = List.for_all (fun id -> pn_proved c id) proof_list in
  if cur_state != new_state then
    begin
      Htn.replace c.proof_state.tn_state tid new_state;
      propagate_proof c (get_trans_parent c.controller_session tid)
    end

and update_proof c id =
  match get_proof_parent c.controller_session id with
  | Theory th -> update_theory th c.proof_state
  | Trans tid -> propagate_trans c tid

(* [update_proof_node c id b] Update the whole proof_state
   of c according to the result (id, b) *)
let update_proof_node c id b =
  Hpn.replace c.proof_state.pn_state id b;
  update_proof c id

(* [update_trans_node c id b] Update the proof_state of c to take the result of (id,b). Then
   propagates it to its parents *)
let update_trans_node c id b =
  Htn.replace c.proof_state.tn_state id b;
  propagate_proof c (get_trans_parent c.controller_session id)



(* printing *)

module PSession = struct

  open Stdlib

  type any =
    | Session
    | File of file
    | Theory of theory
    | Goal of proofNodeID
    | Transf of transID
    | ProofAttempt of proof_attempt

  type 'a t = { tcont : controller;
                tkind : any }

  let decomp x =
    let s = x.tcont.controller_session in
    let n y acc = { x with tkind = y } :: acc in
    match x.tkind with
    | Session -> "", Hstr.fold (fun _ f -> n (File f)) (get_files s) []
    | File f ->
       f.file_name,
       List.fold_right (fun th -> n (Theory th)) f.file_detached_theories
                       (List.fold_right (fun th -> n (Theory th)) f.file_theories [])
    | Theory th ->
       let id = theory_name th in
       let name = id.Ident.id_string in
       let name = if th_proved x.tcont th then name^"!" else name^"?" in
       name,
       List.fold_right (fun g -> n (Goal g)) (theory_goals th)
                       (List.fold_right (fun g -> n (Goal g)) (theory_detached_goals th) [])
    | Goal id ->
       let gid = get_proof_name s id in
       let name = gid.Ident.id_string in
       let name = if pn_proved x.tcont id then name^"!" else name^"?" in
       let pas = get_proof_attempts s id in
       let trs = get_transformations s id in
       name,
       List.fold_right (fun g -> n (Transf g)) trs
                       (List.fold_right (fun g -> n (ProofAttempt g)) pas [])
    | ProofAttempt pa ->
       Pp.sprintf_wnl "%a%s%s"
                      Whyconf.print_prover pa.prover
                      (match pa.Session_itp.proof_state with
                       | Some { Call_provers.pr_answer = Call_provers.Valid} -> ""
                       | _ -> "?")
                      (if pa.proof_obsolete then "O" else ""), []
    | Transf id ->
       let name = get_transf_name s id in
       let name = if tn_proved x.tcont id then name^"!" else name^"?" in
       let sts = get_sub_tasks s id in
       let dsts = get_detached_sub_tasks s id in
       name,
       List.fold_right (fun g -> n (Goal g)) sts
                       (List.fold_right (fun g -> n (Goal g)) dsts [])

end

module P = Print_tree.PMake(PSession)

let print_session fmt c =
  P.print fmt { PSession.tcont = c; PSession.tkind = PSession.Session }








(*********)



module type Scheduler = sig
  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: prio:int -> (unit -> bool) -> unit
end

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


(** reload files, associating old proof attempts and transformations
    to the new goals.  old theories and old goals for which we cannot
    find a corresponding new theory resp. old goal are kept, with
    tasks associated to them *)

let merge_file (old_ses : session) (c : controller) env ~use_shapes _ file =
  let format = file.file_format in
  let old_theories = file.file_theories in
  let file_name = Filename.concat (get_dir old_ses) file.file_name in
  let new_theories =
    try
      read_file c.controller_env file_name ?format
    with _ -> (* TODO: filter only syntax error and typing errors *)
      []
  in
  add_file_section
    c.controller_session ~use_shapes ~merge:(old_ses,old_theories,env) file_name new_theories format


let reload_files (c : controller) (env : Env.env) ~use_shapes =
  let old_ses = c.controller_session in
  c.controller_session <- empty_session ~shape_version:(get_shape_version old_ses) (get_dir old_ses);
  Stdlib.Hstr.iter (merge_file old_ses c env ~use_shapes) (get_files old_ses)

let add_file c ?format fname =
  let theories = read_file c.controller_env ?format fname in
  add_file_section ~use_shapes:false c.controller_session fname theories format

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
    Driver.prove_task ?old:None ~cntexample:true ~inplace:false ~command
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
    | Call_provers.ProverInterrupted ->
       if started then decr number_of_running_provers;
       (* inform the callback *)
       callback (Interrupted)
    | Call_provers.InternalFailure exn ->
       if started then decr number_of_running_provers;
       (* inform the callback *)
       callback (InternalFailure (exn))
  done;
  Queue.transfer q prover_tasks_in_progress;
  (* if the number of prover tasks is less than 3 times the maximum
     number of running provers, then we heuristically decide to add
     more tasks *)
  try
    for _i = Queue.length prover_tasks_in_progress
        to 3 * !max_number_of_running_provers do
      let (c,id,pr,limit,callback) = Queue.pop scheduled_proof_attempts in
      try
        build_prover_call c id pr limit callback
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

let schedule_proof_attempt_r c id pr ~limit ~callback =
  let panid =
    graft_proof_attempt c.controller_session id pr ~timelimit:limit.Call_provers.limit_time
  in
  Queue.add (c,id,pr,limit,callback panid) scheduled_proof_attempts;
  callback panid Scheduled;
  run_timeout_handler ()

let schedule_proof_attempt c id pr ~limit ~callback =
  let callback panid s = (match s with
  | Done pr -> update_proof_node c id (pr.Call_provers.pr_answer == Call_provers.Valid)
  | Interrupted | InternalFailure _ -> update_proof_node c id false
  | _ -> ());
  callback panid s
  in
  schedule_proof_attempt_r c id pr ~limit:limit ~callback

let schedule_transformation_r c id name args ~callback =
  let apply_trans () =
    let task = get_task c.controller_session id in
    begin
      try
        let subtasks = Trans.apply_transform_args name c.controller_env args task in
        (* if result is same as input task, consider it as a failure *)
        begin
          match subtasks with
          | [t'] when Task.task_equal t' task ->
             callback TSfailed
          | _ ->
             let tid = graft_transf c.controller_session id name args subtasks in
             callback (TSdone tid)
        end
      with e when not (Debug.test_flag Debug.stack_trace) ->
        Format.eprintf
          "@[Exception raised in Trans.apply_transform %s:@ %a@.@]"
          name Exn_printer.exn_printer e;
        callback TSfailed
    end;
    false
  in
  S.idle ~prio:0 apply_trans;
  callback TSscheduled

let schedule_transformation c id name args ~callback =
  let callback s = (match s with
  | TSdone tid -> update_trans_node c tid false
  (*(get_sub_tasks c.controller_session tid = [])*)
  (* TODO need to change schedule transformation to get the id ? *)
  | TSfailed -> ()
  | _ -> ()); callback s in
  schedule_transformation_r c id name args ~callback

open Strategy

let run_strategy_on_goal c id strat ~callback_pa ~callback_tr ~callback =
  let rec exec_strategy pc strat g =
    if pc < 0 || pc >= Array.length strat then
      callback STShalt
    else
      match Array.get strat pc with
      | Icall_prover(p,timelimit,memlimit) ->
         let callback panid res =
           callback_pa panid res;
           match res with
           | Scheduled | Running -> (* nothing to do yet *) ()
           | Done { Call_provers.pr_answer = Call_provers.Valid } ->
              (* proof succeeded, nothing more to do *)
              callback STShalt
           | Interrupted | InternalFailure _
           | Done _ ->
              (* proof did not succeed, goto to next step *)
              callback (STSgoto (g,pc+1));
              let run_next () = exec_strategy (pc+1) strat g; false in
              S.idle ~prio:0 run_next
           | Unedited | JustEdited | Uninstalled _ ->
                         (* should not happen *)
                         assert false
         in
         let limit = { Call_provers.empty_limit with
                       Call_provers.limit_time = timelimit;
                       limit_mem  = memlimit} in
         schedule_proof_attempt c g p ~limit ~callback
      | Itransform(trname,pcsuccess) ->
         let callback ntr =
           callback_tr ntr;
           match ntr with
           | TSfailed -> (* transformation failed *)
              callback (STSgoto (g,pc+1));
              let run_next () = exec_strategy (pc+1) strat g; false in
              S.idle ~prio:0 run_next
           | TSscheduled -> ()
           | TSdone tid ->
              List.iter
                (fun g ->
                 callback (STSgoto (g,pcsuccess));
                 let run_next () =
                   exec_strategy pcsuccess strat g; false
                 in
                 S.idle ~prio:0 run_next)
                (get_sub_tasks c.controller_session tid)
         in
         schedule_transformation c g trname [] ~callback
      | Igoto pc ->
         callback (STSgoto (g,pc));
         exec_strategy pc strat g
  in
  exec_strategy 0 strat id

let replay_proof_attempt c pr limit (id: proofNodeID) ~callback =

  (* The replay can be done on a different machine so we need
     to check more things before giving the attempt to the scheduler *)
  if not (Hprover.mem c.controller_provers pr) then
    callback (Uninstalled pr)
  else
    (Queue.add (c, id, pr, limit, callback) scheduled_proof_attempts;
     callback Scheduled;
     run_timeout_handler ())

type report =
  | Result of Call_provers.prover_result * Call_provers.prover_result
  (** Result(new_result,old_result) *)
  | CallFailed of exn
  | Prover_not_installed
  | Edited_file_absent of string
  | No_former_result of Call_provers.prover_result

(* TODO find a better way to print it *)
let print_report fmt (r: report) =
  match r with
  | Result (new_r, old_r) ->
    Format.fprintf fmt "new_result = %a, old_result = %a@."
      Call_provers.print_prover_result new_r
      Call_provers.print_prover_result old_r
  | CallFailed _ ->
    Format.fprintf fmt "Callfailed@."
  | Prover_not_installed ->
    Format.fprintf fmt "Prover not installed@."
  | Edited_file_absent _ ->
    Format.fprintf fmt "No edited file@."
  | No_former_result new_r ->
    Format.fprintf fmt "new_result = %a, no former result@."
      Call_provers.print_prover_result new_r

(* TODO to be removed when we have a better way to print *)
let replay_print (lr: (proofNodeID * Whyconf.prover * Call_provers.resource_limit * report) list) =
  let pp_elem fmt (id, pr, rl, report) =
    fprintf fmt "ProofNodeID: %d, Prover: %a, Timelimit?: %d, Result: %a@."
      (Obj.magic id) Whyconf.print_prover pr rl.Call_provers.limit_time print_report report
  in
  Format.printf "%a@." (Pp.print_list Pp.newline pp_elem) lr

let replay ~remove_obsolete ~use_steps c ~callback =

  (* === Side functions used by replay === *)
  let counting s count =
    match s with
    | Interrupted -> count := !count - 1
    | Done _ -> count := !count - 1
    | InternalFailure _ -> count := !count - 1
    | Uninstalled _ -> count := !count - 1
    | _ -> () in

  let craft_report s r id pr limits pa =
    match s with
    | Interrupted -> assert false
(* Never happen r := (id, pr, limits, CallFailed (User_interrupt)) :: !r *)
    | Done new_r ->
        (match pa.Session_itp.proof_state with
        | None -> (r := (id, pr, limits, No_former_result new_r) :: !r)
        | Some old_r -> r := (id, pr, limits, Result (new_r, old_r)) :: !r)
    | InternalFailure e ->
        r := (id, pr, limits, CallFailed (e)) :: !r
    | Uninstalled _ -> r := (id, pr, limits, Prover_not_installed) :: !r;
    | _ -> () in

  let update_node pa s =
    match s with
    | Done new_r ->
        (pa.Session_itp.proof_state <- Some new_r;
         pa.proof_obsolete <- false)
    | InternalFailure _ ->
        pa.proof_obsolete <- true
    | Uninstalled _ ->
        pa.proof_obsolete <- true
    | _ -> () in

  let update_uninstalled c remove_obsolete id s pr =
    match s with
    | Uninstalled _ ->
        if remove_obsolete then
          remove_proof_attempt c.controller_session id pr
        else
          ()
    | _ -> () in

  (* === replay === *)
  let session = c.controller_session in
  let count = ref 0 in
  let report = ref [] in

  (* TODO count the number of node in a more efficient way *)
  (* Counting the number of proof_attempt to print report only once *)
  Session_itp.session_iter_proof_attempt
    (fun _ _ -> count := !count + 1) session;

  (* Replaying function *)
  let replay_pa id pa =
    let pr = pa.prover in
    (* If use_steps, we give only steps as a limit *)
    let limit =
      if use_steps then
        Call_provers.{empty_limit with limit_steps = pa.limit.limit_steps}
      else
        pa.limit
    in
    replay_proof_attempt c pr limit id
      ~callback:(fun s ->
        counting s count; craft_report s report id pr limit pa; update_node pa s;
        update_uninstalled c remove_obsolete id s pr;
        if !count = 0 then callback !report) in

  (* Calling replay on all the proof_attempts of the session *)
  Session_itp.session_iter_proof_attempt
    (fun id pa -> replay_pa id pa) session

end
