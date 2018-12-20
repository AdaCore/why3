(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Wstdlib
open Session_itp
open Generic_arg_trans_utils
open Args_wrapper

let debug_sched = Debug.register_info_flag "scheduler"
  ~desc:"Print@ debugging@ messages@ about@ scheduling@ of@ prover@ calls@ \
         and@ transformation@ applications."

let debug_call_prover = Debug.lookup_flag "call_prover"
let default_delay_ms = 100 (* 0.1 seconds *)

(** State of a proof *)
type proof_attempt_status =
  | Undone   (** prover was never called *)
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Done of Call_provers.prover_result (** external proof done *)
  | Interrupted (** external proof has never completed *)
  | Detached (** parent goal has no task, is detached *)
  | InternalFailure of exn (** external proof aborted by internal error *)
  | Uninstalled of Whyconf.prover (** prover is uninstalled *)
  | UpgradeProver of Whyconf.prover (** prover is upgraded *)
  | Removed of Whyconf.prover (** prover has been removed or upgraded *)

let print_status fmt st =
  match st with
  | Undone            -> fprintf fmt "Undone"
  | Scheduled         -> fprintf fmt "Scheduled"
  | Running           -> fprintf fmt "Running"
  | Done r            ->
      fprintf fmt "Done(%a)" Call_provers.print_prover_result r
  | Interrupted       -> fprintf fmt "Interrupted"
  | Detached          -> fprintf fmt "Detached"
  | InternalFailure e ->
      fprintf fmt "InternalFailure(%a)" Exn_printer.exn_printer e
  | Uninstalled pr    ->
      fprintf fmt "Prover %a is uninstalled" Whyconf.print_prover pr
  | UpgradeProver pr    ->
      fprintf fmt "Prover upgrade to %a" Whyconf.print_prover pr
  | Removed pr    ->
      fprintf fmt "Prover %a removed" Whyconf.print_prover pr

type transformation_status =
  | TSscheduled | TSdone of transID | TSfailed of (proofNodeID * exn)
  | TSfatal of (proofNodeID * exn)

let print_trans_status fmt st =
  match st with
  | TSscheduled -> fprintf fmt "TScheduled"
  | TSdone _tid -> fprintf fmt "TSdone" (* TODO print tid *)
  | TSfailed _e -> fprintf fmt "TSfailed"
  | TSfatal _e -> fprintf fmt "TSfatal"

type strategy_status = STSgoto of proofNodeID * int | STShalt
                     | STSfatal of string * proofNodeID * exn

let print_strategy_status fmt st =
  match st with
  | STSgoto(id,n) ->
      fprintf fmt "goto step %d in proofNode %a" n print_proofNodeID id
  | STShalt -> fprintf fmt "halt"
  | STSfatal _ -> fprintf fmt "fatal"


type controller =
  { mutable controller_session: Session_itp.session;
    mutable controller_config : Whyconf.config;
    mutable controller_env: Env.env;
    controller_provers:
      (Whyconf.config_prover * Driver.driver) Whyconf.Hprover.t;
    controller_strategies : (string * string * string * Strategy.instruction array) Hstr.t;
    controller_running_proof_attempts : unit Hpan.t;
  }

let session_max_tasks = ref 1

let set_session_max_tasks n =
  session_max_tasks := n;
  Prove_client.set_max_running_provers n

let set_session_prover_upgrade_policy c p u =
  c.controller_config <- Whyconf.set_prover_upgrade_policy c.controller_config p u

let load_drivers c =
  let env = c.controller_env in
  let config = c.controller_config in
  let provers = Whyconf.get_provers config in
  Whyconf.Mprover.iter
    (fun _ p ->
     try
       let d = Whyconf.load_driver (Whyconf.get_main config) env p.Whyconf.driver [] in
       Whyconf.Hprover.add c.controller_provers p.Whyconf.prover (p,d)
     with e ->
       Debug.dprintf debug_call_prover
         "[Controller_itp] error while loading driver for prover %a: %a@."
         Whyconf.print_prover p.Whyconf.prover
         Exn_printer.exn_printer e)
    provers

let create_controller config env ses =
  let c =
    {
      controller_session = ses;
      controller_config = config;
      controller_env = env;
      controller_provers = Whyconf.Hprover.create 7;
      controller_strategies = Hstr.create 7;
      controller_running_proof_attempts = Hpan.create 17;
    }
  in
  load_drivers c;
  c


(* Cannot remove a proof_attempt that was scheduled but did not finish yet.
   It can be interrupted though. *)
let removable_proof_attempt c pa =
  try let () = Hpan.find c.controller_running_proof_attempts pa in false
  with Not_found -> true

let any_removable c any =
  match any with
  | APa pa -> removable_proof_attempt c pa
  | _ -> true

(* Check whether the subtree [n] contains an unremovable proof_attempt
   (ie: scheduled or running) *)
let check_removable c (n: any) =
  fold_all_any c.controller_session (fun acc any -> acc && any_removable c any) true n


let remove_subtree ~(notification:notifier) ~(removed:notifier) c (n: any) =
  if check_removable c n then
    Session_itp.remove_subtree ~notification ~removed c.controller_session n

(* Get children of any without proofattempts *)
let get_undetached_children_no_pa s any : any list =
  match any with
  | AFile f -> List.map (fun th -> ATh th) (file_theories f)
  | ATh th  -> List.map (fun g -> APn g) (theory_goals th)
  | ATn tn  -> List.map (fun pn -> APn pn) (get_sub_tasks s tn)
  | APn pn  -> List.map (fun tn -> ATn tn) (get_transformations s pn)
  | APa _ -> []



(* printing *)

module PSession = struct

  type any =
    | Session
    | File of file
    | Theory of theory
    | Goal of proofNodeID
    | Transf of transID
    | ProofAttempt of proof_attempt_node

  type 'a t = { tcont : controller;
                tkind : any }

  let decomp x =
    let s = x.tcont.controller_session in
    let n y acc = { x with tkind = y } :: acc in
    match x.tkind with
    | Session -> "", Hfile.fold (fun _ f -> n (File f)) (get_files s) []
    | File f ->
       string_of_file_path (file_path f),
       List.fold_right (fun th -> n (Theory th)) (file_theories f) []
    | Theory th ->
       let id = theory_name th in
       let name = id.Ident.id_string in
       let name = if th_proved s th then name^"!" else name^"?" in
       name,
       List.fold_right
         (fun g -> n (Goal g))
         (theory_goals th)
         []
    | Goal id ->
       let gid = get_proof_name s id in
       let name = gid.Ident.id_string in
       let name = if pn_proved s id then name^"!" else name^"?" in
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
       let name = if tn_proved s id then name^"!" else name^"?" in
       let sts = get_sub_tasks s id in
       name,
       List.fold_right (fun g -> n (Goal g)) sts []

end

module P = Print_tree.PMake(PSession)

let print_session fmt c =
  P.print fmt { PSession.tcont = c; PSession.tkind = PSession.Session }

(*********)




(** reload files, associating old proof attempts and transformations
    to the new goals.  old theories and old goals for which we cannot
    find a corresponding new theory resp. old goal are kept, with
    tasks associated to them *)

let reload_files (c : controller) ~shape_version =
  let old_ses = c.controller_session in
  c.controller_env <- Env.create_env (Env.get_loadpath c.controller_env);
  Whyconf.Hprover.reset c.controller_provers;
  load_drivers c;
  c.controller_session <- empty_session ~from:old_ses (get_dir old_ses);
  merge_files ~shape_version c.controller_env c.controller_session old_ses

exception Errors_list of exn list

let reload_files (c: controller) ~shape_version =
  let errors, b1, b2 = reload_files c ~shape_version in
  match errors with
  | [] -> b1, b2
  | _ -> raise (Errors_list errors)

let add_file c ?format fname =
  let file_is_detached,theories,errors =
    try false,(Session_itp.read_file c.controller_env ?format fname), None
    with e -> true,[], Some e
  in
  let (_ : file) = add_file_section c.controller_session fname ~file_is_detached theories format in
  errors

let add_file c ?format fname =
  let errors = add_file c ?format fname in
  match errors with
  | None -> ()
  | Some error -> raise (Errors_list [error])

module type Scheduler = sig
  val blocking: bool
  val multiplier: int
  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: prio:int -> (unit -> bool) -> unit
end

module Make(S : Scheduler) = struct

(* type for scheduled proof attempts *)
type sched_pa_rec =
  { spa_contr    : controller;
    spa_id       : proofNodeID;
    spa_pr       : Whyconf.prover;
    spa_limit    : Call_provers.resource_limit;
    spa_pr_scr   : string option;
    spa_callback : (proof_attempt_status -> unit);
    spa_ores     : Call_provers.prover_result option;
  }

let scheduled_proof_attempts : sched_pa_rec Queue.t = Queue.create ()

(* type for prover tasks in progress *)
type tasks_prog_rec =
  {
    tp_session  : Session_itp.session;
    tp_id       : proofNodeID;
    tp_pr       : Whyconf.prover;
    tp_callback : (proof_attempt_status -> unit);
    tp_started  : bool;
    tp_call     : Call_provers.prover_call;
    tp_ores     : Call_provers.prover_result option;
  }

let prover_tasks_in_progress :
    (Call_provers.prover_call,tasks_prog_rec) Hashtbl.t =
  Hashtbl.create 17

(* We need to separate tasks that are edited from proofattempt in progress
   because we are not using why3server for the edited proofs and timeout_handler
   rely on a loop on why3server's results. *)
let prover_tasks_edited = Queue.create ()

let timeout_handler_running = ref false


let number_of_running_provers = ref 0

let observer = ref (fun _ _ _ -> ())

let register_observer = (:=) observer

module Hprover = Whyconf.Hprover

(* calling provers, with limits adaptation *)


(* to avoid corner cases when prover results are obtained very closely
   to the time or mem limits, we adapt these limits when we replay a
   proof *)

let adapt_limits ~interactive ~use_steps limits a =
  let t, m, s =
    let timelimit = limits.Call_provers.limit_time in
    let memlimit = limits.Call_provers.limit_mem in
    let steplimit = limits.Call_provers.limit_steps in
    match a.proof_state with
    | Some { Call_provers.pr_answer = r;
             Call_provers.pr_time = t;
             Call_provers.pr_steps = s } ->
       (* increased time limit is 1 + twice the previous running time,
       but enforced to remain inside the interval [l,2l] where l is
       the previous time limit *)
       let t = truncate (1.5 +. 2.0 *. t) in
       let increased_time = if interactive then 0
                            else max timelimit (min t (2 * timelimit)) in
       (* increased mem limit is just 1.5 times the previous mem limit *)
       let increased_mem = if interactive then 0 else 3 * memlimit / 2 in
       begin
         match r with
         | Call_provers.OutOfMemory -> increased_time, memlimit, steplimit
         | Call_provers.Timeout -> timelimit, increased_mem, steplimit
         | Call_provers.Valid ->
            let steplimit =
              if use_steps then
                (* We need to allow at least one more step than what was used to
                   prove the same statement. Otherwise, the prover run out of
                   steps: this happens with cvc4 on some very fast proofs
                   (steps = 28).
                *)
                s + 1
              else
                0
            in
            increased_time, increased_mem, steplimit
         | Call_provers.Unknown _
         | Call_provers.StepLimitExceeded
         | Call_provers.Invalid -> increased_time, increased_mem, steplimit
         | Call_provers.Failure _
         | Call_provers.HighFailure ->
            (* correct ? failures are supposed to appear quickly anyway... *)
            timelimit, memlimit, steplimit
       end
    | None when interactive -> 0, 0, 0
    | None -> timelimit, memlimit, steplimit
  in
  { Call_provers.limit_time = t; limit_mem = m; limit_steps = s }

let group_answer a =
  match a with
  | Call_provers.OutOfMemory
  | Call_provers.Unknown _
  | Call_provers.Timeout -> Call_provers.Timeout
  | _ -> a

let fuzzy_proof_time nres ores =
  let ansold = ores.Call_provers.pr_answer in
  let told = ores.Call_provers.pr_time in
  let ansnew = nres.Call_provers.pr_answer in
  let tnew = nres.Call_provers.pr_time in
  if ansnew <> Call_provers.Timeout && group_answer ansold = group_answer ansnew &&
       tnew >= told *. 0.9 -. 0.1 && tnew <= told *. 1.1 +. 0.1
  then { nres with Call_provers.pr_time = told }
  else nres


let build_prover_call spa =
  let c = spa.spa_contr in
  let limit = spa.spa_limit in
  let (config_pr,driver) = Hprover.find c.controller_provers spa.spa_pr in
  let with_steps =
    Call_provers.(limit.limit_steps <> empty_limit.limit_steps) in
  let command =
    Whyconf.get_complete_command config_pr ~with_steps in
  try
    let task = Session_itp.get_task c.controller_session spa.spa_id in
    Debug.dprintf debug_sched "[build_prover_call] Script file = %a@."
                  (Pp.print_option Pp.string) spa.spa_pr_scr;
    let inplace = config_pr.Whyconf.in_place in
    let interactive = config_pr.Whyconf.interactive in
    try
      let call =
        Driver.prove_task ?old:spa.spa_pr_scr ~inplace ~command
                        ~limit ~interactive driver task
      in
      let pa =
        { tp_session  = c.controller_session;
          tp_id       = spa.spa_id;
          tp_pr       = spa.spa_pr;
          tp_callback = spa.spa_callback;
          tp_started  = false;
          tp_call     = call;
          tp_ores     = spa.spa_ores } in
      Hashtbl.replace prover_tasks_in_progress call pa
    with Sys_error _ as e ->
      spa.spa_callback (InternalFailure e)
  with Not_found (* goal has no task, it is detached *) ->
       spa.spa_callback Detached

let update_observer () =
  let scheduled = Queue.length scheduled_proof_attempts in
  let waiting_or_running = Hashtbl.length prover_tasks_in_progress in
  let running = !number_of_running_provers in
  !observer scheduled (waiting_or_running - running) running

let timeout_handler () =
  (* examine all the prover tasks in progress *)
  (* When no tasks are there, probably no tasks were scheduled and the server
     was not launched so getting results could fail. *)
  if Hashtbl.length prover_tasks_in_progress != 0 then begin
    let results = Call_provers.get_new_results ~blocking:S.blocking in
    List.iter (fun (call, prover_update) ->
      match Hashtbl.find prover_tasks_in_progress call with
      | ptp ->
        begin match prover_update with
        | Call_provers.NoUpdates -> ()
        | Call_provers.ProverStarted ->
            assert (not ptp.tp_started);
            ptp.tp_callback Running;
            incr number_of_running_provers;
            Hashtbl.replace prover_tasks_in_progress ptp.tp_call
              {ptp with tp_started = true}
        | Call_provers.ProverFinished res ->
            Hashtbl.remove prover_tasks_in_progress ptp.tp_call;
            if ptp.tp_started then decr number_of_running_provers;
            let res = Opt.fold fuzzy_proof_time res ptp.tp_ores in
            (* inform the callback *)
            ptp.tp_callback (Done res)
        | Call_provers.ProverInterrupted ->
            Hashtbl.remove prover_tasks_in_progress ptp.tp_call;
            if ptp.tp_started then decr number_of_running_provers;
            (* inform the callback *)
            ptp.tp_callback (Interrupted)
        | Call_provers.InternalFailure exn ->
            Hashtbl.remove prover_tasks_in_progress ptp.tp_call;
            if ptp.tp_started then decr number_of_running_provers;
            (* inform the callback *)
            ptp.tp_callback (InternalFailure (exn))
        end
      | exception Not_found -> ()
        (* We probably received ProverStarted after ProverFinished,
           because what is sent to and received from the server is
           not ordered. *)
    ) results;
  end;

  (* When blocking is activated, we are in script mode and we don't want editors
     to be launched so we don't need to go in this loop. *)
  if not S.blocking then begin
    (* Check for editor calls which are not finished *)
    let q = Queue.create () in
    while not (Queue.is_empty prover_tasks_edited) do
      (* call is an EditorCall *)
      let (callback,call,ores) as c =
        Queue.pop prover_tasks_edited in
      let prover_update = Call_provers.query_call call in
      match prover_update with
      | Call_provers.NoUpdates -> Queue.add c q
      | Call_provers.ProverFinished res ->
          (* res is meaningless for edition, we returned the old result *)
          (* inform the callback *)
          callback (match ores with None -> Done res | Some r -> Done r)
      | _ -> assert (false) (* An edition can only return Noupdates or finished *)
    done;
    Queue.transfer q prover_tasks_edited;
  end;

  (* if the number of prover tasks is less than S.multiplier times the maximum
     number of running provers, then we heuristically decide to add
     more tasks *)
  begin
    try
      for _i = Hashtbl.length prover_tasks_in_progress
          to S.multiplier * !session_max_tasks do
        let spa = Queue.pop scheduled_proof_attempts in
        try build_prover_call spa
        with e when not (Debug.test_flag Debug.stack_trace) ->
          spa.spa_callback (InternalFailure e)
      done
  with Queue.Empty -> ()
  end;
  update_observer ();
  true

let interrupt () =
  (* Interrupt provers *)
  Hashtbl.iter
    (fun call e ->
     Call_provers.interrupt_call call;
     e.tp_callback Interrupted)
    prover_tasks_in_progress;
  Hashtbl.clear prover_tasks_in_progress;
  (* Do not interrupt editors
  while not (Queue.is_empty prover_tasks_edited) do
    let (_ses,_id,_pr,callback,_started,_call,_ores) =
      Queue.pop prover_tasks_edited in
    callback Interrupted
  done;
  *)
  number_of_running_provers := 0;
  while not (Queue.is_empty scheduled_proof_attempts) do
    let spa = Queue.pop scheduled_proof_attempts in
    spa.spa_callback Interrupted
  done;
  !observer 0 0 0

let run_timeout_handler () =
  if not !timeout_handler_running then
    begin
      timeout_handler_running := true;
      S.timeout ~ms:default_delay_ms timeout_handler;
    end

let schedule_proof_attempt c id pr ?save_to ~limit ~callback ~notification =
  let ses = c.controller_session in
  let callback panid s =
    begin
      match s with
      | UpgradeProver _ | Removed _ -> ()
      | Scheduled ->
         Hpan.add c.controller_running_proof_attempts panid ();
         update_goal_node notification ses id
      | Running -> update_goal_node notification ses id
      | Done res ->
         Hpan.remove c.controller_running_proof_attempts panid;
         update_proof_attempt ~obsolete:false notification ses id pr res;
         update_goal_node notification ses id
      | Interrupted
      | InternalFailure _ ->
         Hpan.remove c.controller_running_proof_attempts panid;
         (* what to do ?
         update_proof_attempt ~obsolete:false notification ses id pr res;
          *)
         update_goal_node notification ses id
      | Detached -> assert false
      | Uninstalled _ -> assert false
      | Undone -> assert false
    end;
    callback panid s
  in
  let ores,proof_script =
    try
      let h = get_proof_attempt_ids ses id in
      let pa = Hprover.find h pr in
      let a = get_proof_attempt_node ses pa in
      let old_res = a.proof_state in
      let script =
        if save_to = None then
          Opt.map (fun s ->
                            Debug.dprintf debug_sched "Script file = %s@." s;
                            Filename.concat (get_dir ses) s) a.proof_script
        else
          save_to
      in
      old_res, script
    with Not_found | Session_itp.BadID -> None,save_to
  in
  let panid = graft_proof_attempt ~limit ses id pr in
  let spa =
    { spa_contr    = c;
      spa_id       = id;
      spa_pr       = pr;
      spa_limit    = limit;
      spa_pr_scr   = proof_script;
      spa_callback = callback panid;
      spa_ores     = ores } in
  Queue.add spa scheduled_proof_attempts;
  callback panid Scheduled;
  run_timeout_handler ()




(*** { 2 edition of proof scripts} *)

(* create the path to a file for saving the external proof script *)
let create_file_rel_path c pr pn =
  let session = c.controller_session in
  let driver = snd (Hprover.find c.controller_provers pr) in
  let task = Session_itp.get_task session pn in
  let session_dir = Session_itp.get_dir session in
  let th = get_encapsulating_theory session (APn pn) in
  let th_name = (Session_itp.theory_name th).Ident.id_string in
  let f = get_encapsulating_file session (ATh th) in
  let fn = Filename.chop_extension (Session_itp.basename (file_path f)) in
  let file = Driver.file_of_task driver fn th_name task in
  let file = Filename.concat session_dir file in
  let file = Sysutil.uniquify file in
  let file = Sysutil.relativize_filename session_dir file in
  match file with
  | [f] -> f
  | _ -> assert false

let prepare_edition c ?file pn pr ~notification =
  let session = c.controller_session in
  let proof_attempts_id = get_proof_attempt_ids session pn in
  let panid =
    try
      let panid = Hprover.find proof_attempts_id pr in
      (* if no proof script yet, we need to add one
         it happens e.g when editing a file for an automatic prover
       *)
      let pa = get_proof_attempt_node session panid in
      match pa.proof_script with
      | None ->
         let file = match file with
           | Some f -> f
           | None -> create_file_rel_path c pr pn
         in
         set_proof_script pa file;
         panid
      | Some _ -> panid
    with Not_found ->
      let file = match file with
        | Some f -> f
        | None -> create_file_rel_path c pr pn
      in
      let limit = Call_provers.empty_limit in
      graft_proof_attempt session pn pr ~file ~limit
  in
  update_goal_node notification session pn;
  let pa = get_proof_attempt_node session panid in
  let file = Opt.get pa.proof_script in
  let old_res = pa.proof_state in
  let session_dir = Session_itp.get_dir session in
  let file = Filename.concat session_dir file in
  let old =
    if Sys.file_exists file
    then
      begin
        let backup = file ^ ".bak" in
        if Sys.file_exists backup
        then Sys.remove backup;
        Sys.rename file backup;
        Some(open_in backup)
      end
    else None
  in
  let ch = open_out file in
  let fmt = formatter_of_out_channel ch in
  let task = Session_itp.get_task session pn in
  let driver = snd (Hprover.find c.controller_provers pr) in
  Driver.print_task ?old driver fmt task;
  Opt.iter close_in old;
  close_out ch;
  panid,file,old_res

exception Editor_not_found

let schedule_edition c id pr ~callback ~notification =
  Debug.dprintf debug_sched "[Sched] Scheduling an edition@.";
  let config = c.controller_config in
  let session = c.controller_session in
  let prover_conf = Whyconf.get_prover_config config pr in
  (* Make sure editor exists. Fails otherwise *)
  let editor =
    match prover_conf.Whyconf.editor with
    | "" -> Whyconf.(default_editor (get_main config))
    | s ->
       try
         let ed = Whyconf.editor_by_id config s in
         String.concat " " (ed.Whyconf.editor_command ::
                              ed.Whyconf.editor_options)
       with Not_found -> raise Editor_not_found
  in
  let panid,file,old_res = prepare_edition c id pr ~notification in
  (* Notification node *)
  let callback panid s =
    begin
      match s with
      | UpgradeProver _ -> ()
      | Running -> ()
      | Done res ->
         (* set obsolete to true since we do not know if the manual
            proof was completed or not *)
         Debug.dprintf debug_sched
                       "Setting status of %a under parent %a to obsolete@."
                       print_proofAttemptID panid print_proofNodeID id;
         update_proof_attempt ~obsolete:true notification session id pr res;
         update_goal_node notification session id
      | Interrupted
      | InternalFailure _ ->
         update_goal_node notification session id
      | Undone | Detached | Uninstalled _ | Scheduled | Removed _ -> assert false
    end;
    callback panid s
  in
  Debug.dprintf debug_sched "[Editing] goal %s with command '%s' on file %s@."
                (Session_itp.get_proof_name session id).Ident.id_string
                editor file;
  let call = Call_provers.call_editor ~command:editor file in
  callback panid Running;
  Queue.add (callback panid,call,old_res) prover_tasks_edited;
  run_timeout_handler ()

exception TransAlreadyExists of string * string
exception GoalNodeDetached of proofNodeID

(*** { 2 transformations} *)

let schedule_transformation c id name args ~callback ~notification =
  let callback s =
    begin match s with
          | TSdone tid -> update_trans_node notification c.controller_session tid
          | TSscheduled
          | TSfailed _ | TSfatal _  -> ()
    end;
    callback s
  in
  let apply_trans () =
    begin
      try
        let subtasks =
          apply_trans_to_goal ~allow_no_effect:false
                              c.controller_session c.controller_env name args id
        in
        let tid = graft_transf c.controller_session id name args subtasks in
        callback (TSdone tid)
      with
      | NoProgress ->
         (* if result is same as input task, consider it as a failure *)
         callback (TSfailed (id, NoProgress))
      | (Arg_trans _ | Arg_trans_decl _ | Arg_trans_missing _
        | Arg_trans_term _ | Arg_trans_term2 _ | Arg_trans_term3 _
        | Arg_trans_pattern _ | Arg_trans_type _ | Arg_bad_hypothesis _
        | Cannot_infer_type _ | Unnecessary_terms _ | Parse_error _
        | Arg_expected _ | Arg_theory_not_found _ | Arg_expected_none _
        | Arg_qid_not_found _ | Arg_pr_not_found _ | Arg_error _
        | Arg_parse_type_error _ | Unnecessary_arguments _
        | Reflection.NoReification ) as e ->
          callback (TSfailed (id, e))
      | e when not (Debug.test_flag Debug.stack_trace) ->
          (* "@[Exception raised in Session_itp.apply_trans_to_goal %s:@ %a@.@]"
          name Exn_printer.exn_printer e; TODO *)
        callback (TSfatal (id, e))
    end;
    false
  in
  if Session_itp.is_detached c.controller_session (APn id) then
    raise (GoalNodeDetached id);
  if Session_itp.check_if_already_exists c.controller_session id name args then
    raise (TransAlreadyExists (name, List.fold_left (fun acc s -> s ^ " " ^ acc) "" args));
  S.idle ~prio:0 apply_trans;
  callback TSscheduled


open Strategy

let run_strategy_on_goal
    c id strat ~callback_pa ~callback_tr ~callback ~notification =
  let rec exec_strategy pc strat g =
    if pc < 0 || pc >= Array.length strat then
      callback STShalt
    else
      match Array.get strat pc with
      | Icall_prover(p,timelimit,memlimit) ->
         let callback panid res =
           callback_pa panid res;
           match res with
           | UpgradeProver _ | Scheduled | Running -> (* nothing to do yet *) ()
           | Done { Call_provers.pr_answer = Call_provers.Valid } ->
              (* proof succeeded, nothing more to do *)
              callback STShalt
           | Interrupted | InternalFailure _ ->
              callback STShalt
           | Done _ ->
              (* proof did not succeed, goto to next step *)
              callback (STSgoto (g,pc+1));
              let run_next () = exec_strategy (pc+1) strat g; false in
              S.idle ~prio:0 run_next
           | Undone | Detached | Uninstalled _ | Removed _ ->
                         (* should not happen *)
                         assert false
         in
         let limit = { Call_provers.empty_limit with
                       Call_provers.limit_time = timelimit;
                       limit_mem  = memlimit} in
         schedule_proof_attempt c g p ?save_to:None ~limit ~callback ~notification
      | Itransform(trname,pcsuccess) ->
         let callback ntr =
           callback_tr trname [] ntr;
           match ntr with
           | TSfatal (id, e) ->
               callback (STSfatal (trname, id, e))
           | TSfailed _e -> (* transformation failed *)
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
         schedule_transformation c g trname [] ~callback ~notification
      | Igoto pc ->
         callback (STSgoto (g,pc));
         exec_strategy pc strat g
  in
  exec_strategy 0 strat id

let schedule_pa_with_same_arguments
    c (pa: proof_attempt_node) (pn: proofNodeID) ~callback ~notification =
  let prover = pa.prover in
  let limit = pa.limit in
  schedule_proof_attempt c pn prover ~limit ~callback ~notification

let schedule_tr_with_same_arguments
    c (tr: transID) (pn: proofNodeID) ~callback ~notification =
  let s = c.controller_session in
  let args = get_transf_args s tr in
  let name = get_transf_name s tr in
  let callback = callback name args in

  schedule_transformation c pn name args ~callback ~notification

let proof_is_complete pa =
  match pa.Session_itp.proof_state with
  | None -> false
  | Some pr ->
     not pa.Session_itp.proof_obsolete &&
       Call_provers.(pr.pr_answer = Valid)


let clean c ~removed nid =

  (* clean should not change proved status *)
  let notification any =
    Format.eprintf "Cleaning error: cleaning attempts to change status of node %a@." fprintf_any any
  in
  let s = c.controller_session in
  (* This function is applied on leafs first for the case of removes *)
  let clean_aux () any =
    let do_remove =
      Session_itp.is_detached s any ||
      match any with
      | APa pa ->
         let pa = Session_itp.get_proof_attempt_node s pa in
         pn_proved s pa.parent && not (proof_is_complete pa)
      | ATn tn ->
         let pn = get_trans_parent s tn in
         pn_proved s pn && not (tn_proved s tn)
      | _ -> false
    in
    if do_remove then
      remove_subtree ~notification ~removed c any
  in

  match nid with
  | Some nid ->
      Session_itp.fold_all_any s clean_aux () nid
  | None ->
      Session_itp.fold_all_session s clean_aux ()

(* This function folds on any subelements of given node and tries to mark all
   proof attempts it encounters *)
let mark_as_obsolete ~notification c any =
  let s = c.controller_session in
  (* Case for proof attempt only *)
  let mark_as_obsolete_pa n =
    let parent = get_proof_attempt_parent s n in
    Session_itp.mark_obsolete s n;
    notification (APa n);
    update_goal_node notification s parent
  in
  match any with
  | Some any ->
      fold_all_any s
        (fun () any -> match any with
        | APa n -> mark_as_obsolete_pa n
        | _ -> ()) () any
  | None ->
      session_iter_proof_attempt
        (fun pa _pan ->
          mark_as_obsolete_pa pa) s

exception BadCopyPaste

(* Reproduce the transformation made on node on an other one *)
let rec copy_rec ~notification ~callback_pa ~callback_tr c from_any to_any =
  let s = c.controller_session in
  match from_any, to_any with
(*
    | AFile _, AFile _ ->
        raise BadCopyPaste
    | ATh _from_th, ATh _to_th ->
        raise BadCopyPaste
 *)
    | APn from_pn, APn to_pn ->
      let from_pa_list = get_proof_attempts s from_pn in
      List.iter (fun x -> schedule_pa_with_same_arguments ?save_to:None c x to_pn
          ~callback:callback_pa ~notification) from_pa_list;
      let from_tr_list = get_transformations s from_pn in
      let callback x tr args st = callback_tr tr args st;
        match st with
        | TSdone tid ->
          copy_rec c (ATn x) (ATn tid) ~notification ~callback_pa ~callback_tr
        | _ -> ()
      in
      List.iter (fun x -> schedule_tr_with_same_arguments c x to_pn
          ~callback:(callback x) ~notification) from_tr_list
    | ATn from_tn, ATn to_tn ->
        let from_tn_list = get_sub_tasks s from_tn in
        let to_tn_list = get_sub_tasks s to_tn in
        let rec iter_copy l1 l2 =
          match l1,l2 with
          | x::r1, y::r2 ->
             copy_rec c (APn x) (APn y)
                      ~notification ~callback_pa ~callback_tr;
             iter_copy r1 r2
          | _ -> ()
        in iter_copy from_tn_list to_tn_list
    | _ -> raise BadCopyPaste


let copy_paste ~notification ~callback_pa ~callback_tr c from_any to_any =
  let s = c.controller_session in
  if is_below s to_any from_any then
    raise BadCopyPaste;
  match from_any, to_any with
  | APn _, APn _ ->
     copy_rec ~notification ~callback_pa ~callback_tr c from_any to_any
  | ATn from_tn, APn to_pn ->
     let callback tr args st =
       callback_tr tr args st;
       match st with
       | TSdone tid ->
          copy_rec c (ATn from_tn) (ATn tid) ~notification ~callback_pa ~callback_tr
       | _ -> ()
     in
     schedule_tr_with_same_arguments c from_tn to_pn ~callback ~notification
  | _ -> raise BadCopyPaste








(***************** {2 replay} ****************)


let debug_replay = Debug.register_flag "replay" ~desc:"Debug@ info@ for@ replay"

let find_prover notification c goal_id pr =
  if Hprover.mem c.controller_provers pr then `Found pr else
   match Whyconf.get_prover_upgrade_policy c.controller_config pr with
   | exception Not_found -> `Keep
   | Whyconf.CPU_keep -> `Keep
   | Whyconf.CPU_remove -> `Remove
   | Whyconf.CPU_upgrade new_pr ->
      (* does a proof using new_pr already exists ? *)
      if Hprover.mem (get_proof_attempt_ids c.controller_session goal_id) new_pr
      then (* yes, then we remove the attempt *)
        `Remove
      else
        begin
          (* we modify the prover in-place *)
          Session_itp.change_prover notification c.controller_session goal_id pr new_pr;
          `Found new_pr
        end
   | Whyconf.CPU_duplicate new_pr ->
      (* does a proof using new_pr already exists ? *)
      if Hprover.mem (get_proof_attempt_ids c.controller_session goal_id) new_pr
      then (* yes, then we do nothing *)
        `Keep
      else
        begin
          (* we duplicate the proof attempt *)
          `Found new_pr
        end


let replay_proof_attempt c pr limit (parid: proofNodeID) id ~callback ~notification =
  (* The replay can be done on a different machine so we need
     to check more things before giving the attempt to the scheduler *)
  match find_prover notification c parid pr with
  | `Keep -> callback id (Uninstalled pr)
  | `Remove ->
     (* it is necessary to call the callback before effectively removing the node, otherwise, a bad id will be used in the callback *)
      callback id (Removed pr);
      remove_proof_attempt c.controller_session parid pr
  | `Found pr' ->
     try
       if pr' <> pr then callback id (UpgradeProver pr');
       let _ = get_task c.controller_session parid in
       schedule_proof_attempt ?save_to:None c parid pr' ~limit ~callback ~notification
     with Not_found ->
       callback id Detached



type report =
  | Result of Call_provers.prover_result * Call_provers.prover_result
  (** Result(new_result,old_result) *)
  | CallFailed of exn
  | Replay_interrupted
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
  | CallFailed e ->
    Format.fprintf fmt "Callfailed %a@." Exn_printer.exn_printer e
  | Replay_interrupted ->
    Format.fprintf fmt "Interrupted@."
  | Prover_not_installed ->
    Format.fprintf fmt "Prover not installed@."
  | Edited_file_absent _ ->
    Format.fprintf fmt "No edited file@."
  | No_former_result new_r ->
    Format.fprintf fmt "new_result = %a, no former result@."
      Call_provers.print_prover_result new_r

(* TODO to be removed when we have a better way to print *)
let replay_print fmt (lr: (proofNodeID * Whyconf.prover * Call_provers.resource_limit * report) list) =
  let pp_elem fmt (id, pr, rl, report) =
    fprintf fmt "ProofNodeID: %d, Prover: %a, Timelimit?: %d, Result: %a@."
      (Obj.magic id) Whyconf.print_prover pr
      rl.Call_provers.limit_time print_report report
  in
  Format.fprintf fmt "%a@." (Pp.print_list Pp.newline pp_elem) lr

let replay ~valid_only ~obsolete_only ?(use_steps=false) ?(filter=fun _ -> true)
           c ~callback ~notification ~final_callback ~any =

  let session = c.controller_session in
  let count = ref 0 in
  let report = ref [] in
  let found_upgraded_prover = ref false in

  let craft_report s id limits pa =
    let pr = pa.Session_itp.prover in
    match s with
    | UpgradeProver _ -> found_upgraded_prover := true
    | Removed _ ->
       found_upgraded_prover := true;
       decr count
    | Scheduled | Running -> ()
    | Undone | Interrupted ->
       decr count;
       report := (id, pr, limits, Replay_interrupted ) :: !report
    | Done new_r ->
       decr count;
       begin
         match pa.Session_itp.proof_state with
         | None -> (report := (id, pr, limits, No_former_result new_r) :: !report)
         | Some old_r -> report := (id, pr, limits, Result (new_r, old_r)) :: !report
       end
    | InternalFailure e ->
       decr count;
       report := (id, pr, limits, CallFailed (e)) :: !report
    | Uninstalled _ ->
       decr count;
       report := (id, pr, limits, Prover_not_installed) :: !report;
    | Detached -> decr count
  in

  let need_replay id pa =
    filter pa &&
      (pa.proof_obsolete || not obsolete_only) &&
        (* When on a single proofattempt node, we want to always replay even non
           valid proofattempts.
        *)
        (any = Some (APa id) || not valid_only ||
           match pa.Session_itp.proof_state with
           | None -> false
           | Some pr -> Call_provers.(pr.pr_answer = Valid))
  in


  (* TODO count the number of node in a more efficient way *)
  (* Counting the number of proof_attempt to print report only once *)
  (match any with
  | None ->
      Session_itp.session_iter_proof_attempt
        (fun paid pa -> if need_replay paid pa then incr count) session
  | Some nid ->
      Session_itp.any_iter_proof_attempt session
        (fun paid pa -> if need_replay paid pa then incr count) nid);

  (* Replaying function *)
  let replay_pa id pa =
    let is_need_replay = need_replay id pa in
    Debug.dprintf debug_replay "Need_replay is set to %b for prover %a@."
      is_need_replay Whyconf.print_prover pa.prover;
    if is_need_replay then
      begin
        let parid = pa.parent in
        let pr = pa.prover in
        (* TODO: if pr is not installed, lookup for a replacement policy
         OR: delegate this work to the replay_proof_attempt function *)
        (* If use_steps, we give only steps as a limit
         TODO: steps should not be used if prover was replaced above *)
        let limit =
          if use_steps then
            Call_provers.{empty_limit with limit_steps = pa.limit.limit_steps}
          else
            Call_provers.{ pa.limit with limit_steps = empty_limit.limit_steps }
        in
        replay_proof_attempt c pr limit parid id
                             ~callback:(fun id s ->
                                        craft_report s parid limit pa;
                                        callback id s;
                                        if !count = 0 then
                                          final_callback !found_upgraded_prover !report)
                             ~notification
      end in

  if !count = 0 then final_callback !found_upgraded_prover !report else
  (* Calling replay on all the proof_attempts of the session *)
  match any with
  | None -> Session_itp.session_iter_proof_attempt replay_pa session
  | Some nid -> Session_itp.any_iter_proof_attempt session replay_pa nid




(*************** bisect **********)



let debug = Debug.register_flag ~desc:"Task bisection" "bisect"

let create_rem_list =
  let b = Buffer.create 17 in
  fun rem ->
  Buffer.clear b;
  let add pr id =
    if Buffer.length b > 0 then Buffer.add_char b ',';
    Buffer.add_string b (Pp.string_of pr id)
  in
  let remove_ts ts = add Pretty.print_ts ts in
  let remove_ls ls = add Pretty.print_ls ls in
  let remove_pr pr = add Pretty.print_pr pr in
  Ty.Sts.iter remove_ts rem.Eliminate_definition.rem_ts;
  Term.Sls.iter remove_ls rem.Eliminate_definition.rem_ls;
  Decl.Spr.iter remove_pr rem.Eliminate_definition.rem_pr;
  Buffer.contents b


exception CannotRunBisectionOn of proofAttemptID


let bisect_proof_attempt ~callback_tr ~callback_pa ~notification ~removed c pa_id =
  let ses = c.controller_session in
  let pa = get_proof_attempt_node ses pa_id in
  if not (proof_is_complete pa) then
    raise (CannotRunBisectionOn pa_id); (* proof attempt should be valid *)
  let goal_id = pa.parent in
  let prover = pa.prover in
  let limit = { pa.limit with
                Call_provers.limit_steps =
                  Call_provers.empty_limit.Call_provers.limit_steps }
  in
  let timelimit = ref limit.Call_provers.limit_time in
  let set_timelimit res =
    timelimit := 1 + (int_of_float (floor res.Call_provers.pr_time)) in
  let bisect_end rem =
    if Decl.Spr.is_empty rem.Eliminate_definition.rem_pr &&
         Term.Sls.is_empty rem.Eliminate_definition.rem_ls &&
           Ty.Sts.is_empty rem.Eliminate_definition.rem_ts
    then
      Debug.dprintf debug "Bisecting didn't reduce the task.@."
    else
      begin
        Debug.dprintf debug "Bisecting done.@.";
        (* apply again the transformation *)
        let rem = create_rem_list rem in
        let callback st =
          callback_tr "remove" [rem] st;
          begin match st with
          | TSscheduled -> ()
          | TSfailed _ -> assert false
          | TSfatal _ -> assert false
          | TSdone trid ->
             match get_sub_tasks ses trid with
             | [pn] ->
                let limit = { limit with Call_provers.limit_time = !timelimit; } in
                let callback paid st =
                  callback_pa paid st;
                  begin match st with
                  | UpgradeProver _ | Scheduled | Running -> ()
                  | Detached | Uninstalled _ | Removed _ -> assert false
                  | Undone | Interrupted -> Debug.dprintf debug "Bisecting interrupted.@."
                  | InternalFailure exn ->
                     (* Perhaps the test can be considered false in this case? *)
                     Debug.dprintf debug "Bisecting interrupted by an error %a.@."
                                   Exn_printer.exn_printer exn
                  | Done res ->
                     assert (res.Call_provers.pr_answer = Call_provers.Valid);
                     Debug.dprintf debug "Bisecting: %a.@."
                                   Call_provers.print_prover_result res
                  end
                in
                schedule_proof_attempt ?save_to:None c pn prover ~limit ~callback ~notification
             | _ -> assert false
          end
        in
        Debug.dprintf debug "To remove: %s@." rem;
        schedule_transformation c goal_id "remove" [rem] ~callback ~notification
      end
  in
  let rec bisect_step rem kont =
    (* we have to:
       1) apply transformation remove with the given rem
       2) on the generated sub-goal, run the prover with some callback
       3) the callback should :
          compute (next_iter success_value)
          if result is done, do nothing more
          if result is some new rem, remove the previous transformation
           and recursively call bisect_step
     *)
    let rem = create_rem_list rem in
    let callback st =
      begin match st with
      | TSscheduled ->
         Debug.dprintf
           debug
           "[Bisect] transformation 'remove' scheduled@.";
         callback_tr "remove" [rem] st;
      | TSfatal (_, exn)
      | TSfailed(_,exn) ->
         (* may happen if removing a type or a lsymbol that is used
later on. We do has if proof fails. *)
         begin
           Debug.dprintf
             debug
             "[Bisect] transformation failed %a@." Exn_printer.exn_printer exn;
           match kont false with
           | Eliminate_definition.BSstep (rem,kont) ->
              bisect_step rem kont
           | Eliminate_definition.BSdone rem ->
              bisect_end rem
         end
      | TSdone trid ->
         Debug.dprintf
           debug
           "[Bisect] transformation 'remove' succeeds@.";
         callback_tr "remove" [rem] st;
         match get_sub_tasks ses trid with
         | [pn] ->
            let limit = { limit with Call_provers.limit_time = !timelimit; } in
            let callback paid st =
              callback_pa paid st;
              begin
              match st with
              | UpgradeProver _ | Removed _ -> ()
              | Scheduled ->
                 Debug.dprintf
                   debug "[Bisect] prover on subtask is scheduled@."
              | Running ->
                 Debug.dprintf
                   debug "[Bisect] prover on subtask is running@.";
              | Detached
              | Uninstalled _ -> assert false
              | Undone | Interrupted -> Debug.dprintf debug "Bisecting interrupted.@."
              | InternalFailure exn ->
                 (* Perhaps the test can be considered false in this case? *)
                 Debug.dprintf debug "[Bisect] prover interrupted by an error: %a.@."
                               Exn_printer.exn_printer exn
              | Done res ->
                 Debug.dprintf
                   debug "[Bisect] prover on subtask returns %a@."
                   Call_provers.print_prover_answer res.Call_provers.pr_answer;
                 let b = res.Call_provers.pr_answer = Call_provers.Valid in
                 if b then set_timelimit res;
                 match kont b with
                 | Eliminate_definition.BSstep (rem,kont) ->
                    Session_itp.remove_subtree ~notification ~removed ses (Session_itp.ATn trid);
                    bisect_step rem kont
                 | Eliminate_definition.BSdone rem ->
                    bisect_end rem
              end
            in
            Debug.dprintf
              debug "[Bisect] running the prover on subtask@.";
            schedule_proof_attempt ?save_to:None c pn prover ~limit ~callback ~notification
         | _ -> assert false
      end
    in
    Debug.dprintf debug "To remove: %s@." rem;
    schedule_transformation c goal_id "remove" [rem] ~callback ~notification
  in
  Debug.dprintf debug "Bisecting with %a started.@."
                Whyconf.print_prover prover;
  let t = get_task ses goal_id in
  match Eliminate_definition.bisect_step t with
  | Eliminate_definition.BSdone _ -> assert false
  | Eliminate_definition.BSstep(rem,kont) -> bisect_step rem kont

end
