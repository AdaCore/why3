open Format
open Session_itp


let debug_sched = Debug.register_info_flag "scheduler"
  ~desc:"Print@ debugging@ messages@ about@ scheduling@ of@ prover@ calls@ \
         and@ transformation@ applications."

exception Noprogress

let () = Exn_printer.register
    (fun fmt e ->
      match e with
      | Noprogress ->
          Format.fprintf fmt "The transformation made no progress.\n"
      | _ -> raise e)

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
  | Unedited          -> fprintf fmt "Unedited"
  | JustEdited        -> fprintf fmt "JustEdited"
  | Interrupted       -> fprintf fmt "Interrupted"
  | Scheduled         -> fprintf fmt "Scheduled"
  | Running           -> fprintf fmt "Running"
  | Done r            ->
      fprintf fmt "Done(%a)" Call_provers.print_prover_result r
  | InternalFailure e ->
      fprintf fmt "InternalFailure(%a)" Exn_printer.exn_printer e
  | Uninstalled pr    ->
      fprintf fmt "Prover %a is uninstalled" Whyconf.print_prover pr

type transformation_status =
  | TSscheduled | TSdone of transID | TSfailed of (proofNodeID * exn)

let print_trans_status fmt st =
  match st with
  | TSscheduled -> fprintf fmt "TScheduled"
  | TSdone _tid -> fprintf fmt "TSdone" (* TODO print tid *)
  | TSfailed _e -> fprintf fmt "TSfailed"

type strategy_status = STSgoto of proofNodeID * int | STShalt

let print_strategy_status fmt st =
  match st with
  | STSgoto(id,n) ->
      fprintf fmt "goto step %d in proofNode %a" n print_proofNodeID id
  | STShalt -> fprintf fmt "halt"


type controller =
  { mutable controller_session: Session_itp.session;
    controller_config : Whyconf.config;
    controller_env: Env.env;
    controller_provers:
      (Whyconf.config_prover * Driver.driver) Whyconf.Hprover.t;
  }


let create_controller config env ses =
  let c =
    {
      controller_session = ses;
      controller_config = config;
      controller_env = env;
      controller_provers = Whyconf.Hprover.create 7;
    }
  in
  let provers = Whyconf.get_provers config in
  Whyconf.Mprover.iter
    (fun _ p ->
     try
       let d = Whyconf.load_driver (Whyconf.get_main config) env p.Whyconf.driver [] in
       Whyconf.Hprover.add c.controller_provers p.Whyconf.prover (p,d)
     with e ->
       Format.eprintf
         "[Controller_itp] error while loading driver for prover %a: %a@."
         Whyconf.print_prover p.Whyconf.prover
         Exn_printer.exn_printer e)
    provers;
  c


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

  open Stdlib

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
    | Session -> "", Hstr.fold (fun _ f -> n (File f)) (get_files s) []
    | File f ->
       (file_name f),
       List.fold_right
          (fun th -> n (Theory th))
          (file_detached_theories f)
          (List.fold_right (fun th -> n (Theory th)) (file_theories f) [])
    | Theory th ->
       let id = theory_name th in
       let name = id.Ident.id_string in
       let name = if th_proved s th then name^"!" else name^"?" in
       name,
       List.fold_right
         (fun g -> n (Goal g))
         (theory_goals th)
         (List.fold_right (fun g -> n (Goal g)) (theory_detached_goals th) [])
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
       let dsts = get_detached_sub_tasks s id in
       name,
       List.fold_right (fun g -> n (Goal g)) sts
                       (List.fold_right (fun g -> n (Goal g)) dsts [])

end

module P = Print_tree.PMake(PSession)

let print_session fmt c =
  P.print fmt { PSession.tcont = c; PSession.tkind = PSession.Session }

(*********)



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

let merge_file (old_ses : session) (c : controller) ~use_shapes _ file =
  let format = file_format file in
  let old_theories = file_theories file in
  let file_name = Filename.concat (get_dir old_ses) (file_name file) in
  let new_theories =
    try
      read_file c.controller_env file_name ?format
    with e -> (* TODO: filter only syntax error and typing errors *)
      raise e
  in
  merge_file_section
    c.controller_session ~use_shapes ~old_ses ~old_theories
    ~env:c.controller_env file_name new_theories format

let reload_files (c : controller) ~use_shapes =
  let old_ses = c.controller_session in
  c.controller_session <-
    empty_session ~shape_version:(get_shape_version old_ses) (get_dir old_ses);
  try
    Stdlib.Hstr.iter
      (fun f -> merge_file old_ses c ~use_shapes f)
      (get_files old_ses);
  with e ->
    c.controller_session <- old_ses;
    raise e

let add_file c ?format fname =
  let theories = read_file c.controller_env ?format fname in
  add_file_section c.controller_session fname theories format


module type Scheduler = sig
  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: prio:int -> (unit -> bool) -> unit
end

module Make(S : Scheduler) = struct

let scheduled_proof_attempts = Queue.create ()

let prover_tasks_in_progress = Queue.create ()

let timeout_handler_running = ref false

let max_number_of_running_provers = ref 1

let set_max_tasks n =
  max_number_of_running_provers := n;
  Prove_client.set_max_running_provers n

let number_of_running_provers = ref 0

let observer = ref (fun _ _ _ -> ())

let register_observer = (:=) observer

module Hprover = Whyconf.Hprover

let build_prover_call ?proof_script ~cntexample c id pr limit callback =
  let (config_pr,driver) = Hprover.find c.controller_provers pr in
  let command =
    Whyconf.get_complete_command
      config_pr
      ~with_steps:Call_provers.(limit.limit_steps <> empty_limit.limit_steps) in
  let task = Session_itp.get_task c.controller_session id in
  let table = Session_itp.get_table c.controller_session id in
  let call =
    Driver.prove_task ?old:proof_script ~cntexample:cntexample ~inplace:false ~command
                      ~limit ?name_table:table driver task
  in
  let pa = (c.controller_session,id,pr,proof_script,callback,false,call) in
  Queue.push pa prover_tasks_in_progress

let timeout_handler () =
  (* examine all the prover tasks in progress *)
  let q = Queue.create () in
  while not (Queue.is_empty prover_tasks_in_progress) do
    let (ses,id,pr,pr_script,callback,started,call) as c =
      Queue.pop prover_tasks_in_progress in
    match Call_provers.query_call call with
    | Call_provers.NoUpdates -> Queue.add c q
    | Call_provers.ProverStarted ->
       assert (not started);
       callback Running;
       incr number_of_running_provers;
       Queue.add (ses,id,pr,pr_script,callback,true,call) q
    | Call_provers.ProverFinished res when pr_script = None ->
       if started then decr number_of_running_provers;
       (* update the session *)
       update_proof_attempt ses id pr res;
       (* inform the callback *)
       callback (Done res)
    | Call_provers.ProverFinished res (* when pr_script <> None *) ->
       if started then decr number_of_running_provers;
       (* update the session *)
       update_proof_attempt ~obsolete:true ses id pr res;
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
  begin
    try
      for _i = Queue.length prover_tasks_in_progress
          to 3 * !max_number_of_running_provers do
        let (c,id,pr,limit,proof_script,callback,cntexample) = Queue.pop scheduled_proof_attempts in
        try
          build_prover_call ?proof_script ~cntexample c id pr limit callback
        with e when not (Debug.test_flag Debug.stack_trace) ->
          (*Format.eprintf
            "@[Exception raised in Controller_itp.build_prover_call:@ %a@.@]"
            Exn_printer.exn_printer e;*)
          callback (InternalFailure e)
      done
  with Queue.Empty -> ()
  end;
  let scheduled = Queue.length scheduled_proof_attempts in
  let waiting_or_running = Queue.length prover_tasks_in_progress in
  let running = !number_of_running_provers in
  !observer scheduled (waiting_or_running - running) running;
  true

let interrupt () =
  while not (Queue.is_empty prover_tasks_in_progress) do
    let (_ses,_id,_pr,_proof_script,callback,_started,_call) =
      Queue.pop prover_tasks_in_progress in
    (* TODO: apply some Call_provers.interrupt_call call *)
    callback Interrupted
  done;
  number_of_running_provers := 0;
  while not (Queue.is_empty scheduled_proof_attempts) do
    let (_c,_id,_pr,_limit,_proof_script,callback,_cntexample) = Queue.pop scheduled_proof_attempts in
    callback Interrupted
  done;
  !observer 0 0 0

let run_timeout_handler () =
  if not !timeout_handler_running then
    begin
      timeout_handler_running := true;
      S.timeout ~ms:125 timeout_handler;
    end

let schedule_proof_attempt_r ?proof_script c id pr ~counterexmp ~limit ~callback =
  let panid =
    graft_proof_attempt c.controller_session id pr ~limit
  in
  Queue.add (c,id,pr,limit,proof_script,callback panid,counterexmp)
            scheduled_proof_attempts;
  callback panid Scheduled;
  run_timeout_handler ()

let schedule_proof_attempt ?proof_script c id pr
                           ~counterexmp ~limit ~callback ~notification =
  let callback panid s = callback panid s;
    (match s with
    | Scheduled | Running | Done _ ->
                             update_goal_node notification c.controller_session id
    | _ -> ())
  in
  (* proof_script is specific to interactive manual provers *)
  let session_dir = Session_itp.get_dir c.controller_session in
  let proof_script =
    Opt.map (Sysutil.absolutize_filename session_dir) proof_script
  in
  schedule_proof_attempt_r ?proof_script c id pr ~counterexmp ~limit ~callback

(* TODO to be simplified *)
(* create the path to a file for saving the external proof script *)
let create_file_rel_path c pr pn =
  let session = c.controller_session in
  let driver = snd (Hprover.find c.controller_provers pr) in
  let task = Session_itp.get_task session pn in
  let session_dir = Session_itp.get_dir session in
  let th = get_encapsulating_theory session (APn pn) in
  let th_name = (Session_itp.theory_name th).Ident.id_string in
  let f = get_encapsulating_file session (ATh th) in
  let fn = file_name f in
  let file = Driver.file_of_task driver fn th_name task in
  let file = Filename.concat session_dir file in
  let file = Sysutil.uniquify file in
  let file = Sysutil.relativize_filename session_dir file in
  file

let update_edit_external_proof c pn ?panid pr =
  let session = c.controller_session in
  let driver = snd (Hprover.find c.controller_provers pr) in
  let task = Session_itp.get_task session pn in
  let session_dir = Session_itp.get_dir session in
  let file =
    match panid with
    | None ->
        create_file_rel_path c pr pn
    | Some panid ->
        let pa = get_proof_attempt_node session panid in
        Opt.get pa.proof_script
  in
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
  (* Name table is only used in ITP printing *)
  Driver.print_task ~cntexample:false ?old driver fmt task;
  Opt.iter close_in old;
  close_out ch;
  file

exception Editor_not_found

let schedule_edition c id pr ?file ~callback ~notification =
  Debug.dprintf debug_sched "[Sched] Scheduling an edition@.";
  let config = c.controller_config in
  let session = c.controller_session in
  let prover_conf = Whyconf.get_prover_config config pr in
  let session_dir = Session_itp.get_dir session in
  (* Notification node *)
  let callback panid s = callback panid s;
    match s with
    | Scheduled | Running | Done _ -> update_goal_node notification c.controller_session id
    | _ -> ()
  in

  let limit = Call_provers.empty_limit in
  (* Make sure editor exists. Fails otherwise *)
  let editor =
    match prover_conf.Whyconf.editor with
    | "" -> raise Editor_not_found
    | s ->
        try
          let ed = Whyconf.editor_by_id config s in
          String.concat " "(ed.Whyconf.editor_command ::
                            ed.Whyconf.editor_options)
        with Not_found -> raise Editor_not_found
  in
  let proof_attempts_id = get_proof_attempt_ids session id in
  let panid =
    try Some (Hprover.find proof_attempts_id pr) with
    | _ -> None
  in
  (* make sure to actually create the file and the proof attempt *)
  let panid, file =
    match panid, file with
    | None, None ->
        let file = update_edit_external_proof c id pr in
        let filename = Sysutil.relativize_filename session_dir file in
        let panid = graft_proof_attempt c.controller_session id pr ~file:filename ~limit in
        panid, file
    | None, Some file ->
        let panid = graft_proof_attempt c.controller_session id pr ~file ~limit in
        let file = update_edit_external_proof c id ~panid pr in
        panid, file
    | Some panid, _ ->
        let file = update_edit_external_proof c id ~panid pr in
        panid, file
  in

  Debug.dprintf debug_sched "[Editing] goal %s with command '%s' on file %s@."
    (Session_itp.get_proof_name session id).Ident.id_string
    editor file;
  let call = Call_provers.call_editor ~command:editor file in
  callback panid Running;
  let file = Sysutil.relativize_filename session_dir file in
  Queue.add (c.controller_session,id,pr,Some file,callback panid,false,call)
    prover_tasks_in_progress;
  run_timeout_handler ()


let schedule_transformation_r c id name args ~callback =
  let apply_trans () =
    let task = get_task c.controller_session id in
    let table = match get_table c.controller_session id with
    | None -> raise (Task.Bad_name_table "Controller_itp.schedule_transformation_r")
    | Some table -> table in
    begin
      try
        let subtasks =
          Trans.apply_transform_args name c.controller_env args table task in
        (* if result is same as input task, consider it as a failure *)
        begin
          match subtasks with
          | [t'] when Task.task_equal t' task ->
             callback (TSfailed (id, Noprogress))
          | _ ->
             let tid = graft_transf c.controller_session id name args subtasks in
             callback (TSdone tid)
        end
      with e when not (Debug.test_flag Debug.stack_trace) ->
        (* Format.eprintf
          "@[Exception raised in Trans.apply_transform %s:@ %a@.@]"
          name Exn_printer.exn_printer e; TODO *)
        callback (TSfailed (id, e))
    end;
    false
  in
  S.idle ~prio:0 apply_trans;
  callback TSscheduled

let schedule_transformation c id name args ~callback ~notification =
  let callback s = callback s; (match s with
      | TSdone tid -> update_trans_node notification c.controller_session tid
      | TSfailed _e -> ()
      | _ -> ()) in
  schedule_transformation_r c id name args ~callback

open Strategy

let run_strategy_on_goal
    c id strat ~counterexmp ~callback_pa ~callback_tr ~callback ~notification =
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
           | Interrupted | InternalFailure _ ->
              callback STShalt
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
         schedule_proof_attempt c g p ~counterexmp ~limit ~callback ~notification
      | Itransform(trname,pcsuccess) ->
         let callback ntr =
           callback_tr ntr;
           match ntr with
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
  schedule_transformation c pn name args ~callback ~notification

let clean_session c ~removed =
  (* clean should not change proved status *)
  let notification _ = assert false in
  let s = c.controller_session in
  (* This function is applied on leafs first for the case of removes *)
  Session_itp.fold_all_session s
    (fun () any ->
      (match any with
      | APa pa ->
        let pa = Session_itp.get_proof_attempt_node s pa in
        if pn_proved s pa.parent then
          (match pa.Session_itp.proof_state with
          | None -> ()
          | Some pr ->
           if pa.Session_itp.proof_obsolete ||
                Call_provers.(pr.pr_answer <> Valid)
           then
             remove_subtree ~notification ~removed s any)
      | ATn tn ->
        let pn = get_trans_parent s tn in
        if pn_proved s pn && not (tn_proved s tn) then
          remove_subtree s ~notification ~removed (ATn tn)
      | _ -> ())) ()

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
  fold_all_any s
    (fun () any -> match any with
    | APa n -> mark_as_obsolete_pa n
    | _ -> ()) () any

exception BadCopyPaste

(* Reproduce the transformation made on node on an other one *)
let rec copy_paste ~notification ~callback_pa ~callback_tr c from_any to_any =
  let s = c.controller_session in
  if (not (is_below s from_any to_any) &&
      not (is_below s to_any from_any)) then
    match from_any, to_any with
    | AFile _, AFile _ ->
        raise BadCopyPaste
    | ATh _from_th, ATh _to_th ->
        raise BadCopyPaste
    | APn from_pn, APn to_pn ->
      let from_pa_list = get_proof_attempts s from_pn in
      List.iter (fun x -> schedule_pa_with_same_arguments c x to_pn ~counterexmp:false
          ~callback:callback_pa ~notification) from_pa_list;
      let from_tr_list = get_transformations s from_pn in
      let callback x st = callback_tr st;
        match st with
        | TSdone tid ->
          copy_paste c (ATn x) (ATn tid) ~notification ~callback_pa ~callback_tr
        | _ -> ()
      in
      List.iter (fun x -> schedule_tr_with_same_arguments c x to_pn
          ~callback:(callback x) ~notification) from_tr_list
    | ATn from_tn, ATn to_tn ->
        let from_tn_list = get_sub_tasks s from_tn in
        let to_tn_list = get_sub_tasks s to_tn in
        if (List.length from_tn_list = List.length to_tn_list) then
          List.iter2 (fun x y -> copy_paste c (APn x) (APn y)
              ~notification ~callback_pa ~callback_tr) from_tn_list to_tn_list
    | _ -> raise BadCopyPaste


let copy_detached ~copy c from_any =
  match from_any with
  | APn from_pn ->
    begin
      let pn_id = copy_proof_node_as_detached c.controller_session from_pn in
      let parent = get_any_parent c.controller_session from_any in
      match parent with
      | None -> raise (BadCopyDetached "copy_detached no parent")
      | Some parent ->
          copy ~parent (APn pn_id);
          copy_structure
            ~notification:copy c.controller_session (APn from_pn) (APn pn_id)
    end
  (* Only goal can be detached *)
  | _ -> raise (BadCopyDetached "copy_detached. Can only copy goal")


let replay_proof_attempt ?proof_script c pr limit (parid: proofNodeID) id ~callback ~notification =
  (* The replay can be done on a different machine so we need
     to check more things before giving the attempt to the scheduler *)
  if not (Hprover.mem c.controller_provers pr) then
    callback id (Uninstalled pr)
  else
    schedule_proof_attempt ?proof_script c parid pr ~counterexmp:false ~limit ~callback ~notification

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

let replay ?(obsolete_only=true) ?(use_steps=false)
           c ~callback ~notification ~final_callback =

  let craft_report count s r id pr limits pa =
    match s with
    | Scheduled | Running -> ()
    | Unedited | JustEdited -> assert false
    | Interrupted ->
       decr count;
       r := (id, pr, limits, Replay_interrupted ) :: !r
    | Done new_r ->
       decr count;
        (match pa.Session_itp.proof_state with
        | None -> (r := (id, pr, limits, No_former_result new_r) :: !r)
        | Some old_r -> r := (id, pr, limits, Result (new_r, old_r)) :: !r)
    | InternalFailure e ->
       decr count;
        r := (id, pr, limits, CallFailed (e)) :: !r
    | Uninstalled _ ->
       decr count;
       r := (id, pr, limits, Prover_not_installed) :: !r;
  in

  (* === replay === *)
  let session = c.controller_session in
  let count = ref 0 in
  let report = ref [] in

  (* TODO count the number of node in a more efficient way *)
  (* Counting the number of proof_attempt to print report only once *)
  Session_itp.session_iter_proof_attempt
    (fun _ pa -> if pa.proof_obsolete || not obsolete_only then incr count) session;

  (* Replaying function *)
  let replay_pa id pa =
    if pa.proof_obsolete || not obsolete_only then
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
        let proof_script = pa.proof_script in
        replay_proof_attempt ?proof_script c pr limit parid id
                             ~callback:(fun id s ->
                                        craft_report count s report parid pr limit pa;
                                        callback id s;
                                        if !count = 0 then final_callback !report)
                             ~notification
      end in

  (* Calling replay on all the proof_attempts of the session *)
  Session_itp.session_iter_proof_attempt replay_pa session

end
