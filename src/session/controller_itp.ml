open Format
open Session_itp

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


open Ident

type proof_state = {
    th_state: bool Hid.t;
    tn_state: bool Htn.t;
    pn_state : bool Hpn.t;
  }

let init_proof_state () =
  {th_state = Hid.create 7;
   tn_state = Htn.create 42;
   pn_state = Hpn.create 42}

type controller =
  { mutable controller_session: Session_itp.session;
    proof_state: proof_state;
    controller_env: Env.env;
    controller_provers:
      (Whyconf.config_prover * Driver.driver) Whyconf.Hprover.t;
  }

let clear_proof_state c =
  Hid.clear c.proof_state.th_state;
  Htn.clear c.proof_state.tn_state;
  Hpn.clear c.proof_state.pn_state

let create_controller env =
  {
    controller_session = Session_itp.dummy_session;
    proof_state = init_proof_state ();
    controller_env = env;
    controller_provers = Whyconf.Hprover.create 7;
  }

let init_controller s c =
  clear_proof_state (c);
  c.controller_session <- s

let tn_proved c tid = Htn.find_def c.proof_state.tn_state false tid
let pn_proved c pid = Hpn.find_def c.proof_state.pn_state false pid
let th_proved c th  =
  if (theory_goals th = []) then
    Hid.find_def c.proof_state.th_state true (theory_name th)
  else
    Hid.find_def c.proof_state.th_state false (theory_name th)
let file_proved c f =
  if f.file_theories = [] then
    true
  else
    List.for_all (fun th -> th_proved c th) f.file_theories

let any_proved cont any : bool =
  match any with
  | AFile file -> file_proved cont file
  | ATh th -> th_proved cont th
  | ATn tn -> tn_proved cont tn
  | APn pn -> pn_proved cont pn
  | APa pa ->
      begin
        let pa = get_proof_attempt_node cont.controller_session pa in
        match pa.Session_itp.proof_state with
        | None -> false
        | Some pa ->
          begin
            match pa.Call_provers.pr_answer with
            | Call_provers.Valid -> true
            | _ -> false
          end
      end

let remove_any_proof_state cont any : unit =
  match any with
  | AFile _file -> ()
  | ATh th     -> Hid.remove cont.proof_state.th_state (theory_name th)
  | APn pn     -> Hpn.remove cont.proof_state.pn_state pn
  | ATn tn     -> Htn.remove cont.proof_state.tn_state tn
  | APa _pa     -> ()

(* Update the result of the theory according to its children *)
let update_theory_proof_state notification ps th =
  let goals = theory_goals th in
  if Hid.mem ps.th_state (theory_name th) then
  begin
    let old_state = Hid.find_def ps.th_state false (theory_name th) in
    let new_state =
      List.for_all (fun id -> Hpn.find_def ps.pn_state false id) goals in
    if new_state != old_state then
      begin
        Hid.replace ps.th_state (theory_name th) new_state;
        notification (ATh th) new_state
      end
  end
  else
  begin
    let new_state =
      List.for_all (fun id -> Hpn.find_def ps.pn_state false id) goals in
    Hid.replace ps.th_state (theory_name th) new_state;
    notification (ATh th) new_state
  end

let rec propagate_proof notification c (id: Session_itp.proofNodeID) =
  let tr_list = get_transformations c.controller_session id in
  let new_state = List.exists (fun id -> tn_proved c id) tr_list in
  if new_state != pn_proved c id then
    begin
      Hpn.replace c.proof_state.pn_state id new_state;
      notification (APn id) new_state;
      update_proof notification c id
    end

and propagate_trans notification c (tid: Session_itp.transID) =
  let proof_list = get_sub_tasks c.controller_session tid in
  let cur_state = tn_proved c tid in
  let new_state = List.for_all (fun id -> pn_proved c id) proof_list in
  if cur_state != new_state then
    begin
      Htn.replace c.proof_state.tn_state tid new_state;
      notification (ATn tid) new_state;
      propagate_proof notification c (get_trans_parent c.controller_session tid)
    end

and update_proof notification c id =
  match get_proof_parent c.controller_session id with
  | Theory th -> update_theory_proof_state notification c.proof_state th
  | Trans tid -> propagate_trans notification c tid

(* [update_proof_node c id b] Update the whole proof_state
   of c according to the result (id, b) *)
let update_proof_node notification c id b =
  if Hpn.mem c.proof_state.pn_state id then
  begin
    let b' = Hpn.find_def c.proof_state.pn_state false id in
    if b != b' then
    begin
      Hpn.replace c.proof_state.pn_state id b;
      notification (APn id) b;
      update_proof notification c id
    end
  end
  else
  begin
    Hpn.replace c.proof_state.pn_state id b;
    notification (APn id) b;
    update_proof notification c id
  end

(* [update_trans_node c id b] Update the proof_state of c to take the result of
   (id,b). Then propagates it to its parents *)
let update_trans_node notification c id b =
  if Htn.mem c.proof_state.tn_state id then
  begin
    let b' = Htn.find_def c.proof_state.tn_state false id in
    if b != b' then
    begin
      Htn.replace c.proof_state.tn_state id b;
      notification (ATn id) b
    end
  end
  else
    (Htn.replace c.proof_state.tn_state id b;
     notification (ATn id) b);
  propagate_proof notification c (get_trans_parent c.controller_session id)

(** TODO make the whole reloading of proof_state more efficient and natural *)

(* Note that f has side effect on the elements of l. We want this effect to
   happen. That's why we cannot use List.for_all (respectively List.exists)
   directly (List.for_all stops on first element that evaluates to false) *)
let for_all_se f l =
  List.for_all (fun b -> b) (List.map f l)

let exists_se f l =
  List.exists (fun b -> b) (List.map f l)

(* init proof state after reload *)
let rec reload_goal_proof_state c g =
  let ses = c.controller_session in
  let tr_list = get_transformations ses g in
  let pa_list = get_proof_attempts ses g in
  let proved = exists_se (reload_trans_proof_state c) tr_list in
  let proved = exists_se reload_pa_proof_state pa_list || proved in
  Hpn.replace c.proof_state.pn_state g proved;
  proved

and reload_trans_proof_state c tr =
  let proof_list = get_sub_tasks c.controller_session tr in
  let proved = for_all_se (reload_goal_proof_state c) proof_list in
  Htn.replace c.proof_state.tn_state tr proved;
  proved

and reload_pa_proof_state pa =
  match pa.proof_obsolete, pa.Session_itp.proof_state with
  | false, Some pr when pr.Call_provers.pr_answer = Call_provers.Valid -> true
  | _ -> false

(* to be called after reload *)
let reload_theory_proof_state c th =
  let ps = c.proof_state in
  let goals = theory_goals th in
  let proved = for_all_se (reload_goal_proof_state c) goals in
  Hid.replace ps.th_state (theory_name th) proved

(* to be called after reload *)
let reload_file_proof_state c f =
  List.iter (reload_theory_proof_state c) f.file_theories

(* to be called after reload *)
let reload_session_proof_state c =
  Stdlib.Hstr.iter
    (fun _ f -> reload_file_proof_state c f)
    (get_files c.controller_session)

(* Get children of any without proofattempts *)
let get_undetached_children_no_pa s any : any list =
  match any with
  | AFile f -> List.map (fun th -> ATh th) f.file_theories
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
       f.file_name,
       List.fold_right
          (fun th -> n (Theory th))
          f.file_detached_theories
          (List.fold_right (fun th -> n (Theory th)) f.file_theories [])
    | Theory th ->
       let id = theory_name th in
       let name = id.Ident.id_string in
       let name = if th_proved x.tcont th then name^"!" else name^"?" in
       name,
       List.fold_right
         (fun g -> n (Goal g))
         (theory_goals th)
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
  let format = file.file_format in
  let old_theories = file.file_theories in
  let file_name = Filename.concat (get_dir old_ses) file.file_name in
  let new_theories =
    try
      read_file c.controller_env file_name ?format
    with e -> (* TODO: filter only syntax error and typing errors *)
      raise e
  in
  merge_file_section
    c.controller_session ~use_shapes ~old_ses ~old_theories
    ~env:c.controller_env file_name new_theories format;
  reload_session_proof_state c

let reload_files (c : controller) ~use_shapes =
  let old_ses = c.controller_session in
  c.controller_session <-
    empty_session ~shape_version:(get_shape_version old_ses) (get_dir old_ses);
  try
    Stdlib.Hstr.iter
      (fun f -> merge_file old_ses c ~use_shapes f)
      (get_files old_ses)
  with e ->
    c.controller_session <- old_ses;
    raise e

let add_file c ?format fname =
  let theories = read_file c.controller_env ?format fname in
  add_file_section ~use_shapes:false c.controller_session fname theories format

(* Update the proof_state according to new false state and then remove
   the subtree *)
let remove_subtree c (n: any) ~removed ~node_change =
  let removed = (fun x -> removed x; remove_any_proof_state c x) in
  let parent = get_any_parent c.controller_session n in
  match n with
  | ATn _ | APa _ ->
    Session_itp.remove_subtree c.controller_session n ~notification:removed;
    (match parent with
      | Some (APn parent) ->
        (* If proof_state of the parent is actually changed update the branch
           otherwise do nothing *)
        let tr_list = get_transformations c.controller_session parent in
        let pa_list = get_proof_attempts c.controller_session parent in
        let proved = List.exists (tn_proved c) tr_list in
        let proved = List.exists reload_pa_proof_state pa_list || proved in
        if proved then
          ()
        else
          update_proof_node node_change c parent false
    | _ -> assert false)
  | _ -> ()

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
    Whyconf.get_complete_command
      config_pr
      ~with_steps:Call_provers.(limit.limit_steps <> empty_limit.limit_steps) in
  let task = Session_itp.get_task c.controller_session id in
  let tables = Session_itp.get_tables c.controller_session id in
  let call =
    Driver.prove_task ?old:None ~cntexample:true ~inplace:false ~command
                      ~limit ?name_table:tables driver task
  in
  let pa = (c.controller_session,id,pr,callback,false,call) in
  Queue.push pa prover_tasks_in_progress

let timeout_handler () =
  (* examine all the prover tasks in progress *)
  let q = Queue.create () in
  while not (Queue.is_empty prover_tasks_in_progress) do
    let (ses,id,pr,callback,started,call) as c =
      Queue.pop prover_tasks_in_progress in
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
  begin
    try
      for _i = Queue.length prover_tasks_in_progress
          to 3 * !max_number_of_running_provers do
        let (c,id,pr,limit,callback) = Queue.pop scheduled_proof_attempts in
        try
          build_prover_call c id pr limit callback
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
    let (_ses,_id,_pr,callback,_started,_call) =
      Queue.pop prover_tasks_in_progress in
    (* TODO: apply some Call_provers.interrupt_call call *)
    callback Interrupted
  done;
  number_of_running_provers := 0;
  while not (Queue.is_empty scheduled_proof_attempts) do
    let (_c,_id,_pr,_limit,callback) = Queue.pop scheduled_proof_attempts in
    callback Interrupted
  done;
  !observer 0 0 0

let run_timeout_handler () =
  if not !timeout_handler_running then
    begin
      timeout_handler_running := true;
      S.timeout ~ms:125 timeout_handler;
    end

let schedule_proof_attempt_r c id pr ~limit ~callback =
  let panid =
    graft_proof_attempt c.controller_session id pr
      ~timelimit:limit.Call_provers.limit_time
  in
  Queue.add (c,id,pr,limit,callback panid) scheduled_proof_attempts;
  callback panid Scheduled;
  run_timeout_handler ()

let schedule_proof_attempt c id pr ~limit ~callback ~notification =
  let callback panid s = callback panid s;
    (match s with
    | Done pr -> update_proof_node notification c id
          (pr.Call_provers.pr_answer == Call_provers.Valid)
    | Interrupted | InternalFailure _ ->
        update_proof_node notification c id false
    | _ -> ())
  in
  schedule_proof_attempt_r c id pr ~limit:limit ~callback

let schedule_transformation_r c id name args ~callback =
  let apply_trans () =
    let task = get_task c.controller_session id in
    let tables = match get_tables c.controller_session id with
    | None -> raise (Task.Bad_name_table "schedule_transformation")
    | Some tables -> tables in
    begin
      try
        let subtasks =
          Trans.apply_transform_args name c.controller_env args tables task in
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
      | TSdone tid ->
        let has_subtasks =
          match get_sub_tasks c.controller_session tid with
          | [] -> true
          | _ -> false
        in
        update_trans_node notification c tid has_subtasks
      | TSfailed _e -> ()
      | _ -> ()) in
  schedule_transformation_r c id name args ~callback

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
         schedule_proof_attempt c g p ~limit ~callback ~notification
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

let clean_session c ~remove ~node_change =
  let is_valid (pa: proof_attempt_node) : bool =
    match pa.Session_itp.proof_state with
    | None -> false
    | Some pr ->
      begin
        match pr.Call_provers.pr_answer with
        | Call_provers.Valid -> true
        | _ -> false
      end
  in
  let s = c.controller_session in
  Session_itp.session_iter_proof_attempt
    (fun _ pa ->
      let pnid = pa.parent in
      Hprover.iter (fun _ paid ->
        if (not (is_valid (get_proof_attempt_node s paid))) then
          remove_subtree c ~removed:remove ~node_change (APa paid))
        (get_proof_attempt_ids s pnid)) s

let mark_as_obsolete ~node_change ~node_obsolete c any =
  let s = c.controller_session in
  match any with
  | APa n ->
    let parent = get_proof_attempt_parent s n in
    Session_itp.mark_obsolete s n;
    node_obsolete any true;
    let b = reload_goal_proof_state c parent in
    node_change (APn parent) b;
    update_proof_node node_change c parent b
  | _ -> ()


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
      List.iter (fun x -> schedule_pa_with_same_arguments c x to_pn
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
      | None -> raise BadCopyDetached
      | Some parent ->
          copy ~parent (APn pn_id);
          copy_structure
            ~notification:copy c.controller_session (APn from_pn) (APn pn_id)
    end
  | _ -> raise BadCopyDetached (* Only goal can be detached *)


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
let replay_print fmt (lr: (proofNodeID * Whyconf.prover * Call_provers.resource_limit * report) list) =
  let pp_elem fmt (id, pr, rl, report) =
    fprintf fmt "ProofNodeID: %d, Prover: %a, Timelimit?: %d, Result: %a@."
      (Obj.magic id) Whyconf.print_prover pr
      rl.Call_provers.limit_time print_report report
  in
  Format.fprintf fmt "%a@." (Pp.print_list Pp.newline pp_elem) lr

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
  let replay_pa pa =
    let id = pa.parent in
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
        counting s count;
        craft_report s report id pr limit pa;
        update_node pa s;
        update_uninstalled c remove_obsolete id s pr;
        if !count = 0 then callback !report) in

  (* Calling replay on all the proof_attempts of the session *)
  Session_itp.session_iter_proof_attempt
    (fun _ pa -> replay_pa pa) session

end
