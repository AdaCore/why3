(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Session

let debug = Debug.register_info_flag "scheduler"
  ~desc:"Print@ debugging@ messages@ about@ scheduling@ of@ prover@ calls@ \
         and@ transformation@ applications."

let usleep t = ignore (Unix.select [] [] [] t)
let default_delay_ms = 100 (* 0.1 seconds *)

module Todo = struct
  type ('a,'b) todo =
      {mutable todo : int;
       mutable report : 'a;
       push_report : 'a -> 'b -> 'a;
       callback : 'a -> unit}

  let create init push callback =
    {todo = 0;  report = init; push_report = push; callback = callback}

  let stop todo =
    todo.todo <- todo.todo - 1;
    if todo.todo=0 then todo.callback todo.report

  let _done todo v =
    todo.report <- todo.push_report todo.report v;
    stop todo

  let start todo =
    todo.todo <- todo.todo + 1

(** dead code
  let print todo =
    dprintf debug "[Sched] todo: %i@." todo.todo
*)
end

(***************************)
(*     main functor        *)
(***************************)

module type OBSERVER = sig
  type key
  val create: ?parent:key -> unit -> key
  val remove: key -> unit
  val reset: unit -> unit

  val timeout: ms:int -> (unit -> bool) -> unit
  val idle: (unit -> bool) -> unit

  val notify_timer_state : int -> int -> int -> unit

  val init : key -> key any -> unit

  val notify : key any -> unit

  val uninstalled_prover :
    key env_session -> Whyconf.prover -> Whyconf.prover_upgrade_policy

end



module Make(O : OBSERVER) = struct

(*************************)
(*         Scheduler     *)
(*************************)

type action =
  | Action_proof_attempt of
      bool * Call_provers.resource_limit * string option * bool * string *
      Driver.driver * (proof_attempt_status -> unit) * Task.task
  | Action_delayed of (unit -> unit)

type timeout_action =
  | Check_prover of
      (proof_attempt_status -> unit) * bool * Call_provers.prover_call
  | Any_timeout of (unit -> bool)

type t =
    { (* Actions that wait some idle time *)
      actions_queue : action Queue.t;
      (** Quota of action slot *)
      mutable maximum_running_proofs : int;
      (** Running actions which take one action slot *)
      mutable running_proofs : int;
      (** proof attempt that wait some available action slot *)
      proof_attempts_queue : timeout_action Queue.t;
      (** timeout handler state *)
      mutable timeout_handler_activated : bool;
      mutable timeout_handler_running : bool;
      (** idle handler state *)
      mutable idle_handler_activated : bool;
    }

let set_maximum_running_proofs max sched =
  Prove_client.set_max_running_provers max;
  (* TODO dequeue actions if maximum_running_proofs increase *)
  sched.maximum_running_proofs <- max

let init max =
  Debug.dprintf debug "[Sched] init scheduler max=%i@." max;
  Prove_client.set_max_running_provers max;
  { actions_queue = Queue.create ();
    maximum_running_proofs = max;
    running_proofs = 0;
    proof_attempts_queue = Queue.create ();
    timeout_handler_activated = false;
    timeout_handler_running = false;
    idle_handler_activated = false
  }

let notify_timer_state t continue =
  O.notify_timer_state
    (Queue.length t.actions_queue)
    (Queue.length t.proof_attempts_queue)
    t.running_proofs;
  continue

(* timeout handler *)

let timeout_handler t =
  Debug.dprintf debug "[Sched] Timeout handler called@.";
  assert (not t.timeout_handler_running);
  t.timeout_handler_running <- true;
  (* Check if some action ended *)
  let q = Queue.create () in
  while not (Queue.is_empty t.proof_attempts_queue) do
    match Queue.pop t.proof_attempts_queue with
    | Check_prover (callback,started,call) as c ->
        begin match Call_provers.query_call call with
          | Call_provers.NoUpdates ->
              Queue.add c q
          | Call_provers.ProverStarted when started ->
              Queue.add c q (* should not happen *)
          | Call_provers.ProverStarted ->
              callback Running;
              t.running_proofs <- t.running_proofs + 1;
              Debug.dprintf debug "[Sched] proof attempts started@.";
              Queue.add (Check_prover (callback,true,call)) q
          | Call_provers.ProverFinished res ->
              if started then t.running_proofs <- t.running_proofs - 1;
              callback (Done res)
        end
    | Any_timeout callback as c ->
        if callback () then Queue.add c q
  done;
  Queue.transfer q t.proof_attempts_queue;
  let continue =
    if Queue.is_empty t.proof_attempts_queue then begin
          Debug.dprintf debug "[Sched] Timeout handler stopped@.";
          false
    end else true
  in
  t.timeout_handler_activated <- continue;
  t.timeout_handler_running <- false;
  notify_timer_state t continue

let run_timeout_handler t =
  if t.timeout_handler_activated then () else
    begin
      t.timeout_handler_activated <- true;
      Debug.dprintf debug "[Sched] Timeout handler started@.";
      O.timeout ~ms:default_delay_ms (fun () -> timeout_handler t)
    end

let schedule_any_timeout t callback =
  Debug.dprintf debug "[Sched] schedule a new timeout@.";
  Queue.add (Any_timeout callback) t.proof_attempts_queue;
  run_timeout_handler t

(* idle handler *)

let idle_handler t =
  try
    if Queue.length t.proof_attempts_queue < 3 * t.maximum_running_proofs then
      begin match Queue.pop t.actions_queue with
        | Action_proof_attempt(cntexample,limit,
              old,inplace,command,driver,callback,goal) ->
            begin
              try
                let call =
                  Driver.prove_task ?old ~cntexample ~inplace ~command
                    ~limit driver goal
                in
                let pa = Check_prover (callback,false,call) in
                Queue.push pa t.proof_attempts_queue;
                run_timeout_handler t
              with e when not (Debug.test_flag Debug.stack_trace) ->
                Format.eprintf
                  "@[Exception raise in Session.idle_handler:@ %a@.@]"
                  Exn_printer.exn_printer e;
                callback (InternalFailure e)
            end
        | Action_delayed callback -> callback ()
      end
    else
      usleep (float default_delay_ms /. 1000.);
    notify_timer_state t true
  with
    | Queue.Empty ->
      t.idle_handler_activated <- false;
      Debug.dprintf debug "[Sched] idle_handler stopped@.";
      notify_timer_state t false
    | e when not (Debug.test_flag Debug.stack_trace) ->
      Format.eprintf "@[Exception raise in Session.idle_handler:@ %a@.@]"
        Exn_printer.exn_printer e;
      eprintf "Session.idle_handler stopped@.";
      notify_timer_state t false


let run_idle_handler t =
  if t.idle_handler_activated then () else
    begin
      t.idle_handler_activated <- true;
      Debug.dprintf debug "[Sched] idle_handler started@.";
      O.idle (fun () -> idle_handler t)
    end

(* main scheduling functions *)

let cancel_scheduled_proofs t =
  let new_queue = Queue.create () in
  try
    while true do
      match Queue.pop t.actions_queue with
        | Action_proof_attempt(_cntexample,_limit,
              _old,_inplace,_command,_driver,callback,_goal) ->
            callback Interrupted
        | Action_delayed _ as a->
            Queue.push a new_queue
    done
  with Queue.Empty ->
    Queue.transfer new_queue t.actions_queue;
    (* NOTE: we cannot cancel proof attempts sent to the server *)
    (*
    try
      while true do
        let (callback,_,_) = Queue.pop t.proof_attempts_queue in
        callback Interrupted
      done
    with
      | Queue.Empty ->
    *)
    ignore (notify_timer_state t false)


let schedule_proof_attempt ~cntexample ~limit ?old ~inplace
    ~command ~driver ~callback t goal =
  Debug.dprintf debug "[Sched] Scheduling a new proof attempt (goal: %a)@."
    (fun fmt g -> Format.pp_print_string fmt
      (Task.task_goal g).Decl.pr_name.Ident.id_string) goal;
  callback Scheduled;
  Queue.push
    (Action_proof_attempt(cntexample,limit,
      old,inplace,command,driver,callback,goal))
    t.actions_queue;
  run_idle_handler t

let schedule_edition t command filename callback =
  Debug.dprintf debug "[Sched] Scheduling an edition@.";
  let call = Call_provers.call_editor ~command filename in
  callback Running;
  Queue.add (Check_prover(callback,false,call)) t.proof_attempts_queue;
  run_timeout_handler t

let schedule_delayed_action t callback =
  Debug.dprintf debug "[Sched] Scheduling a delayed action@.";
  Queue.push (Action_delayed callback) t.actions_queue;
  run_idle_handler t

(**************************)
(*  session functions     *)
(**************************)

let notify = O.notify

let rec init_any any = O.init (key_any any) any; iter init_any any

let init_session session = session_iter init_any session

let update_session ~allow_obsolete ~release ~use_shapes
    old_session env whyconf  =
  O.reset ();
  let ctxt = Session.mk_update_context
      ~allow_obsolete_goals:allow_obsolete
      ~release_tasks:release
      ~use_shapes_for_pairing_sub_goals:use_shapes
      O.create
  in
  let (env_session,_,_) as res =
    update_session ~ctxt old_session env whyconf
  in
  Debug.dprintf debug "Init_session@\n";
  init_session env_session.session;
  res

let add_file env_session ?format f =
  let mfile = add_file ~keygen:O.create env_session ?format f in
  let any_file = (File mfile) in
  init_any any_file;
  O.notify any_file;
  mfile

(*****************************************************)
(* method: run a given prover on each unproved goals *)
(*****************************************************)

let find_prover eS a =
  match load_prover eS a.proof_prover with
    | Some p -> Some (a.proof_prover, p,a)
    | None ->
        match O.uninstalled_prover eS a.proof_prover with
          | Whyconf.CPU_keep -> None
          | Whyconf.CPU_upgrade new_p ->
            (* does a proof using new_p already exists ? *)
            let g = a.proof_parent in
            begin
              try
                let _ = PHprover.find (goal_external_proofs g) new_p in
                (* yes, then we do nothing *)
                None
              with Not_found ->
                (* we modify the prover in-place *)
                Session.change_prover a new_p;
                match load_prover eS new_p with
                  | Some p -> Some (new_p,p,a)
                  | None ->
                    (* should never happen because at loading, config
                       ignores uninstalled prover targets.
                       Nevertheless, we can safely return None.
                    *)
                    None
            end
          | Whyconf.CPU_duplicate new_p ->
            (* does a proof using new_p already exists ? *)
            let g = a.proof_parent in
            begin
              try
                let _ = PHprover.find (goal_external_proofs g) new_p in
                (* yes, then we do nothing *)
                None
              with Not_found ->
                (* we duplicate the proof_attempt *)
                let new_a = copy_external_proof
                  ~notify ~keygen:O.create ~prover:new_p ~env_session:eS a
                in
                O.init new_a.proof_key (Proof_attempt new_a);
                match load_prover eS new_p with
                  | Some p -> Some (new_p,p,new_a)
                  | None ->
                    (* should never happen because at loading, config
                       ignores uninstalled prover targets.
                       Nevertheless, we can safely return None.
                    *)
                    None
            end


(* to avoid corner cases when prover results are obtained very closely
   to the time or mem limits, we adapt these limits when we replay a
   proof *)
let adapt_limits ~interactive ~use_steps a =
  let timelimit = (a.proof_limit.Call_provers.limit_time) in
  let memlimit = (a.proof_limit.Call_provers.limit_mem) in
  match a.proof_state with
  | Done { Call_provers.pr_answer = r;
           Call_provers.pr_time = t;
           Call_provers.pr_steps = s } ->
    (* increased time limit is 1 + twice the previous running time,
       but enforced to remain inside the interval [l,2l] where l is
       the previous time limit *)
    let t = truncate (1.0 +. 2.0 *. t) in
    let increased_time = if interactive then t
      else max timelimit (min t (2 * timelimit)) in
    (* increased mem limit is just 1.5 times the previous mem limit *)
    let increased_mem = if interactive then 0 else 3 * memlimit / 2 in
    begin
      match r with
      | Call_provers.OutOfMemory -> increased_time, memlimit, 0
      | Call_provers.Timeout -> timelimit, increased_mem, 0
      | Call_provers.Valid ->
        let steplimit =
          if use_steps && not a.proof_obsolete then s else 0
        in
        increased_time, increased_mem, steplimit
      | Call_provers.Unknown _
      | Call_provers.StepLimitExceeded
      | Call_provers.Invalid -> increased_time, increased_mem, 0
      | Call_provers.Failure _
      | Call_provers.HighFailure ->
        (* correct ? failures are supposed to appear quickly anyway... *)
        timelimit, memlimit, 0
    end
  | _ when interactive -> 0, 0, 0
  | _ -> timelimit, memlimit, 0

let adapt_limits ~interactive ~use_steps a =
  let t, m, s = adapt_limits ~interactive ~use_steps a in
  { Call_provers.limit_time = t; limit_mem = m; limit_steps = s }

type run_external_status =
| Starting
| MissingProver
| MissingFile of string
| StatusChange of proof_attempt_status

exception NoFile of string

(* do not modify the proof duration stored in proof sessions if it
   changed by less than 10% or 0.1s, so as to avoid diff noise in
   session files *)

let group_answer a =
  match a with
  | Call_provers.OutOfMemory
  | Call_provers.Unknown _
  | Call_provers.Timeout -> Call_provers.Timeout
  | _ -> a

let fuzzy_proof_time nres ores =
  match ores, nres with
  | Done { Call_provers.pr_answer= ansold; Call_provers.pr_time = told },
    Done ({ Call_provers.pr_answer= ansnew; Call_provers.pr_time = tnew } as res')
  when group_answer ansold = group_answer ansnew && tnew >= told *. 0.9 -. 0.1 && tnew <= told *. 1.1 +. 0.1 ->
    Done { res' with Call_provers.pr_time = told }
  | _, _ -> nres

(** run_external_proof_v3 doesn't modify existing proof attempt, it can just
    create new one by find_prover *)
let run_external_proof_v3 ~use_steps eS eT a ?(cntexample=false) callback =
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

(** run_external_proof_v2 modify the session according to the current state *)
let run_external_proof_v2 ~use_steps eS eT a ~cntexample callback =
  let previous_res = ref (a.proof_state,a.proof_obsolete) in
  let callback a ap limits previous state =
    begin match state with
    | Starting -> previous_res := (a.proof_state,a.proof_obsolete)
    | MissingFile _ ->
      set_proof_state ~notify ~obsolete:false ~archived:false
        Unedited a
    | StatusChange result ->
      begin match result with
      | Interrupted ->
        let previous_result,obsolete = !previous_res in
        set_proof_state ~notify ~obsolete
          ~archived:false previous_result a
      | _ ->
        set_proof_state ~notify ~obsolete:false
          ~archived:false result a
      end
    | _ -> ()
    end;
    callback a ap limits previous state
  in
  run_external_proof_v3 ~use_steps eS eT a ~cntexample callback

let running = function
  | Scheduled | Running -> true
  | Unedited | JustEdited | Interrupted
  | Done _ | InternalFailure _ -> false

let run_external_proof_v2 ~use_steps eS eT a ?(cntexample=false) callback =
  (* Perhaps the test a.proof_archived should be done somewhere else *)
  if a.proof_archived || running a.proof_state then () else
  run_external_proof_v2 ~use_steps eS eT a ~cntexample callback

let run_external_proof eS eT ?(cntexample=false) ?callback a =
  let callback =
    match callback with
    | None -> fun _ _ _ _ _ -> ()
    | Some c -> fun a _ _ _ s ->
      match s with
      | Starting -> ()
      | MissingProver -> c a Interrupted
      | MissingFile _ -> c a a.proof_state
      | StatusChange s -> c a s
  in
  run_external_proof_v2 ~use_steps:false eS eT a ~cntexample callback

let prover_on_goal eS eT ?callback ?(cntexample=false) ~limit p g =
  let a =
    try
      let a = PHprover.find (goal_external_proofs g) p in
      set_timelimit (limit.Call_provers.limit_time) a;
      set_memlimit (limit.Call_provers.limit_mem) a;
      a
    with Not_found ->
      let ep = add_external_proof ~keygen:O.create ~obsolete:false
        ~archived:false ~limit
        ~edit:None g p Interrupted in
      O.init ep.proof_key (Proof_attempt ep);
      ep
  in
  run_external_proof eS eT ~cntexample ?callback a

let prover_on_goal_or_children eS eT
    ~context_unproved_goals_only ~cntexample ~limit p g =
  goal_iter_leaf_goal ~unproved_only:context_unproved_goals_only
    (prover_on_goal eS eT ~cntexample ~limit p) g

let run_prover eS eT ~context_unproved_goals_only ~cntexample ~limit pr a =
  match a with
  | Goal g ->
    prover_on_goal_or_children eS eT
      ~context_unproved_goals_only ~cntexample ~limit pr g
  | Theory th ->
        List.iter
          (prover_on_goal_or_children eS eT
             ~context_unproved_goals_only ~cntexample ~limit pr)
          th.theory_goals
    | File file ->
        List.iter
          (fun th ->
             List.iter
               (prover_on_goal_or_children eS eT
                  ~context_unproved_goals_only ~cntexample ~limit pr)
               th.theory_goals)
          file.file_theories
    | Proof_attempt a ->
        prover_on_goal_or_children eS eT
          ~context_unproved_goals_only ~cntexample ~limit pr a.proof_parent
    | Transf tr ->
        List.iter
          (prover_on_goal_or_children eS eT
             ~context_unproved_goals_only ~cntexample ~limit pr)
          tr.transf_goals
    | Metas m ->
      prover_on_goal_or_children eS eT
        ~context_unproved_goals_only ~cntexample ~limit pr m.metas_goal



(***********************************)
(* method: mark proofs as obsolete *)
(***********************************)

let cancel_proof a =
  if not a.proof_archived then
    set_obsolete ~notify a

let cancel = iter_proof_attempt cancel_proof

(** Set or unset archive *)

let set_archive a b = set_archived a b; notify (Proof_attempt a)

(*********************************)
(* method: check existing proofs *)
(*********************************)

type report =
  | Result of Call_provers.prover_result * Call_provers.prover_result
  | CallFailed of exn
  | Prover_not_installed
  | Edited_file_absent of string
  | No_former_result of Call_provers.prover_result

let push_report report (g,p,limits,r) =
  (goal_name g,p,limits,r)::report

let check_external_proof ~use_steps eS eT todo a =
  let callback a ap limits old s =
    let g = a.proof_parent in
    match s with
    | Starting ->
      Todo.start todo
    | MissingFile f ->
      Todo._done todo (g, ap, limits, Edited_file_absent f)
    | MissingProver ->
      Todo._done todo (g, ap, limits, Prover_not_installed)
    | StatusChange (Scheduled | Running) -> ()
    | StatusChange (Interrupted | Unedited | JustEdited) -> assert false
    | StatusChange (InternalFailure e) ->
      Todo._done todo (g, ap, limits, CallFailed e)
    | StatusChange (Done res) ->
      let r =
        match old with
        | None -> No_former_result res
        | Some old -> Result (res, old) in
      Todo._done todo (g, ap, limits, r) in
  run_external_proof_v2 ~use_steps eS eT a callback

let rec goal_iter_proof_attempt_with_release ~release f g =
  let iter g = goal_iter_proof_attempt_with_release ~release f g in
  PHprover.iter (fun _ a -> f a) (goal_external_proofs g);
  PHstr.iter (fun _ t -> List.iter iter t.transf_goals) (goal_transformations g);
  Mmetas_args.iter (fun _ t -> iter t.metas_goal) (goal_metas g);
  if release then release_task g

let check_all ?(release=false) ~use_steps ?filter eS eT ~callback =
  Debug.dprintf debug "[Sched] check all@.%a@." print_session eS.session;
  let todo = Todo.create [] push_report callback in
  Todo.start todo;
  let check_top_goal g =
    let check a =
      let c = match filter with
        | None -> true
        | Some f -> f a in
      if c then check_external_proof ~use_steps eS eT todo a in
    goal_iter_proof_attempt_with_release ~release check g
  in
  PHstr.iter (fun _ file ->
      List.iter (fun t ->
          List.iter check_top_goal t.theory_goals)
        file.file_theories)
    eS.session.session_files;
  Todo.stop todo


(**********************************)
(* method: replay obsolete proofs *)
(**********************************)

(* in the default context, a proof should be replayed if
   . it was successful or
   . it was just edited
*)
let proof_should_be_replayed a =
  match a.proof_state with
    | Done { Call_provers.pr_answer = Call_provers.Valid }
    | JustEdited -> true
    | _ -> false

let rec replay_on_goal_or_children eS eT
    ~obsolete_only ~context_unproved_goals_only g =
  iter_goal
    (fun a ->
       if not obsolete_only || a.proof_obsolete then
         if not context_unproved_goals_only || proof_should_be_replayed a
         then run_external_proof eS eT a)
    (iter_transf
       (replay_on_goal_or_children eS eT
          ~obsolete_only ~context_unproved_goals_only)
    )
    (iter_metas
       (replay_on_goal_or_children eS eT
          ~obsolete_only ~context_unproved_goals_only)
    )
    g

let replay eS eT ~obsolete_only ~context_unproved_goals_only a =
  match a with
    | Goal g ->
        replay_on_goal_or_children eS eT
          ~obsolete_only ~context_unproved_goals_only g
    | Theory th ->
        List.iter
          (replay_on_goal_or_children eS eT
             ~obsolete_only ~context_unproved_goals_only)
          th.theory_goals
    | File file ->
        List.iter
          (fun th ->
             List.iter
               (replay_on_goal_or_children eS eT
                  ~obsolete_only ~context_unproved_goals_only)
               th.theory_goals)
          file.file_theories
    | Proof_attempt a ->
        replay_on_goal_or_children eS eT
          ~obsolete_only ~context_unproved_goals_only a.proof_parent
    | Transf tr ->
        List.iter
          (replay_on_goal_or_children eS eT
             ~obsolete_only ~context_unproved_goals_only)
          tr.transf_goals
    | Metas m ->
      replay_on_goal_or_children eS eT
        ~obsolete_only ~context_unproved_goals_only m.metas_goal


(***********************************)
(* play all                        *)
(***********************************)

let rec play_on_goal_and_children eS eT ~limit todo l g =
  let limit, auto_proved =
    PHprover.fold (fun _ pa (limit, _ as acc) ->
      match pa.proof_edited_as, pa.proof_state with
        | None, Done { Call_provers.pr_answer = Call_provers.Valid } ->
            Call_provers.limit_max limit pa.proof_limit, true
        | _ -> acc)
      (goal_external_proofs g) (limit, false) in
  let callback _key status =
    if not (running status) then Todo._done todo () in
  if auto_proved then begin
    List.iter
      (fun p ->
        Todo.start todo;
      (* eprintf "todo increased to %d@." todo.Todo.todo; *)
      (* eprintf "prover %a on goal %s@." *)
      (*   Whyconf.print_prover p g.goal_name.Ident.id_string; *)
        prover_on_goal eS eT ~callback ~limit p g)
      l
  end;
  iter_goal
    (fun _ -> ())
    (iter_transf
       (play_on_goal_and_children eS eT ~limit todo l)
    )
    (iter_metas
       (play_on_goal_and_children eS eT ~limit todo l)
    )
    g


let play_all eS eT ~callback ~limit l =
  let todo = Todo.create () (fun () _ -> ()) callback in
  Todo.start todo;
  PHstr.iter
    (fun _ file ->
      List.iter
        (fun th ->
          List.iter
            (play_on_goal_and_children eS eT ~limit todo l)
            th.theory_goals)
        file.file_theories)
    eS.session.session_files;
  Todo.stop todo


(** Transformation *)

let transformation_on_goal_aux eS tr keep_dumb_transformation g =
  let gtask = goal_task_or_recover eS g in
  let subgoals = Trans.apply_transform tr eS.env gtask in
  let b = keep_dumb_transformation ||
    match subgoals with
      | [task] -> not (Task.task_equal task gtask)
      | _ -> true
  in
  if b then
    let ntr = add_transformation ~init:init_any ~notify ~keygen:O.create eS tr g subgoals in
    Some ntr
  else None

let transform_goal eS sched ?(keep_dumb_transformation=false)
    ?callback tr g =
  schedule_delayed_action sched
    (fun () -> let ntr = transformation_on_goal_aux eS tr
                 keep_dumb_transformation g in
               Opt.apply () callback ntr)


let transform_goal_or_children ~context_unproved_goals_only eS sched ?callback
    tr g =
  goal_iter_leaf_goal ~unproved_only:context_unproved_goals_only
    (transform_goal eS sched ~keep_dumb_transformation:false
       ?callback tr) g

let rec transform eS sched ~context_unproved_goals_only ?callback tr a =
  match a with
    | Goal g | Proof_attempt {proof_parent = g} ->
      transform_goal_or_children ~context_unproved_goals_only eS sched
        ?callback tr g
    | _ -> iter (transform ~context_unproved_goals_only eS sched ?callback tr) a

(*****************************)
(* method: edit current goal *)
(*****************************)

let edit_proof_v3 ~cntexample eS sched ~default_editor callback a =
  match find_prover eS a with
  | None ->
          (* nothing to do
             TODO: report an non replayable proof if some option is set
          *)
    ()
  | Some(_,npc,a) ->
    let editor =
      match npc.prover_config.Whyconf.editor with
      | "" -> default_editor
      | s ->
        try
          let ed = Whyconf.editor_by_id eS.whyconf s in
          String.concat " "(ed.Whyconf.editor_command ::
                              ed.Whyconf.editor_options)
        with Not_found -> default_editor
    in
    let file = update_edit_external_proof ~cntexample eS a in
    Debug.dprintf debug "[Editing] goal %s with command '%s' on file %s@."
      (goal_name a.proof_parent).Ident.id_string editor file;
    schedule_edition sched editor file (fun res -> callback a res)

let edit_proof ~cntexample eS sched ~default_editor a =
  (* check that the state is not Scheduled or Running *)
  if a.proof_archived || running a.proof_state then ()
(*
    info_window `ERROR "Edition already in progress"
*)
  else
    let callback a res =
      match res with
      | Done {Call_provers.pr_answer = Call_provers.Unknown ("", _)} ->
        set_proof_state ~notify ~obsolete:true ~archived:false
          JustEdited a
      | _ ->
        set_proof_state ~notify ~obsolete:false ~archived:false
          res a
    in
    edit_proof_v3 ~cntexample eS sched ~default_editor callback a

let edit_proof_v3 ~cntexample eS sched ~default_editor ~callback a =
  let callback a res =
    match res with
    | Done {Call_provers.pr_answer = Call_provers.Unknown ("", _)} ->
      callback a
    | _ -> ()
  in
  edit_proof_v3 ~cntexample eS sched ~default_editor callback a


(*************)
(* removing  *)
(*************)

let remove_proof_attempt (a:O.key proof_attempt) =
  O.remove a.proof_key;
  let notify = (notify : O.key notify) in
  remove_external_proof ~notify a

let remove_transformation t =
  O.remove t.transf_key;
  remove_transformation ~notify t

let remove_metas t =
  O.remove t.metas_key;
  remove_metas ~notify t

(* a proof is removable if
    . it is not in progress and
    . it is obsolete or not successful
*)
let proof_removable a =
  match a.proof_state with
  | Scheduled | Running -> false
  | Done pr ->
    a.proof_obsolete || pr.Call_provers.pr_answer <> Call_provers.Valid
  | Unedited | JustEdited | Interrupted | InternalFailure _ -> true


let rec clean = function
  | Goal g when Opt.inhabited (goal_verified g) ->
    iter_goal
      (fun a -> if proof_removable a then remove_proof_attempt a)
      (fun t ->
        if not (Opt.inhabited t.transf_verified) then remove_transformation t
        else transf_iter clean t)
      (fun m ->
        if not (Opt.inhabited m.metas_verified) then remove_metas m
        else metas_iter clean m)
      g
  | Goal g ->
    (* don't iter on proof_attempt if the goal is not proved *)
    iter_goal (fun _ -> ()) (transf_iter clean) (metas_iter clean) g
  | Proof_attempt a -> clean (Goal a.proof_parent)
  | any -> iter clean any

(**** convert ***)

let convert_unknown_prover =
  Session_tools.convert_unknown_prover ~keygen:O.create

  open Strategy

  let rec exec_strategy ~todo es sched pc strat g =
    if pc < 0 || pc >= Array.length strat then
      (* halt the strategy *)
      Todo._done todo ()
    else
      match Array.get strat pc with
        | Icall_prover(p,timelimit,memlimit) ->
          let callback _pa res =
            match res with
              | Scheduled | Running ->
                (* nothing to do yet *)
                ()
              | Done { Call_provers.pr_answer = Call_provers.Valid } ->
                (* proof succeeded, nothing more to do *)
                Todo._done todo ()
              | Interrupted | InternalFailure _ | Done _ ->
                (* proof did not succeed, goto to next step *)
                let callback () = exec_strategy ~todo es sched (pc+1) strat g in
                schedule_delayed_action sched callback
              | Unedited | JustEdited ->
                (* should not happen *)
                assert false
          in
          let limit = { Call_provers.empty_limit with
                        Call_provers.limit_time = timelimit;
                        limit_mem  = memlimit} in
          prover_on_goal es sched ~callback ~limit p g
        | Itransform(trname,pcsuccess) ->
          let callback ntr =
            match ntr with
              | None -> (* transformation failed *)
                let callback () = exec_strategy ~todo es sched (pc+1) strat g in
                schedule_delayed_action sched callback
              | Some tr ->
                List.iter
                  (fun g ->
                    Todo.start todo;
                    let callback () =
                      exec_strategy ~todo es sched pcsuccess strat g
                    in
                    schedule_delayed_action sched callback
                  )
                tr.transf_goals;
                Todo._done todo ()
          in
          transform_goal es sched ~callback trname g
        | Igoto pc ->
          exec_strategy ~todo es sched pc strat g


  let run_strategy_on_goal
      ?(intermediate_callback=fun () -> ())
      ?(final_callback=fun () -> ())
      es sched strat g =
    let todo =
      Todo.create () (fun () -> intermediate_callback) final_callback
    in
    Todo.start todo;
    let callback () = exec_strategy ~todo es sched 0 strat g in
    schedule_delayed_action sched callback


  let run_strategy_on_goal_or_children ~context_unproved_goals_only
      eS sched strat g =
    goal_iter_leaf_goal ~unproved_only:context_unproved_goals_only
      (run_strategy_on_goal eS sched strat) g

  let rec run_strategy eS sched ~context_unproved_goals_only strat a =
    match a with
    | Goal g | Proof_attempt {proof_parent = g} ->
      run_strategy_on_goal_or_children ~context_unproved_goals_only
        eS sched strat g
    | _ ->
      iter (run_strategy ~context_unproved_goals_only eS sched strat) a


end


module Base_scheduler (X : sig end)  =
  (struct

    let idle_handler = ref None
    let timeout_handler = ref None

    let verbose = ref true

     let idle f =
       match !idle_handler with
         | None -> idle_handler := Some f;
         | Some _ -> failwith "Replay.idle: already one handler installed"

     let timeout ~ms f =
       match !timeout_handler with
         | None -> timeout_handler := Some(float ms /. 1000.0 ,f);
         | Some _ -> failwith "Replay.timeout: already one handler installed"

     let notify_timer_state w s r =
       if !verbose then
         Printf.eprintf "Progress: %d/%d/%d                       \r%!" w s r

     let main_loop () =
       let last = ref (Unix.gettimeofday ()) in
       try while true do
           let time = Unix.gettimeofday () -. !last in
           (* attempt to run timeout handler *)
           let timeout =
             match !timeout_handler with
               | None -> false
               | Some(ms,f) ->
                 if time > ms then
                   let b = f () in
                   if b then true else
                     begin
                       timeout_handler := None;
                       true
                     end
                 else false
           in
           if timeout then
             last := Unix.gettimeofday ()
           else
      (* attempt to run the idle handler *)
             match !idle_handler with
               | None ->
                 begin
                   let ms =
                     match !timeout_handler with
                       | None -> raise Exit
                       | Some(ms,_) -> ms
                   in
                   usleep (ms -. time)
                 end
               | Some f ->
                 let b = f () in
                 if b then () else
                   begin
                     idle_handler := None;
                   end
         done
       with Exit -> ()

end)





(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
