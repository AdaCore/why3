(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Session
open Debug

let debug = register_flag "scheduler"

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

  val unknown_prover :
    key env_session -> Whyconf.prover -> Whyconf.prover option

  val replace_prover : key proof_attempt -> key proof_attempt -> bool

end

module Make(O : OBSERVER) = struct

let notify = O.notify

let rec init_any any =
  O.init (key_any any) any;
  iter init_any any

let init_session session = session_iter init_any session

(***************************)
(*     session state       *)
(***************************)

(* type prover_option = *)
(*   | Detected_prover of prover_data *)
(*   | Undetected_prover of string *)

(* let prover_id p = match p with *)
(*   | Detected_prover p -> p.prover_id *)
(*   | Undetected_prover s -> s *)

let theory_name t = t.theory_name
let theory_key t = t.theory_key
let verified t = t.theory_verified
let goals t = t.theory_goals
let theory_expanded t = t.theory_expanded

let running a = match a.proof_state with
  | Undone (Scheduled | Running) -> true
  | Undone (Unedited | JustEdited | Interrupted)
  | Done _ | InternalFailure _ -> false

(*************************)
(*         Scheduler     *)
(*************************)

type action =
  | Action_proof_attempt of int * int * in_channel option * string *
      Driver.driver * (proof_attempt_status -> unit) * Task.task
  | Action_delayed of (unit -> unit)


type timeout_action =
  | Check_prover of (proof_attempt_status -> unit) * Call_provers.prover_call
  | Any_timeout of (unit -> bool)

type t =
    { (** Actions that wait some idle time *)
      actions_queue : action Queue.t;
      (** Quota of action slot *)
      mutable maximum_running_proofs : int;
      (** Running actions which take one action slot *)
      mutable running_proofs : timeout_action list;
      (** Running check which doesn't take a running slot.
          Check the end of some computation *)
      mutable running_check : (unit -> bool) list;
      (** proof attempt that wait some available action slot *)
      proof_attempts_queue :
        ((proof_attempt_status -> unit) *
            (unit -> Call_provers.prover_call))
        Queue.t;
      (** timeout handler state *)
      mutable timeout_handler_activated : bool;
      mutable timeout_handler_running : bool;
      (** idle handler state *)
      mutable idle_handler_activated : bool;
    }

let set_maximum_running_proofs max sched =
 (** TODO dequeue actions if maximum_running_proofs increase *)
  sched.maximum_running_proofs <- max

let init max =
  dprintf debug "[Sched] init scheduler max=%i@." max;
  { actions_queue = Queue.create ();
    maximum_running_proofs = max;
    running_proofs = [];
    running_check = [];
    proof_attempts_queue = Queue.create ();
    timeout_handler_activated = false;
    timeout_handler_running = false;
    idle_handler_activated = false
  }

(* timeout handler *)

let timeout_handler t =
  dprintf debug "[Sched] Timeout handler called@.";
  assert (not t.timeout_handler_running);
  t.timeout_handler_running <- true;
  (** Check if some action ended *)
  let l = List.fold_left
    (fun acc c ->
       match c with
         | Check_prover(callback,call)  ->
             (match Call_provers.query_call call with
               | None -> c::acc
               | Some post ->
                   let res = post () in callback (Done res);
                   acc)
         | Any_timeout callback ->
             let b = callback () in
             if b then c::acc else acc)
    [] t.running_proofs
  in
  (** Check if some new actions must be started *)
  let l =
    if List.length l < t.maximum_running_proofs then
      begin try
        let (callback,pre_call) = Queue.pop t.proof_attempts_queue in
        callback (Undone Running);
        dprintf debug "[Sched] proof attempts started@.";
        let call = pre_call () in
        (Check_prover(callback,call))::l
      with Queue.Empty -> l
      end
    else l
  in
  t.running_proofs <- l;
  (** Call the running check *)
  t.running_check <- List.fold_left
    (fun acc check -> if check () then check::acc else acc)
    [] t.running_check;
  let continue =
    match l with
      | [] ->
          dprintf debug "[Sched] Timeout handler stopped@.";
          false
      | _ -> true
  in
  O.notify_timer_state
    (Queue.length t.actions_queue)
    (Queue.length t.proof_attempts_queue) (List.length l);
  t.timeout_handler_activated <- continue;
  t.timeout_handler_running <- false;
  continue

let run_timeout_handler t =
  if t.timeout_handler_activated then () else
    begin
      t.timeout_handler_activated <- true;
      dprintf debug "[Sched] Timeout handler started@.";
      O.timeout ~ms:100 (fun () -> timeout_handler t)
    end

let schedule_any_timeout t callback =
  dprintf debug "[Sched] schedule a new timeout@.";
  t.running_proofs <- (Any_timeout callback) :: t.running_proofs;
  run_timeout_handler t

let add_a_check t callback =
  dprintf debug "[Sched] add a new check@.";
  t.running_check <- callback :: t.running_check;
  run_timeout_handler t

(* idle handler *)


let idle_handler t =
  try
    begin
      match Queue.pop t.actions_queue with
        | Action_proof_attempt(timelimit,memlimit,old,command,driver,
                               callback,goal) ->
            callback (Undone Scheduled);
            begin
              try
                let pre_call =
                  Driver.prove_task
                    ?old ~command ~timelimit ~memlimit driver goal
                in
                Queue.push (callback,pre_call) t.proof_attempts_queue;
                run_timeout_handler t
              with e ->
                Format.eprintf "@[Exception raise in Session.idle_handler:@ \
%a@.@]"
                  Exn_printer.exn_printer e;
                callback (InternalFailure e)
            end
        | Action_delayed callback -> callback ()
    end;
    true
  with Queue.Empty ->
    t.idle_handler_activated <- false;
    dprintf debug "[Sched] idle_handler stopped@.";
    false
    | e ->
      Format.eprintf "@[Exception raise in Session.idle_handler:@ %a@.@]"
        Exn_printer.exn_printer e;
      eprintf "Session.idle_handler stopped@.";
      false


let run_idle_handler t =
  if t.idle_handler_activated then () else
    begin
      t.idle_handler_activated <- true;
      dprintf debug "[Sched] idle_handler started@.";
      O.idle (fun () -> idle_handler t)
    end

(* main scheduling functions *)

let cancel_scheduled_proofs t =
  let new_queue = Queue.create () in
  try
    while true do
      match Queue.pop t.actions_queue with
        | Action_proof_attempt(_timelimit,_memlimit,_old,_command,
                               _driver,callback,_goal) ->
            callback (Undone Interrupted)
        | Action_delayed _ as a->
            Queue.push a new_queue
    done
  with Queue.Empty ->
    Queue.transfer new_queue t.actions_queue;
    try
      while true do
        let (callback,_) = Queue.pop t.proof_attempts_queue in
        callback (Undone Interrupted)
      done
    with
      | Queue.Empty ->
          O.notify_timer_state 0 0 (List.length t.running_proofs)


let schedule_proof_attempt ~timelimit ~memlimit ?old
    ~command ~driver ~callback t goal =
    dprintf debug "[Sched] Scheduling a new proof attempt (goal : %a)@."
      (fun fmt g -> Format.pp_print_string fmt
       (Task.task_goal g).Decl.pr_name.Ident.id_string) goal;
  Queue.push
    (Action_proof_attempt(timelimit,memlimit,old,command,driver,
                        callback,goal))
    t.actions_queue;
  run_idle_handler t

let schedule_edition t command filename callback =
  dprintf debug "[Sched] Scheduling an edition@.";
  let precall =
    Call_provers.call_on_file ~command ~regexps:[] ~timeregexps:[]
      ~exitcodes:[(0,Call_provers.Unknown "")] filename
  in
  callback (Undone Running);
  t.running_proofs <- (Check_prover(callback, precall ())) :: t.running_proofs;
  run_timeout_handler t

let schedule_delayed_action t callback =
  dprintf debug "[Sched] Scheduling a delayed action@.";
  Queue.push (Action_delayed callback) t.actions_queue;
  run_idle_handler t

(**************************)
(*  session function      *)
(**************************)

let update_session ~allow_obsolete old_session env whyconf  =
  O.reset ();
  let (env_session,_) as res =
    update_session ~keygen:O.create ~allow_obsolete old_session env whyconf in
  init_session env_session.session;
  res

let add_file env_session f =
  let mfile = add_file ~keygen:O.create env_session f in
  let any_file = (File mfile) in
  init_any any_file;
  O.notify any_file;
  mfile

(*****************************************************)
(* method: run a given prover on each unproved goals *)
(*****************************************************)
let rec find_loadable_prover eS prover =
  (** try the default one *)
  match load_prover eS prover with
    | None -> begin
      (** If its not loadable ask for one*)
      match O.unknown_prover eS prover with
        | None -> None
        | Some prover -> find_loadable_prover eS prover
    end
    | Some npc -> Some (prover,npc)

let adapt_timelimit a =
  match a.proof_state with
    | Done { Call_provers.pr_answer = Call_provers.Valid ;
             Call_provers.pr_time = t } ->
      let time = max a.proof_timelimit (1 + truncate (2.0 *. t)) in
      set_timelimit time a;
      time
    | _ -> a.proof_timelimit


let run_external_proof eS eT ?callback a =
  (* check that the state is not Scheduled or Running *)
  (* Perhaps this test, a.proof_archived, should be done somewhere else *)
  if a.proof_archived || running a then ()
  else
    let ap = a.proof_prover in
    match find_loadable_prover eS a.proof_prover with
      | None ->
        Debug.dprintf debug
          "[Info] Can't redo an external proof since the prover %a is not loaded@."
          Whyconf.print_prover a.proof_prover;
        Util.apply_option2 () callback a a.proof_state
      | Some (nap,npc) ->
        (* eprintf "prover %a on goal %s@." *)
        (*   Whyconf.print_prover a.proof_prover a.proof_parent.goal_name.Ident.id_string; *)
        let g = a.proof_parent in
        try
          if nap == ap then raise Not_found;
          let np_a = PHprover.find g.goal_external_proofs nap in
          if O.replace_prover np_a a then
            begin
            (** The notification will be done by the new proof_attempt *)
              O.remove np_a.proof_key;
              raise Not_found
            end
        with Not_found ->
          (** replace [a] by a new_proof attempt if [a.proof_prover] was not
              loadable *)
        let a = if nap == ap then a
          else
            let a = copy_external_proof
              ~notify ~keygen:O.create ~prover:nap ~env_session:eS a in
            O.init a.proof_key (Proof_attempt a);
            a
        in
        if a.proof_edited_as = None &&
          npc.prover_config.Whyconf.interactive then
          begin
            set_proof_state ~notify ~obsolete:false ~archived:false
              (Undone Unedited) a;
            Util.apply_option2 () callback a a.proof_state
          end
        else
          begin
          let previous_result,previous_obs = a.proof_state,a.proof_obsolete in
          let timelimit = adapt_timelimit a in
          let callback result =
            begin match result with
              | Undone Interrupted ->
                  set_proof_state ~notify
                    ~obsolete:previous_obs ~archived:false previous_result a
              | _ ->
                  set_proof_state ~notify ~obsolete:false
                    ~archived:false result a end;
            Util.apply_option2 () callback a result
          in
          let old =
            match get_edited_as_abs eS.session a with
              | None -> None
              | Some f ->
                if Sys.file_exists f then begin
                  dprintf debug "Info: proving using edited file %s@." f;
                  (Some (open_in f))
                end
                else begin
                  dprintf debug "Warning: the file %s is not found@." f;
                  None
                end
          in
          let command =
            String.concat " " (npc.prover_config.Whyconf.command ::
                                 npc.prover_config.Whyconf.extra_options) in
          (* eprintf "scheduling it...@."; *)
          schedule_proof_attempt
            ~timelimit ~memlimit:0
            ?old ~command
            ~driver:npc.prover_driver
            ~callback
            eT
            (goal_task g)
        end

let prover_on_goal eS eT ?callback ~timelimit p g =
  let a =
    try
      let a = PHprover.find g.goal_external_proofs p in
      set_timelimit timelimit a;
      a
    with Not_found ->
      let ep = add_external_proof ~keygen:O.create ~obsolete:false
        ~archived:false ~timelimit
        ~edit:None g p (Undone Interrupted) in
      O.init ep.proof_key (Proof_attempt ep);
      ep
  in
  run_external_proof eS eT ?callback a

let prover_on_goal_or_children eS eT
    ~context_unproved_goals_only ~timelimit p g =
  goal_iter_leaf_goal ~unproved_only:context_unproved_goals_only
    (prover_on_goal eS eT ~timelimit p) g

let run_prover eS eT ~context_unproved_goals_only ~timelimit pr a =
  match a with
    | Goal g ->
        prover_on_goal_or_children eS eT
          ~context_unproved_goals_only ~timelimit pr g
    | Theory th ->
        List.iter
          (prover_on_goal_or_children eS eT
             ~context_unproved_goals_only ~timelimit pr)
          th.theory_goals
    | File file ->
        List.iter
          (fun th ->
             List.iter
               (prover_on_goal_or_children eS eT
                  ~context_unproved_goals_only ~timelimit pr)
               th.theory_goals)
          file.file_theories
    | Proof_attempt a ->
        prover_on_goal_or_children eS eT
          ~context_unproved_goals_only ~timelimit pr a.proof_parent
    | Transf tr ->
        List.iter
          (prover_on_goal_or_children eS eT
             ~context_unproved_goals_only ~timelimit pr)
          tr.transf_goals

(**********************************)
(* method: replay obsolete proofs *)
(**********************************)

let proof_successful_or_just_edited a =
  match a.proof_state with
    | Done { Call_provers.pr_answer = Call_provers.Valid }
    | Undone JustEdited -> true
    | _ -> false

let rec replay_on_goal_or_children eS eT
    ~obsolete_only ~context_unproved_goals_only g =
  PHprover.iter
    (fun _ a ->
       if not obsolete_only || a.proof_obsolete then
         if not context_unproved_goals_only || proof_successful_or_just_edited a
         then run_external_proof eS eT a)
    g.goal_external_proofs;
  PHstr.iter
    (fun _ t ->
       List.iter
         (replay_on_goal_or_children eS eT
            ~obsolete_only ~context_unproved_goals_only)
         t.transf_goals)
    g.goal_transformations

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
  | No_former_result of Call_provers.prover_result

module Todo = struct
  type ('a,'b) todo =
      {mutable todo : int;
       report : 'a;
       push_report : 'a -> 'b -> unit}

  let create init push =
    {todo = 0;  report = init; push_report = push}

  let _done todo v =
    todo.todo <- todo.todo - 1;
    todo.push_report todo.report v

  let stop todo =
    todo.todo <- todo.todo - 1

  let todo todo =
    todo.todo <- todo.todo + 1

  let _end todo =
    if todo.todo<>0 then None else Some todo.report

  let print todo =
    dprintf debug "[Sched] todo : %i@." todo.todo
end

let push_report report (g,p,t,r) =
  report := (g.goal_name,p,t,r)::!report

(** When no smoke *)
let check_external_proof eS eT todo a =
  let g = a.proof_parent in
  dprintf debug "[Sched] Check external proof : %a@."
    (fun fmt g -> pp_print_string fmt g.goal_name.Ident.id_string) g;
  (* check that the state is not Scheduled or Running *)
  if a.proof_archived || running a then ()
  else
    begin
      Todo.todo todo;
      let ap = a.proof_prover in
      match find_loadable_prover eS ap with
        | None ->
          dprintf debug "[sched] prover not found : %a@."
            Whyconf.print_prover ap;
            Todo._done todo (g,ap,0,Prover_not_installed)
            (* set_proof_state ~notify ~obsolete:false a Undone *)
        | Some (nap,npc) ->
          let g = a.proof_parent in
          try
            if nap == ap then raise Not_found;
            let np_a = PHprover.find g.goal_external_proofs nap in
            if O.replace_prover np_a a then begin
              (** The notification will be done by the new proof_attempt *)
              O.remove np_a.proof_key;
              raise Not_found end
          with Not_found ->
          (** replace [a] by a new_proof attempt if [a.proof_prover] was not
              loadable *)
          let a = if nap == ap then a
            else
              let a = copy_external_proof
                 ~notify ~keygen:O.create ~prover:nap ~env_session:eS a in
              O.init a.proof_key (Proof_attempt a);
              a in
          let timelimit = adapt_timelimit a in
          let callback result =
              match result with
                | Undone Scheduled | Undone Running | Undone Interrupted -> ()
                | Undone (Unedited | JustEdited) -> assert false
                | InternalFailure msg ->
                  Todo._done todo (g,ap,timelimit,(CallFailed msg));
                  set_proof_state ~notify ~obsolete:false ~archived:false
                    result a
                | Done new_res ->
                  begin
                    match a.proof_state with
                      | Done old_res ->
                          Todo._done todo
                            (g,ap,timelimit,(Result(new_res,old_res)))
                      | _ ->
                        Todo._done todo
                          (g,ap,timelimit,No_former_result new_res)
                  end;
                  set_proof_state ~notify ~obsolete:false ~archived:false
                    result a
          in
          let old =
            match a.proof_edited_as with
              | None -> None
              | Some edited_as ->
                let f = Filename.concat eS.session.session_dir edited_as in
              (* Format.eprintf "Info: proving using edited file %s@." f; *)
                (Some (open_in f))
          in
          let command =
            String.concat " " (npc.prover_config.Whyconf.command ::
                                 npc.prover_config.Whyconf.extra_options) in
          schedule_proof_attempt eT
            ~timelimit ~memlimit:0
            ?old ~command
            ~driver:npc.prover_driver
            ~callback
            (goal_task g)
    end

let check_goal_and_children eS eT todo g =
  goal_iter_proof_attempt (check_external_proof eS eT todo) g

let check_all eS eT ~callback =
  dprintf debug "[Sched] check all@.%a@." print_session eS.session;
  let todo = Todo.create (ref []) push_report  in
  session_iter_proof_attempt (check_external_proof eS eT todo)
    eS.session;
  let timeout () =
    match Todo._end todo with
      | None -> true
      | Some reports -> callback !reports;false
  in
  schedule_any_timeout eT timeout


(***********************************)
(* play all                        *)
(***********************************)

let rec play_on_goal_and_children eS eT ~timelimit todo l g =
  let callback _key status =
    match status with
      | Undone Running | Undone Scheduled -> ()
      |  _ ->
        Todo._done todo ();
        (* eprintf "todo decreased to %d@." todo.Todo.todo *)
  in
  List.iter
    (fun p ->
      Todo.todo todo;
      (* eprintf "todo increased to %d@." todo.Todo.todo; *)
      (* eprintf "prover %a on goal %s@." *)
      (*   Whyconf.print_prover p g.goal_name.Ident.id_string; *)
      prover_on_goal eS eT ~callback ~timelimit p g)
    l;
  PHstr.iter
    (fun _ t ->
       List.iter
         (play_on_goal_and_children eS eT ~timelimit todo l)
         t.transf_goals)
    g.goal_transformations


let play_all eS eT ~callback ~timelimit l =
  let todo = Todo.create (ref ()) (fun _ _ -> ())  in
  PHstr.iter
    (fun _ file ->
      List.iter
        (fun th ->
          List.iter
            (play_on_goal_and_children eS eT ~timelimit todo l)
            th.theory_goals)
        file.file_theories)
    eS.session.session_files;
  let timeout () =
    (* eprintf "Timeout handler@."; *)
    match Todo._end todo with
      | None ->  true
      | Some _ -> callback (); false
  in
  schedule_any_timeout eT timeout



(** Transformation *)

let transformation_on_goal_aux eS tr keep_dumb_transformation g =
  let subgoals = Trans.apply_transform tr eS.env (goal_task g) in
  let b = keep_dumb_transformation ||
    match subgoals with
      | [task] ->
              (* let s1 = task_checksum (get_task g) in *)
              (* let s2 = task_checksum task in *)
              (* (\* *)
              (*   eprintf "Transformation returned only one task.
                   sum before = %s, sum after = %s@." (task_checksum g.task)
                   (task_checksum task); *)
              (*   eprintf "addresses: %x %x@." (Obj.magic g.task)
                   (Obj.magic task); *)
              (* *\) *)
              (* s1 <> s2 *)
        not (Task.task_equal task (goal_task g))
      | _ -> true
  in
  if b then
    let goal_name = g.goal_name.Ident.id_string in
    let i = ref (-1) in
    let ntr = add_transformation
      ~keygen:O.create
      ~goal:(fun subtask ->
        incr i;
        let gid,expl,task = goal_expl_task subtask in
        let gid =
          Ident.id_derive (goal_name ^ "." ^ (string_of_int (!i))) gid in
        let gid = Ident.id_register gid in
        gid,expl,task)
      tr g subgoals in
    init_any (Transf ntr);
    Some ntr
  else None

let transform_goal eS sched ?(keep_dumb_transformation=false)
    ?callback tr g =
  schedule_delayed_action sched
    (fun () -> let ntr = transformation_on_goal_aux eS tr
                 keep_dumb_transformation g in
               Util.apply_option () callback ntr)


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

let edit_proof eS sched ~default_editor a =
  (* check that the state is not Scheduled or Running *)
  if a.proof_archived || running a then ()
(*
    info_window `ERROR "Edition already in progress"
*)
  else
    let ap = a.proof_prover in
    match find_loadable_prover eS a.proof_prover with
      | None -> ()
        (** Perhaps a new prover *)
      | Some (nap,npc) ->
          let g = a.proof_parent in
          try
            if nap == ap then raise Not_found;
            let np_a = PHprover.find g.goal_external_proofs nap in
            if O.replace_prover np_a a then begin
              (** The notification will be done by the new proof_attempt *)
              O.remove np_a.proof_key;
              raise Not_found end
          with Not_found ->
          (** replace [a] by a new_proof attempt if [a.proof_prover] was not
              loadable *)
          let a = if nap == ap then a
            else
              let a = copy_external_proof
                ~notify ~keygen:O.create ~prover:nap ~env_session:eS a in
              O.init a.proof_key (Proof_attempt a);
              a in
          (** Now [a] is a proof_attempt of the lodable prover [nap] *)
          let callback res =
            match res with
              | Done {Call_provers.pr_answer = Call_provers.Unknown ""} ->
                set_proof_state ~notify ~obsolete:true ~archived:false
                  (Undone JustEdited) a
              | _ ->
                  set_proof_state ~notify ~obsolete:false ~archived:false
                    res a
          in
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
          let file = update_edit_external_proof eS a in
          dprintf debug "[Editing] goal %a with command %s %s@."
            (fun fmt a -> pp_print_string fmt
              (Task.task_goal (goal_task a.proof_parent))
              . Decl.pr_name.Ident.id_string)
            a editor file;
          schedule_edition sched editor file callback

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

let rec clean = function
  | Goal g when g.goal_verified ->
    iter_goal
      (fun a ->
        if a.proof_obsolete || not (proof_successful_or_just_edited a) then
          remove_proof_attempt a)
      (fun t ->
        if not t.transf_verified then remove_transformation t
        else transf_iter clean t) g
  | Goal g ->
    (** iter only on transformations if the goal is not proved *)
    PHstr.iter (fun _ t -> transf_iter clean t) g.goal_transformations
  | Proof_attempt a -> clean (Goal a.proof_parent)
  | any -> iter clean any

(**** convert ***)

let convert_unknown_prover =
  Session_tools.convert_unknown_prover ~keygen:O.create

end


module Base_scheduler (X : sig end)  =
  (struct

    let usleep t = ignore (Unix.select [] [] [] t)


    let idle_handler = ref None
    let timeout_handler = ref None

     let idle f =
       match !idle_handler with
         | None -> idle_handler := Some f;
         | Some _ -> failwith "Replay.idle: already one handler installed"

     let timeout ~ms f =
       match !timeout_handler with
         | None -> timeout_handler := Some(float ms /. 1000.0 ,f);
         | Some _ -> failwith "Replay.timeout: already one handler installed"

     let notify_timer_state w s r =
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
