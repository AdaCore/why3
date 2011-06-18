(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
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


open Why
open Format

(***************************)
(*     provers             *)
(***************************)

type prover_data =
    { prover_id : string;
      prover_name : string;
      prover_version : string;
      command : string;
      driver_name : string;
      driver : Driver.driver;
      mutable editor : string;
    }

let get_prover_data env id pr acc =
  try
    let dr = Driver.load_driver env pr.Whyconf.driver in
    Util.Mstr.add id
      { prover_id = id ;
        prover_name = pr.Whyconf.name;
        prover_version = pr.Whyconf.version;
        command = pr.Whyconf.command;
        driver_name = pr.Whyconf.driver;
        driver = dr;
        editor = pr.Whyconf.editor;
      }
      acc
  with e ->
    eprintf "Failed to load driver %s for prover %s (%a). prover disabled@."
      pr.Whyconf.driver
      pr.Whyconf.name
      Exn_printer.exn_printer e
      ;
    acc

(***************************)
(*      transformations    *)
(***************************)

type trans =
  | Trans_one of Task.task Trans.trans
  | Trans_list of Task.task Trans.tlist

type transformation_data =
    { transformation_name : string;
      transformation : trans;
    }

let transformation_id t = t.transformation_name

let lookup_trans env name =
  try
    let t = Trans.lookup_transform name env in
    Trans_one t
  with Trans.UnknownTrans _ ->
    let t = Trans.lookup_transform_l name env in
    Trans_list t

let lookup_transformation env =
  let h = Hashtbl.create 13 in
  fun name ->
    try
      Hashtbl.find h name
    with Not_found ->
      let t = {transformation_name = name;
               transformation = lookup_trans env name }
      in Hashtbl.add h name t; t

(***************************)
(*     proof status        *)
(***************************)

type proof_attempt_status =
  | Undone
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Done of Call_provers.prover_result (** external proof done *)
  | InternalFailure of exn (** external proof aborted by internal error *)


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
end

module Make(O : OBSERVER) = struct

(***************************)
(*     session state       *)
(***************************)

type prover_option =
  | Detected_prover of prover_data
  | Undetected_prover of string

let prover_id p = match p with
  | Detected_prover p -> p.prover_id
  | Undetected_prover s -> s

type proof_attempt =
    { prover : prover_option;
      proof_goal : goal;
      proof_key : O.key;
      mutable proof_state : proof_attempt_status;
      mutable timelimit : int;
      mutable proof_obsolete : bool;
      mutable edited_as : string;
    }

and goal_parent =
  | Parent_theory of theory
  | Parent_transf of transf

and goal =
    { goal_name : string;
      goal_expl : string option;
      parent : goal_parent;
      mutable task: Task.task option;
      mutable checksum : string;
      goal_key : O.key;
      mutable proved : bool;
      mutable goal_expanded : bool;
      external_proofs: (string, proof_attempt) Hashtbl.t;
      transformations : (string, transf) Hashtbl.t;
    }

and transf =
    { transf : transformation_data;
      parent_goal : goal;
      mutable transf_proved : bool;
      transf_key : O.key;
      mutable subgoals : goal list;
      mutable transf_expanded : bool;
    }

and theory =
    { theory_name : string;
      mutable theory : Theory.theory option;
      theory_key : O.key;
      theory_parent : file;
      mutable goals : goal list;
      mutable verified : bool;
      mutable theory_expanded : bool;
    }

and file =
    { file_name : string;
      file_key : O.key;
      mutable theories: theory list;
      mutable file_verified : bool;
      mutable file_expanded : bool;
    }

type any =
  | File of file
  | Theory of theory
  | Goal of goal
  | Proof_attempt of proof_attempt
  | Transformation of transf

let theory_name t = t.theory_name
let theory_key t = t.theory_key
let verified t = t.verified
let goals t = t.goals
let theory_expanded t = t.theory_expanded


let get_theory t =
  match t.theory with
    | None ->
        eprintf "Session: theory not yet reimported, this should not happen@.";
        assert false
    | Some t -> t

let goal_name g = g.goal_name
let goal_expl g =
  match g.goal_expl with
    | None -> g.goal_name
    | Some s -> s
let goal_key g = g.goal_key
let goal_proved g = g.proved
let transformations g = g.transformations
let external_proofs g = g.external_proofs
let goal_expanded g = g.goal_expanded

let get_task g =
  match g.task with
    | None ->
        begin
          match g.parent with
            | Parent_theory _th ->
                assert false (* should not happen *)
            | Parent_transf _tr ->
                (* TODO: recompute the task from the parent transformation *)
                assert false
        end
    | Some t -> t


let rec set_goal_expanded g b =
  g.goal_expanded <- b;
  if not b then
    Hashtbl.iter (fun _ tr -> set_transf_expanded tr b) g.transformations

and set_transf_expanded tr b =
  tr.transf_expanded <- b;
  if not b then
    List.iter (fun g -> set_goal_expanded g b) tr.subgoals

let set_theory_expanded t b =
  t.theory_expanded <- b;
  if not b then
    List.iter (fun th -> set_goal_expanded th b) t.goals

let set_file_expanded f b =
  f.file_expanded <- b;
  if not b then
    List.iter (fun th -> set_theory_expanded th b) f.theories

let all_files : file list ref = ref []

let get_all_files () = !all_files

(************************)
(* saving state on disk *)
(************************)

let save_result fmt r =
  fprintf fmt "@\n<result status=\"%s\" time=\"%.2f\"/>"
    (match r.Call_provers.pr_answer with
       | Call_provers.Valid -> "valid"
       | Call_provers.Failure _ -> "failure"
       | Call_provers.Unknown _ -> "unknown"
       | Call_provers.HighFailure -> "highfailure"
       | Call_provers.Timeout -> "timeout"
       | Call_provers.Invalid -> "invalid")
    r.Call_provers.pr_time

let save_status fmt s =
  match s with
    | Undone | Scheduled | Running ->
        fprintf fmt "<undone/>@\n"
    | InternalFailure msg ->
        fprintf fmt "<internalfailure reason=\"%s\"/>@\n"
          (Printexc.to_string msg)
    | Done r -> save_result fmt r

let save_proof_attempt fmt _key a =
  fprintf fmt "@\n@[<v 1><proof prover=\"%s\" timelimit=\"%d\" edited=\"%s\" obsolete=\"%b\">"
    (prover_id a.prover) a.timelimit a.edited_as a.proof_obsolete;
  save_status fmt a.proof_state;
  fprintf fmt "@]@\n</proof>"

let opt lab fmt = function
  | None -> ()
  | Some s -> fprintf fmt "%s=\"%s\" " lab s

let rec save_goal fmt g =
  fprintf fmt "@\n@[<v 1><goal name=\"%s\" %asum=\"%s\" proved=\"%b\" expanded=\"%b\">"
    g.goal_name (opt "expl") g.goal_expl g.checksum g.proved  g.goal_expanded;
  Hashtbl.iter (save_proof_attempt fmt) g.external_proofs;
  Hashtbl.iter (save_trans fmt) g.transformations;
  fprintf fmt "@]@\n</goal>"

and save_trans fmt _ t =
  fprintf fmt "@\n@[<v 1><transf name=\"%s\" proved=\"%b\" expanded=\"%b\">"
    t.transf.transformation_name t.transf_proved t.transf_expanded;
  List.iter (save_goal fmt) t.subgoals;
  fprintf fmt "@]@\n</transf>"

let save_theory fmt t =
  fprintf fmt "@\n@[<v 1><theory name=\"%s\" verified=\"%b\" expanded=\"%b\">"
    t.theory_name t.verified t.theory_expanded;
  List.iter (save_goal fmt) t.goals;
  fprintf fmt "@]@\n</theory>"

let save_file fmt f =
  fprintf fmt "@\n@[<v 1><file name=\"%s\" verified=\"%b\" expanded=\"%b\">" f.file_name f.file_verified f.file_expanded;
  List.iter (save_theory fmt) f.theories;
  fprintf fmt "@]@\n</file>"

let save fname =
  let ch = open_out fname in
  let fmt = formatter_of_out_channel ch in
  fprintf fmt "<?xml version=\"1.0\" encoding=\"UTF-8\"?>@\n";
  fprintf fmt "<!DOCTYPE why3session SYSTEM \"why3session.dtd\">@\n";
  fprintf fmt "@[<v 1><why3session name=\"%s\">" fname;
  List.iter (save_file fmt) (get_all_files());
  fprintf fmt "@]@\n</why3session>";
  fprintf fmt "@.";
  close_out ch

(************************)
(*     actions          *)
(************************)

let init_fun = ref (fun (_:O.key) (_:any) -> ())

let notify_fun = ref (fun (_:any) -> ())

let check_file_verified f =
  let b = List.for_all (fun t -> t.verified) f.theories in
  f.file_verified <- b;
  !notify_fun (File f)

let check_theory_proved t =
  let b = List.for_all (fun g -> g.proved) t.goals in
  t.verified <- b;
  !notify_fun (Theory t);
  check_file_verified t.theory_parent

let rec check_goal_proved g =
  let b1 = Hashtbl.fold
    (fun _ a acc -> acc ||
       not a.proof_obsolete &&
       match a.proof_state with
         | Done { Call_provers.pr_answer = Call_provers.Valid} -> true
         | _ -> false) g.external_proofs false
  in
  let b = Hashtbl.fold
    (fun _ t acc -> acc || t.transf_proved) g.transformations b1
  in
  g.proved <- b;
  !notify_fun (Goal g);
  match g.parent with
    | Parent_theory t -> check_theory_proved t
    | Parent_transf t -> check_transf_proved t

and check_transf_proved t =
  let b = List.for_all (fun g -> g.proved) t.subgoals in
  t.transf_proved <- b;
  !notify_fun (Transformation t);
  check_goal_proved t.parent_goal

let set_proof_state ~obsolete a res =
  a.proof_state <- res;
  a.proof_obsolete <- obsolete;
  !notify_fun (Proof_attempt a);
  check_goal_proved a.proof_goal

(*************************)
(*         Scheduler     *)
(*************************)


(* timeout handler *)

type timeout_action =
  | Check_prover of (proof_attempt_status -> unit) * Call_provers.prover_call
  | Any_timeout of (unit -> bool)

let maximum_running_proofs = ref 2
let running_proofs = ref []

let proof_attempts_queue = Queue.create ()

let timeout_handler_activated = ref false
let timeout_handler_running = ref false

let timeout_handler () =
  assert (not !timeout_handler_running);
  timeout_handler_running := true;
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
    [] !running_proofs
  in
  let l =
    if List.length l < !maximum_running_proofs then
      begin try
        let (callback,pre_call) = Queue.pop proof_attempts_queue in
        callback Running;
        let call = pre_call () in
        (Check_prover(callback,call))::l
      with Queue.Empty -> l
      end
    else l
  in
  running_proofs := l;
  let continue =
    match l with
      | [] ->
(*
          eprintf "Info: timeout_handler stopped@.";
*)
          false
      | _ -> true
  in
  timeout_handler_activated := continue;
  timeout_handler_running := false;
  continue


let run_timeout_handler () =
  if !timeout_handler_activated then () else
    begin
      timeout_handler_activated := true;
(*
      eprintf "Info: timeout_handler started@.";
*)
      O.timeout ~ms:100 timeout_handler
    end

let schedule_any_timeout callback =
  running_proofs := (Any_timeout callback) :: ! running_proofs;
  run_timeout_handler ()

(* idle handler *)


type action =
  | Action_proof_attempt of bool * int * int * in_channel option * string * Driver.driver *
    (proof_attempt_status -> unit) * Task.task
  | Action_delayed of (unit -> unit)

let actions_queue = Queue.create ()

let idle_handler_activated = ref false

let idle_handler () =
  try
    begin
      match Queue.pop actions_queue with
        | Action_proof_attempt(debug,timelimit,memlimit,old,command,driver,
                               callback,goal) ->
            callback Scheduled;
            if debug then
              Format.eprintf "Task for prover: %a@."
                (Driver.print_task driver) goal;
            let pre_call =
              Driver.prove_task ?old ~command ~timelimit ~memlimit driver goal
            in
            Queue.push (callback,pre_call) proof_attempts_queue;
            run_timeout_handler ()
        | Action_delayed callback -> callback ()
    end;
    true
  with Queue.Empty ->
    idle_handler_activated := false;
(*
    eprintf "Info: idle_handler stopped@.";
*)
    false

let run_idle_handler () =
  if !idle_handler_activated then () else
    begin
      idle_handler_activated := true;
(*
      eprintf "Info: idle_handler started@.";
*)
      O.idle idle_handler
    end

(* main scheduling functions *)

let schedule_proof_attempt ~debug ~timelimit ~memlimit ?old
    ~command ~driver ~callback goal =
  Queue.push
    (Action_proof_attempt(debug,timelimit,memlimit,old,command,driver,
                        callback,goal))
    actions_queue;
  run_idle_handler ()

let schedule_edition command callback =
  let precall =
    Call_provers.call_on_buffer ~command ~regexps:[] ~timeregexps:[]
      ~exitcodes:[(0,Call_provers.Unknown "")] ~filename:"" (Buffer.create 1)
  in
  callback Running;
  running_proofs := (Check_prover(callback, precall ())) :: !running_proofs;
  run_timeout_handler ()

let schedule_delayed_action callback =
  Queue.push (Action_delayed callback) actions_queue;
  run_idle_handler ()

let apply_transformation ~callback t task =
   match t.transformation with
    | Trans_one t ->
        callback [Trans.apply t task]
    | Trans_list t ->
        callback (Trans.apply t task)

let schedule_edit_proof ~debug:_ ~editor ~file ~driver ~callback goal =
  let old =
    if Sys.file_exists file
    then
      begin
        let backup = file ^ ".bak" in
        Sys.rename file backup;
        Some(open_in backup)
      end
    else None
  in
  let ch = open_out file in
  let fmt = formatter_of_out_channel ch in
  Driver.print_task ?old driver fmt goal;
  Util.option_iter close_in old;
  close_out ch;
  let command = editor ^ " \"" ^ file ^ "\"" in
  schedule_edition command callback


(*******************************)
(* explanations *)
(****************)


  let expl_regexp = Str.regexp "expl:\\(.*\\)"

  let rec get_labels f =
    (match f.Term.t_node with
      | Term.Tbinop(Term.Timplies,_,f) -> get_labels f
      | Term.Tquant(Term.Tforall,fq) ->
          let (_,_,f) = Term.t_open_quant fq in get_labels f
      | Term.Tlet(_,fb) ->
          let (_,f) = Term.t_open_bound fb in get_labels f
      | Term.Tcase(_,[fb]) ->
          let (_,f) = Term.t_open_branch fb in get_labels f
      | _ -> [])
    @ f.Term.t_label

  let get_explanation id fmla =
    let r = ref None in
(*
    let fl = Debug.lookup_flag "print_labels" in
    Debug.set_flag fl;
    Format.eprintf "searching expl in formula '%a'@." Pretty.print_fmla fmla;
*)
    List.iter
      (fun s ->
         if Str.string_match expl_regexp s 0 then
           begin
             let e = Str.matched_group 1 s in
(*
             Format.eprintf "found explanation: '%s'" e;
*)
             r := Some e
           end)
      (id.Ident.id_label @ get_labels fmla);
    !r


(**********************)
(*     check sum      *)
(**********************)

let task_checksum t =
  fprintf str_formatter "%a@." Pretty.print_task t;
  let s = flush_str_formatter () in
(*
  let tmp = Filename.temp_file "task" "out" in
  let c = open_out tmp in
  output_string c s;
  close_out c;
*)
  let sum = Digest.to_hex (Digest.string s) in
(*
  eprintf "task %s, sum = %s@." tmp sum;
*)
  sum



(******************************)
(* raw additions to the model *)
(******************************)

let raw_add_external_proof ~obsolete ~timelimit ~edit (g:goal) p result =
  let key = O.create ~parent:g.goal_key () in
  let a = { prover = p;
            proof_goal = g;
            proof_key = key;
            proof_obsolete = obsolete;
            proof_state = result;
            timelimit = timelimit;
            edited_as = edit;
          }
  in
  Hashtbl.add g.external_proofs (prover_id p) a;
  let any = Proof_attempt a in
  !init_fun key any;
  !notify_fun any;
  a


(* [raw_add_goal parent name expl sum t] adds a goal to the given parent
   DOES NOT record the new goal in its parent, thus this should not be exported
*)
let raw_add_goal parent name expl sum topt exp =
  let parent_key = match parent with
    | Parent_theory mth -> mth.theory_key
    | Parent_transf mtr -> mtr.transf_key
  in
  let key = O.create ~parent:parent_key () in
  let sum = match topt with
    | None -> sum
    | Some t -> task_checksum t
  in
  let goal = { goal_name = name;
               goal_expl = expl;
               parent = parent;
               task = topt ;
               checksum = sum;
               goal_key = key;
               external_proofs = Hashtbl.create 7;
               transformations = Hashtbl.create 3;
               proved = false;
               goal_expanded = exp;
             }
  in
  let any = Goal goal in
  !init_fun key any;
  !notify_fun any; (*useless ? *)
  goal


(* [raw_add_transformation g name adds a transformation to the given goal g
   Adds no subgoals, thus this should not be exported
*)
let raw_add_transformation g trans exp =
  let parent = g.goal_key in
  let key = O.create ~parent () in
  let tr = { transf = trans;
             parent_goal = g;
             transf_proved = false;
             transf_key = key;
             subgoals = [];
             transf_expanded = exp;
           }
  in
  Hashtbl.add g.transformations trans.transformation_name tr;
  let any = Transformation tr in
  !init_fun key any;
  !notify_fun any;
  tr

let raw_add_theory mfile thopt thname exp =
  let parent = mfile.file_key in
  let key = O.create ~parent () in
  let mth = { theory_name = thname;
              theory = thopt;
              theory_key = key;
              theory_parent = mfile;
              goals = [] ;
              verified = false;
              theory_expanded = exp;
            }
  in
  let any = Theory mth in
  !init_fun key any;
  !notify_fun any;
  mth



let add_theory mfile name th =
  let tasks = List.rev (Task.split_theory th None None) in
  let mth = raw_add_theory mfile (Some th) name true in
  let goals =
    List.fold_left
      (fun acc t ->
         let id = (Task.task_goal t).Decl.pr_name in
         let name = id.Ident.id_string in
         let expl = get_explanation id (Task.task_goal_fmla t) in
         let goal = raw_add_goal (Parent_theory mth) name expl "" (Some t) true in
         goal :: acc)
      []
      tasks
  in
  mth.goals <- List.rev goals;
  check_theory_proved mth;
  mth

let raw_add_file f exp =
  let key = O.create () in
  let mfile = { file_name = f;
                file_key = key;
                theories = [] ;
                file_verified = false;
                file_expanded = exp;
              }
  in
  all_files := !all_files @ [mfile];
  let any = File mfile in
  !init_fun key any;
  !notify_fun any;
  mfile

let current_env = ref None
let current_provers = ref Util.Mstr.empty
let project_dir = ref ""

let get_provers () = !current_provers

let read_file fn =
  let fn = Filename.concat !project_dir fn in
  let env = match !current_env with
    | None -> assert false | Some e -> e
  in
  let theories = Env.read_file env fn in
  let theories =
    Util.Mstr.fold
      (fun name th acc ->
         match th.Theory.th_name.Ident.id_loc with
           | Some l -> (l,name,th)::acc
           | None   -> (Loc.dummy_position,name,th)::acc)
      theories []
  in
  List.sort
    (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
    theories

let add_file f =
  let theories = read_file f in
  let mfile = raw_add_file f true in
  let mths =
    List.fold_left
      (fun acc (_,name,t) ->
         let mth = add_theory mfile name t in
         mth :: acc)
      [] theories
  in
  mfile.theories <- List.rev mths;
  check_file_verified mfile;
  !notify_fun (File mfile)



let file_exists fn =
  List.exists (fun f -> f.file_name = fn) !all_files





(**********************************)
(* reload a file                  *)
(**********************************)

let reload_proof obsolete goal pid old_a =
  let p = 
    try
      Detected_prover (Util.Mstr.find pid !current_provers)
    with Not_found ->
      eprintf
        "Warning: prover %s appears in database but is not installed.@."
        pid;
      (Undetected_prover pid)
  in
  let old_res = old_a.proof_state in
  let obsolete = obsolete || old_a.proof_obsolete in
  (* eprintf "proof_obsolete : %b@." obsolete; *)
  let a =
    raw_add_external_proof ~obsolete ~timelimit:old_a.timelimit
      ~edit:old_a.edited_as goal p old_res
  in
  !notify_fun (Goal a.proof_goal)

let rec reload_any_goal parent gid gname sum t old_goal goal_obsolete =
  let info = get_explanation gid (Task.task_goal_fmla t) in
  let exp = match old_goal with None -> true | Some g -> g.goal_expanded in
  let goal = raw_add_goal parent gname info sum (Some t) exp in
  goal.task <- Some t;
  begin
    match old_goal with
      | None -> ()
      | Some g ->
          Hashtbl.iter (reload_proof goal_obsolete goal) g.external_proofs;
          Hashtbl.iter (reload_trans goal_obsolete goal) g.transformations
  end;
  check_goal_proved goal;
  goal


and reload_trans  _goal_obsolete goal _ tr =
  let trname = tr.transf.transformation_name in
  let gname = goal.goal_name in
  eprintf "[Reload] transformation %s for goal %s @." trname gname;
  let mtr = raw_add_transformation goal tr.transf tr.transf_expanded in
  let old_subgoals =
    List.fold_left
      (fun acc g -> Util.Mstr.add g.checksum g acc)
      Util.Mstr.empty tr.subgoals
  in
  let callback subgoals =
    (* we have an ordered list of new subgoals

           subgoals = [g1; g2; g3; ...]

       and a map of old subgoals indexed by their checksum

           old_subgoals = [s1,h1 ; s2, h2 ; ... ]

       we first associate each new goals for which there is an old goal
       with the same checksum. E.g, imagine checksum of g2 is s1 :

       new_goals_map = [ (g1, None) ; (g2, Some h1) ; (g3, None) ; ]
       remaining = [ s2, h2 ; ... ]

    *)
    let new_goals_map,old_subgoals,_ =
      List.fold_left
        (fun (new_goals_map,old_subgoals,count) subtask ->
           let id = (Task.task_goal subtask).Decl.pr_name in
           let subgoal_name = gname ^ "." ^ (string_of_int count) in
           let sum = task_checksum subtask in
           let old_subgoal,old_subgoals =
             try
               let g = Util.Mstr.find sum old_subgoals in
               (* an old subgoal has the same checksum *)
(*
               eprintf "Merge phase 1: old goal '%s' -> new goal '%s'@."
                 g.goal_name subgoal_name;
*)
               (Some g, Util.Mstr.remove sum old_subgoals)
             with Not_found -> 
(*
               eprintf "Merge phase 1: no old goal -> new goal '%s'@."
                 subgoal_name;
*)
               (None,old_subgoals)
           in
           ((count,id,subgoal_name,subtask,sum,old_subgoal) :: new_goals_map,
            old_subgoals, count+1))
        ([],old_subgoals,1) subgoals
    in
    (* careful : new_goals is now in reverse order *)
    (* we now turn remaining back into a list in the same order as original *)
    let remaining =
      Util.Mstr.fold
        (fun _ g acc -> (g.goal_name,g)::acc)
        old_subgoals
        []
    in
    let remaining =
      List.sort (fun (s1,_) (s2,_) -> String.compare s1 s2) remaining
    in
    (* we now associate to each new goal which does not have an
       associated old goal yet to an old goal in the same order
       (arbitrary choice)

       new_new_goals_map = [ [ (g1, h2) ; (g2, h1) ; (g3, fresh) ; ]

    *)
    let rec associate_remaining_goals new_goals_map remaining acc =
      match new_goals_map with
        | [] -> 
(*
            eprintf "Merge phase 3: dropping %d old goals@."
              (List.length remaining);
*)
            acc
        | (_,id,subgoal_name,subtask,sum,old_subgoal)::new_rem ->
            let ((obsolete,old_goal,rem) : bool * goal option * (string * goal) list) =
              match old_subgoal with
                | Some _g -> 
(*
                    eprintf "Merge phase 2: old goal '%s' -> new goal '%s'@."
                      g.goal_name subgoal_name;
*)
                    (false,old_subgoal,remaining)
                | None ->
                    match remaining with
                      | [] -> 
(*
                          eprintf "Merge phase 2: no old goal -> new goal '%s'@."
                            subgoal_name;
*)
                          (false,None,[])
                      | (_goal_name,g) :: rem -> 
(*
                          eprintf "Merge phase 2: old goal '%s' -> new goal '%s'@."
                            g.goal_name subgoal_name;
*)
                          (true,Some g,rem)
            in
            associate_remaining_goals new_rem rem
              ((id,subgoal_name,sum,subtask,old_goal,obsolete)::acc)
    in
    let goals =
      associate_remaining_goals (List.rev new_goals_map) remaining []
    in
    let goals = List.fold_left
      (fun acc (id,subgoal_name,sum,subtask,old_g, subgoal_obsolete) ->
         let mg =
           reload_any_goal (Parent_transf mtr) id
             subgoal_name sum subtask old_g subgoal_obsolete
         in mg::acc)
      [] (List.rev goals)
    in
    mtr.subgoals <- (List.rev goals);
    check_transf_proved mtr
  in
  apply_transformation ~callback tr.transf (get_task goal)


(* reloads the task [t] in theory mth (named tname) *)
let reload_root_goal mth tname old_goals t : goal =
  let id = (Task.task_goal t).Decl.pr_name in
  let gname = id.Ident.id_string in
  let sum = task_checksum t in
  let old_goal, goal_obsolete =
    try
      let old_goal = Util.Mstr.find gname old_goals in
      let old_sum = old_goal.checksum in
      (Some old_goal,sum <> old_sum)
    with Not_found -> (None,false)
  in
  if goal_obsolete then
    eprintf "Goal %s.%s has changed@." tname gname;
  reload_any_goal (Parent_theory mth) id gname sum t old_goal goal_obsolete

(* reloads a theory *)
let reload_theory mfile old_theories (_,tname,th) =
  eprintf "[Reload] theory '%s'@."tname;
  let tasks = List.rev (Task.split_theory th None None) in
  let old_goals, old_exp =
    try
      let old_mth = Util.Mstr.find tname old_theories in
      old_mth.goals, old_mth.theory_expanded
    with Not_found -> [], true
  in
  let mth = raw_add_theory mfile (Some th) tname old_exp in
  let goalsmap = List.fold_left
    (fun goalsmap g -> Util.Mstr.add g.goal_name g goalsmap)
    Util.Mstr.empty old_goals
  in
  !notify_fun (Theory mth);
  let new_goals = List.fold_left
    (fun acc t ->
       let g = reload_root_goal mth tname goalsmap t in
       g::acc)
    [] tasks
  in
  mth.goals <- List.rev new_goals;
  check_theory_proved mth;
  mth


(* reloads a file *)
let reload_file mf theories =
  let new_mf = raw_add_file mf.file_name mf.file_expanded in
  let old_theories = List.fold_left
    (fun acc t -> Util.Mstr.add t.theory_name t acc)
    Util.Mstr.empty
    mf.theories
  in
  !notify_fun (File new_mf);
  let mths = List.fold_left
    (fun acc th -> reload_theory new_mf old_theories th :: acc)
    [] theories
  in
  new_mf.theories <- List.rev mths;
  check_file_verified new_mf


(* reloads all files *)
let reload_all () =
  let files = !all_files in
  let all_theories =
    List.map (fun mf ->
                eprintf "[Reload] file '%s'@." mf.file_name;
                (mf,read_file mf.file_name))
      files
  in
  all_files := [];
  O.reset ();
  List.iter (fun (mf,ths) -> reload_file mf ths) all_theories

(****************************)
(*     session opening      *)
(****************************)

let bool_attribute field r def =
  try
    match List.assoc field r.Xml.attributes with
      | "true" -> true
      | "false" -> false
      | _ -> assert false
  with Not_found -> def

let int_attribute field r def =
  try
    int_of_string (List.assoc field r.Xml.attributes)
  with Not_found | Invalid_argument _ -> def

let load_result r =
  match r.Xml.name with
    | "result" ->
        let status =
          try List.assoc "status" r.Xml.attributes
          with Not_found -> assert false
        in
        let answer =
          match status with
            | "valid" -> Call_provers.Valid
            | "invalid" -> Call_provers.Invalid
            | "unknown" -> Call_provers.Unknown ""
            | "timeout" -> Call_provers.Timeout
            | "failure" -> Call_provers.Failure ""
            | "highfailure" -> Call_provers.Failure ""
            | s ->
                eprintf "Session.load_result: unexpected status '%s'@."  s;
                assert false
        in
        let time =
          try float_of_string (List.assoc "time" r.Xml.attributes)
          with Not_found -> 0.0
        in
        Done {
          Call_provers.pr_answer = answer;
          Call_provers.pr_time = time;
          Call_provers.pr_output = "";
        }
    | "undone" -> Undone
    | s ->
        eprintf "Session.load_result: unexpected element '%s'@."  s;
        assert false


let rec load_goal ~env parent acc g =
  match g.Xml.name with
    | "goal" ->
        let gname =
          try List.assoc "name" g.Xml.attributes
          with Not_found -> assert false
        in
        let expl =
          try Some (List.assoc "expl" g.Xml.attributes)
          with Not_found -> None
        in
        let sum =
          try List.assoc "sum" g.Xml.attributes
          with Not_found -> ""
        in
        let exp = bool_attribute "expanded" g true in
        let mg = raw_add_goal parent gname expl sum None exp in
        List.iter (load_proof_or_transf ~env mg) g.Xml.elements;
        mg::acc
    | s ->
        eprintf "Session.load_goal: unexpected element '%s'@."  s;
        assert false


and load_proof_or_transf ~env mg a =
  match a.Xml.name with
    | "proof" ->
        let prover =
          try List.assoc "prover" a.Xml.attributes
          with Not_found -> assert false
        in
        let p =
          try
            Detected_prover (Util.Mstr.find prover !current_provers)
          with Not_found -> 
            Undetected_prover prover
        in
        let res = match a.Xml.elements with
          | [r] -> load_result r
          | [] -> Undone
          | _ -> assert false
        in
        let edit =
          try List.assoc "edited" a.Xml.attributes
          with Not_found -> assert false
        in
        let obsolete = bool_attribute "obsolete" a true in
        let timelimit = int_attribute "timelimit" a 10 in
        let (_ : proof_attempt) =
          raw_add_external_proof ~obsolete ~timelimit ~edit mg p res
        in
        (* already done by raw_add_external_proof
           Hashtbl.add mg.external_proofs prover pa *)
        ()
    | "transf" ->
        let trname =
          try List.assoc "name" a.Xml.attributes
          with Not_found -> assert false
        in
        let tr =
          try
            lookup_transformation env trname
          with Not_found -> assert false (* TODO *)
        in
        let _proved =
          try List.assoc "proved" a.Xml.attributes
          with Not_found -> assert false
        in
        let exp = bool_attribute "expanded" a true in
        let mtr = raw_add_transformation mg tr exp in
        mtr.subgoals <-
          List.rev
          (List.fold_left
             (load_goal ~env (Parent_transf mtr))
             [] a.Xml.elements);
        (* already done by raw_add_transformation
           Hashtbl.add mg.transformations trname mtr *)
        ()
    | s ->
        eprintf "Session.load_proof_or_transf: unexpected element '%s'@."  s;
        assert false

let load_theory ~env mf acc th =
  match th.Xml.name with
    | "theory" ->
        let thname =
          try List.assoc "name" th.Xml.attributes
          with Not_found -> assert false
        in
        let exp = bool_attribute "expanded" th true in
        let mth = raw_add_theory mf None thname exp in
        mth.goals <-
          List.rev
          (List.fold_left
             (load_goal ~env (Parent_theory mth))
             [] th.Xml.elements);
        mth::acc
    | s ->
        eprintf "Session.load_theory: unexpected element '%s'@."  s;
        assert false

let load_file ~env f =
  match f.Xml.name with
    | "file" ->
        let fn =
          try List.assoc "name" f.Xml.attributes
          with Not_found -> assert false
        in
        let exp = bool_attribute "expanded" f true in
        let mf = raw_add_file fn exp in
        mf.theories <-
          List.rev
          (List.fold_left (load_theory ~env mf) [] f.Xml.elements)
    | s ->
        eprintf "Session.load_file: unexpected element '%s'@."  s;
        assert false

let load_session ~env xml =
  let cont = xml.Xml.content in
  match cont.Xml.name with
    | "why3session" ->
        List.iter (load_file ~env) cont.Xml.elements
    | s ->
        eprintf "Session.load_session: unexpected element '%s'@."  s;
        assert false

let db_filename = "why3session.xml"

let open_session ~env ~config ~init ~notify dir =
  match !current_env with
    | None ->
        init_fun := init; notify_fun := notify;
        project_dir := dir; current_env := Some env;
        let provers = Whyconf.get_provers config in
        current_provers := 
          Util.Mstr.fold (get_prover_data env) provers Util.Mstr.empty;
        begin try
          let xml = Xml.from_file (Filename.concat dir db_filename) in
          load_session ~env xml;
          reload_all ()
        with
          | Sys_error _ ->
              (* xml does not exist yet *)
              ()
          | Xml.Parse_error s ->
              Format.eprintf "XML database corrupted, ignored (%s)@." s;
              ()
        end
    | _ ->
        eprintf "Session.open_session: session already opened@.";
        assert false

let save_session () =
  match !current_env with
    | Some _ ->
        let f = Filename.concat !project_dir db_filename in
        begin if Sys.file_exists f then
          let b = f ^ ".bak" in
          if Sys.file_exists b then Sys.remove b ; 
          Sys.rename f b
        end;
        save f
    | None ->
        eprintf "Session.save_session: no session opened@.";
        assert false

(*****************************************************)
(* method: run a given prover on each unproved goals *)
(*****************************************************)

let redo_external_proof ~timelimit g a =
  (* check that the state is not Scheduled or Running *)
  let running = match a.proof_state with
    | Scheduled | Running -> true
    | Done _ | Undone | InternalFailure _ -> false
  in
  if running then ()
    (* info_window `ERROR "Proof already in progress" *)
  else
    match a.prover with
      | Undetected_prover _ -> ()
      | Detected_prover p ->
          let callback result =
            set_proof_state ~obsolete:false a result;
          in
          let old = if a.edited_as = "" then None else
            begin
              let f = Filename.concat !project_dir a.edited_as in
              Format.eprintf "Info: proving using edited file %s@." f;
              (Some (open_in f))
            end
          in
          schedule_proof_attempt
            ~debug:false ~timelimit ~memlimit:0
            ?old ~command:p.command ~driver:p.driver
            ~callback
            (get_task g)

let rec prover_on_goal ~timelimit p g =
  let id = p.prover_id in
  let a =
    try Hashtbl.find g.external_proofs id
    with Not_found ->
      raw_add_external_proof ~obsolete:false ~timelimit ~edit:"" g 
        (Detected_prover p) Undone
  in
  let () = redo_external_proof ~timelimit g a in
  Hashtbl.iter
    (fun _ t -> List.iter (prover_on_goal ~timelimit p) t.subgoals)
    g.transformations

let rec prover_on_goal_or_children ~context_unproved_goals_only ~timelimit p g =
  if not (g.proved && context_unproved_goals_only) then
    begin
      let r = ref true in
      Hashtbl.iter
        (fun _ t ->
           r := false;
           List.iter (prover_on_goal_or_children
                        ~context_unproved_goals_only ~timelimit p)
             t.subgoals) g.transformations;
      if !r then prover_on_goal ~timelimit p g
    end

let run_prover ~context_unproved_goals_only ~timelimit pr a =
  match a with
    | Goal g ->
        prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr g
    | Theory th ->
        List.iter
          (prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr)
          th.goals
    | File file ->
        List.iter
          (fun th ->
             List.iter
               (prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr)
               th.goals)
          file.theories
    | Proof_attempt a ->
        prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr a.proof_goal
    | Transformation tr ->
        List.iter
          (prover_on_goal_or_children ~context_unproved_goals_only ~timelimit pr)
          tr.subgoals

(**********************************)
(* method: replay obsolete proofs *)
(**********************************)

let proof_successful a =
  match a.proof_state with
    | Done { Call_provers.pr_answer = Call_provers.Valid } -> true
    | _ -> false

let rec replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only g =
  Hashtbl.iter
    (fun _ a ->
       if not obsolete_only || a.proof_obsolete then
         if not context_unproved_goals_only || proof_successful a
         then redo_external_proof ~timelimit:a.timelimit g a)
    g.external_proofs;
  Hashtbl.iter
    (fun _ t ->
       List.iter
         (replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only)
         t.subgoals)
    g.transformations

let replay ~obsolete_only ~context_unproved_goals_only a =
  match a with
    | Goal g ->
        replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only g
    | Theory th ->
        List.iter
          (replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only)
          th.goals
    | File file ->
        List.iter
          (fun th ->
             List.iter
               (replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only)
               th.goals)
          file.theories
    | Proof_attempt a ->
        replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only a.proof_goal
    | Transformation tr ->
        List.iter
          (replay_on_goal_or_children ~obsolete_only ~context_unproved_goals_only)
          tr.subgoals

(***********************************)
(* method: mark proofs as obsolete *)
(***********************************)

let cancel_proof a = set_proof_state ~obsolete:true a a.proof_state

let rec cancel_goal_or_children g =
  Hashtbl.iter (fun _ a -> cancel_proof a) g.external_proofs;
  Hashtbl.iter
    (fun _ t -> List.iter cancel_goal_or_children t.subgoals)
    g.transformations

let cancel a =
  match a with
    | Goal g ->
        cancel_goal_or_children g
    | Theory th ->
        List.iter cancel_goal_or_children th.goals
    | File file ->
        List.iter
          (fun th -> List.iter cancel_goal_or_children th.goals)
          file.theories
    | Proof_attempt a ->
        cancel_goal_or_children a.proof_goal
    | Transformation tr ->
        List.iter cancel_goal_or_children tr.subgoals

(*********************************)
(* method: check existing proofs *)
(*********************************)

type report =
  | Wrong_result of Call_provers.prover_result * Call_provers.prover_result  
  | CallFailed of exn
  | Prover_not_installed 
  | No_former_result 

let reports = ref []

let push_report g p r =
  reports := (g.goal_name,p,r) :: !reports

let proofs_to_do = ref 0
let proofs_done = ref 0

let same_result r1 r2 =
  match r1.Call_provers.pr_answer, r2.Call_provers.pr_answer with
    | Call_provers.Valid, Call_provers.Valid -> true
    | Call_provers.Invalid, Call_provers.Invalid -> true
    | Call_provers.Timeout, Call_provers.Timeout -> true
    | Call_provers.Unknown _, Call_provers.Unknown _-> true
    | Call_provers.Failure _, Call_provers.Failure _-> true
    | _ -> false

let check_external_proof g a =
  (* check that the state is not Scheduled or Running *)
  let running = match a.proof_state with
    | Scheduled | Running -> true
    | Done _ | Undone | InternalFailure _ -> false
  in
  if running then ()
  else
    begin
      incr proofs_to_do;
      match a.prover with
        | Undetected_prover s ->
            push_report g s Prover_not_installed;
            incr proofs_done;
            set_proof_state ~obsolete:false a Undone
        | Detected_prover p ->
            let p_name = p.prover_name ^ " " ^ p.prover_version in
            let callback result =
              match result with
                | Scheduled | Running -> ()
                | Undone -> assert false
                | InternalFailure msg ->
                    push_report g p_name (CallFailed msg);
                    incr proofs_done;
                    set_proof_state ~obsolete:false a result
                | Done new_res ->
                    begin
                      match a.proof_state with
                        | Done old_res ->
                            if same_result old_res new_res then () else
                              push_report g p_name (Wrong_result(new_res,old_res))
                        | _ ->
                            push_report g p_name No_former_result
                    end;
                    incr proofs_done;
                    set_proof_state ~obsolete:false a result
          in
          let old = if a.edited_as = "" then None else
            begin
              let f = Filename.concat !project_dir a.edited_as in
              (* Format.eprintf "Info: proving using edited file %s@." f; *)
              (Some (open_in f))
            end
          in
          schedule_proof_attempt
            ~debug:false ~timelimit:a.timelimit ~memlimit:0
            ?old ~command:p.command ~driver:p.driver
            ~callback
            (get_task g)
    end

let rec check_goal_and_children g =
  Hashtbl.iter (fun _ a -> check_external_proof g a) g.external_proofs;
  Hashtbl.iter
    (fun _ t ->
       List.iter check_goal_and_children t.subgoals)
    g.transformations

let check_all ~callback =
  reports := [];
  proofs_to_do := 0;
  proofs_done := 0;
  List.iter
    (fun file ->
       List.iter
         (fun th -> List.iter check_goal_and_children th.goals)
         file.theories)
    !all_files;
  let timeout () =
    Printf.eprintf "Progress: %d/%d\r%!" !proofs_done !proofs_to_do;
    if !proofs_done = !proofs_to_do then 
      begin
        Printf.eprintf "\n%!";
        decr maximum_running_proofs;
        callback !reports; 
        false
      end
    else true
  in
  incr maximum_running_proofs;
  schedule_any_timeout timeout

(*****************************************************)
(* method: split selected goals *)
(*****************************************************)

let task_checksum t =
  fprintf str_formatter "%a@." Pretty.print_task t;
  let s = flush_str_formatter () in
(*
  let tmp = Filename.temp_file "task" "out" in
  let c = open_out tmp in
  output_string c s;
  close_out c;
*)
  let sum = Digest.to_hex (Digest.string s) in
(*
  eprintf "task %s, sum = %s@." tmp sum;
*)
  sum

let transformation_on_goal g tr =
    let callback subgoals =
      let b =
         match subgoals with
          | [task] ->
              (* let s1 = task_checksum (get_task g) in *)
              (* let s2 = task_checksum task in *)
              (* (\* *)
              (*   eprintf "Transformation returned only one task. sum before = %s, sum after = %s@." (task_checksum g.task) (task_checksum task); *)
              (*   eprintf "addresses: %x %x@." (Obj.magic g.task) (Obj.magic task); *)
              (* *\) *)
              (* s1 <> s2 *)
              not (Task.task_equal task (get_task g))
          | _ -> true
      in
      if b then
        let tr = raw_add_transformation g tr true in
        let goal_name = g.goal_name in
        let fold =
          fun (acc,count) subtask ->
            let id = (Task.task_goal subtask).Decl.pr_name in
            let expl =
              get_explanation id (Task.task_goal_fmla subtask)
            in
            let subgoal_name =
              goal_name ^ "." ^ (string_of_int count)
            in
            let goal =
              raw_add_goal (Parent_transf tr)
                subgoal_name expl "" (Some subtask) true
            in
            (goal :: acc, count+1)
        in
        let goals,_ =
          List.fold_left fold ([],1) subgoals
        in
        tr.subgoals <- List.rev goals
    in
    apply_transformation ~callback tr (get_task g)

let rec transform_goal_or_children ~context_unproved_goals_only tr g =
  if not (g.proved && context_unproved_goals_only) then
    begin
      let r = ref true in
      Hashtbl.iter
        (fun _ t ->
           r := false;
           List.iter
             (transform_goal_or_children ~context_unproved_goals_only tr)
             t.subgoals)
        g.transformations;
      if !r then
        schedule_delayed_action (fun () -> transformation_on_goal g tr)
    end


let transform ~context_unproved_goals_only tr a =
  let tr = transform_goal_or_children ~context_unproved_goals_only tr in
  match a with
    | Goal g -> tr g
    | Theory th -> List.iter tr th.goals
    | File file ->
        List.iter
          (fun th -> List.iter tr th.goals)
          file.theories
    | Proof_attempt a -> tr a.proof_goal
    | Transformation t -> List.iter tr t.subgoals



(*****************************)
(* method: edit current goal *)
(*****************************)


let ft_of_th th =
  (Filename.basename th.theory_parent.file_name,
   (*
     th.theory.Theory.th_name.Ident.id_string
   *)
   th.theory_name
  )

let rec ft_of_goal g =
  match g.parent with
    | Parent_transf tr -> ft_of_goal tr.parent_goal
    | Parent_theory th -> ft_of_th th

let ft_of_pa a =
  ft_of_goal a.proof_goal

let edit_proof ~default_editor ~project_dir a =
  (* check that the state is not Scheduled or Running *)
  let running = match a.proof_state with
    | Scheduled | Running -> true
    | Undone | Done _ | InternalFailure _ -> false
  in
  if running then ()
(*
    info_window `ERROR "Edition already in progress"
*)
  else
    match a.prover with
      | Undetected_prover _ -> ()
      | Detected_prover p ->
          let g = a.proof_goal in
          let t = (get_task g) in
          let driver = p.driver in
          let file =
            match a.edited_as with
              | "" ->
                  let (fn,tn) = ft_of_pa a in
                  let file = Driver.file_of_task driver
                    (Filename.concat project_dir fn) tn t
                  in
                  (* Uniquify the filename if it exists on disk *)
                  let i =
                    try String.rindex file '.'
                    with _ -> String.length file
                  in
                  let name = String.sub file 0 i in
                  let ext = String.sub file i (String.length file - i) in
                  let i = ref 1 in
                  while Sys.file_exists
                    (name ^ "_" ^ (string_of_int !i) ^ ext) do
                      incr i
                  done;
                  let file = name ^ "_" ^ (string_of_int !i) ^ ext in
                  let file = Sysutil.relativize_filename project_dir file in
                  a.edited_as <- file;
                  file
              | f -> f
          in
          let file = Filename.concat project_dir file in
          let callback res =
            match res with
              | Done _ ->
                  set_proof_state ~obsolete:false a Undone
              | _ ->
                  set_proof_state ~obsolete:false a res
          in
          let editor =
            match p.editor with
              | "" -> default_editor
              | s -> s
          in
          (*
            eprintf "[Editing] goal %s with command %s %s@." g.Decl.pr_name.id_string editor file;
          *)
          eprintf "[Editing] goal %s with command %s %s@." (Task.task_goal t).Decl.pr_name.Ident.id_string editor file;
          schedule_edit_proof ~debug:false ~editor
            ~file
            ~driver
            ~callback
            t

(*************)
(* removing  *)
(*************)

let remove_proof_attempt a =
  O.remove a.proof_key;
  let g = a.proof_goal in
  Hashtbl.remove g.external_proofs (prover_id a.prover);
  check_goal_proved g

let remove_transformation t =
  O.remove t.transf_key;
  let g = t.parent_goal in
  Hashtbl.remove g.transformations t.transf.transformation_name;
  check_goal_proved g

let rec clean_goal g =
  if g.proved then
    begin
      Hashtbl.iter
        (fun _ a ->
           if a.proof_obsolete || not (proof_successful a) then
             remove_proof_attempt a)
        g.external_proofs;
      Hashtbl.iter
        (fun _ t ->
           if not t.transf_proved then
             remove_transformation t
           else
             List.iter clean_goal t.subgoals)
        g.transformations
    end
  else
    Hashtbl.iter
      (fun _ t -> List.iter clean_goal t.subgoals)
      g.transformations


let clean a =
  match a with
    | Goal g -> clean_goal g
    | Theory th -> List.iter clean_goal th.goals
    | File file ->
        List.iter
          (fun th ->
             List.iter clean_goal th.goals)
          file.theories
    | Proof_attempt a ->
        clean_goal a.proof_goal
    | Transformation tr ->
        List.iter clean_goal tr.subgoals

end

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
