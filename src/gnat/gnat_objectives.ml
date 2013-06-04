open Why3

type key = int
(* The key type, with which we identify nodes in the Why3 VC tree *)

module Keygen : sig
   (* A small module that provides a trivial key generator for the session tree
    *)
   val keygen : ?parent:'a -> unit -> key
end = struct

   let count = ref 0

   let keygen ?parent () =
      ignore (parent);
      incr count;
      !count
end


type goal = key Session.goal
(* the type of goals; a goal is an elementary VC *)

type subp = goal

type objective = Gnat_expl.expl
(* an objective is identified by its explanation, which contains the source
   location and the kind of the check *)

type trace = Gnat_loc.loc list

type status =
   | Proved
   | Not_Proved
   | Work_Left

(* the session variable, it is initialized later on *)
let my_session : key Session.env_session option ref = ref None
let get_session () =
   match !my_session with
   | Some s -> s
   | None -> assert false

module GoalHash = struct
   (* module to provide hashing and fast equality on goals *)
   type t = goal
   let equal a b = a.Session.goal_key = b.Session.goal_key
   let hash a = a.Session.goal_key
end
module GoalMap = Hashtbl.Make (GoalHash)
(* module to provide a mutable map on goals *)

module GoalSet : sig
   (* module to provide mutable sets on goals *)
   type t
   val empty : unit -> t
   val is_empty : t -> bool
   val add : t -> goal -> unit
   val remove : t -> goal -> unit
   val choose : t -> goal
   val mem    : t -> goal -> bool
   val count  : t -> int
   val reset : t -> unit
end =
struct
   type t = unit GoalMap.t

   let empty () = GoalMap.create 17
   let is_empty t = GoalMap.length t = 0
   let add t x = GoalMap.add t x ()
   let remove t x = GoalMap.remove t x
   let mem t x = GoalMap.mem t x
   let count t = GoalMap.length t
   let reset t = GoalMap.clear t
   let iter f t = GoalMap.iter (fun k () -> f k) t

   exception Found of goal
   let choose t =
      try
         iter (fun k -> raise (Found k)) t;
         raise Not_found
      with Found k -> k
end

type objective_rec =
   { to_be_scheduled : GoalSet.t;
     to_be_proved    : GoalSet.t
   }
(* an objective consists of to be scheduled and to be proved goals *)

let empty_objective () =
   { to_be_scheduled = GoalSet.empty ();
     to_be_proved    = GoalSet.empty ()
   }

(* The state of the module consists of these mutable structures *)
let explmap : objective_rec Gnat_expl.HExpl.t = Gnat_expl.HExpl.create 17
(* maps proof objectives to goals *)

let goalmap : Gnat_expl.expl GoalMap.t = GoalMap.create 17
(* maps goals to their objectives *)

let total_nb_goals : int ref = ref 0
let nb_objectives : int ref = ref 0
let nb_goals_done : int ref = ref 0

let not_interesting : GoalSet.t = GoalSet.empty ()

let clear () =
   Gnat_expl.HExpl.clear explmap;
   GoalMap.clear goalmap;
   GoalSet.reset not_interesting;
   total_nb_goals := 0;
   nb_objectives := 0;
   nb_goals_done  := 0

let find e =
   try Gnat_expl.HExpl.find explmap e
   with Not_found ->
      let r = empty_objective () in
      Gnat_expl.HExpl.add explmap e r;
      incr nb_objectives;
      r

let add_to_objective ex go =
   let filter =
      match Gnat_config.limit_line with
      | Some l -> Gnat_loc.equal_line l (Gnat_expl.get_loc ex)
      | None -> true
   in
   if filter then begin
      incr total_nb_goals;
      GoalMap.add goalmap go ex;
      let obj = find ex in
      GoalSet.add obj.to_be_scheduled go;
      GoalSet.add obj.to_be_proved go;
   end

let add_objective e = ignore (find e)

let get_objective goal = GoalMap.find goalmap goal

let add_clone derive goal =
   let obj = get_objective derive in
   add_to_objective obj goal

let set_not_interesting x = GoalSet.add not_interesting x
let is_not_interesting x = GoalSet.mem not_interesting x
let is_interesting x = not (is_not_interesting x)

let next objective =
   (* this lookup should always succeed, otherwise it would mean we have a
      corrupt database *)
   let obj_rec = Gnat_expl.HExpl.find explmap objective in
   try
      (* the [choose] can fail however, in that case we want to return
         [None] *)
      let goal = GoalSet.choose obj_rec.to_be_scheduled in
      GoalSet.remove obj_rec.to_be_scheduled goal;
      Some goal
   with Not_found ->
      None

let strategy =
  "split_goal" ::
  (if Gnat_config.proof_mode = Gnat_config.No_Split then
    []
  else
  [
    Gnat_split_conj.split_conj_name;
    Gnat_split_disj.split_disj_name
  ])

let parent_transform_name goal =
   match goal.Session.goal_parent with
   | Session.Parent_transf t -> Some t.Session.transf_name
   | _ -> None

let rev_strategy = List.rev strategy

let last_transform = List.hd rev_strategy

let next_transform =
  let h = Hashtbl.create 17 in
  let rec fill before l =
    match l with
    | [] -> ()
    | x::rest ->
        Hashtbl.add h before x;
        fill x rest
  in
  let _ =
    match strategy with
    | [] -> assert false
    | head::tail -> fill head tail
  in
  (fun trans -> Hashtbl.find h trans)

let find_next_transformation goal =
  match parent_transform_name goal with
  | None -> List.hd strategy
  | Some s ->
      try next_transform s
      with Not_found ->
        Gnat_util.abort_with_message "unknown transformation found"

let is_full_split_goal goal =
   (* check whether the goal has been obtained by the last transformation in
      the transformation list *)
   match parent_transform_name goal with
   | Some name when name = last_transform -> true
   | _ -> false

let has_already_been_applied trans goal =
   (* check whether the goal has already been split by the given
      transformation *)
   Session.PHstr.mem goal.Session.goal_transformations trans

let further_split goal =
   (* check which was the last transformation applied to the goal and
      apply the next one on the list. Note that this may have already been done
      in a previous session, in which case we simply return the underlying
      goals. If it hasn't been done yet, we apply the transformation. If not
      more than one new goal is obtained this way, we move to the next
      transformation in the strategy list. If that still doesn't help, we
      return the empty list. *)
   let rec split trans =
     if has_already_been_applied trans goal then
         let transf =
            Session.PHstr.find goal.Session.goal_transformations trans in
           transf.Session.transf_goals
     else
         let transf =
            Session.add_registered_transformation
              ~keygen:Keygen.keygen
              (get_session ())
              trans
              goal in
         let new_goals = transf.Session.transf_goals in
         if List.length new_goals > 1 then begin
           new_goals
         end else begin
            Session.remove_transformation transf;
            try
              let trans' = next_transform trans in
              split trans'
            with Not_found -> []
         end
   in
   split (find_next_transformation goal)


let why3_says_goal_is_verified goal =
   (* this is a partial check to verify that gnatwhy3 and why3 agree. We only
      check that Why3 says that the goal is verified (all subgoals proved),
      however this does *not* correspond to an objective. *)
   let main_goal =
      if is_full_split_goal goal then
         match goal.Session.goal_parent with
         | Session.Parent_theory _ | Session.Parent_metas _ -> assert false
         | Session.Parent_transf t -> t.Session.transf_parent
      else
         goal
   in
   main_goal.Session.goal_verified

let register_result goal result =
   let obj = get_objective goal in
   let obj_rec = Gnat_expl.HExpl.find explmap obj in
   incr nb_goals_done;
   if result then begin
      (* goal has been proved, we only need to store that info *)
      GoalSet.remove obj_rec.to_be_proved goal;
      if GoalSet.is_empty obj_rec.to_be_proved then begin
         obj, Proved
      end else begin
         obj, Work_Left
      end
   end else begin try
         (* the goal was not proved.
            We first check whether we can simplify the goal. *)
         if is_full_split_goal goal then raise Exit;
         let new_goals = further_split goal in
         if new_goals = [] then raise Exit;
         (* if we are here, it means we have simplified the goal. We add the
            new goals to the set of goals to be proved/scheduled. *)
         List.iter (add_clone goal) new_goals;
         (* We also need to remove the old goal, which should be considered
            "replaced" by the new ones. Otherwise we would fail to report
            "Proved" even though all goals are proved. *)
         GoalSet.remove obj_rec.to_be_proved goal;
         obj, Work_Left
      with Exit ->
         (* if we cannot simplify, the objective has been disproved *)
         let n = GoalSet.count obj_rec.to_be_scheduled in
         GoalSet.reset obj_rec.to_be_scheduled;
         nb_goals_done := !nb_goals_done + n;
         obj, Not_Proved
   end

let objective_status obj =
   let obj_rec = Gnat_expl.HExpl.find explmap obj in
   if GoalSet.is_empty obj_rec.to_be_proved then
      Proved
   else if GoalSet.is_empty obj_rec.to_be_scheduled then
      Not_Proved
   else
      Work_Left


let iter f =
   let obj = Gnat_expl.HExpl.fold (fun k _ acc -> k :: acc) explmap [] in
   let obj = List.sort Gnat_expl.expl_compare obj in
   List.iter f obj

let get_num_goals () =
   !total_nb_goals

let get_num_goals_done () =
   !nb_goals_done

exception Found_Name of string

let extract_subp_name subp =
  (* given a top-level goal that corresponds to an Ada subprogram, extract the
     subprogram name *)
   let task = Session.goal_task subp in
   let goal_ident = (Task.task_goal task).Decl.pr_name in
   let label_set = goal_ident.Ident.id_label in
   try
     Ident.Slab.iter (fun lab ->
       let s = lab.Ident.lab_string in
       if Strings.starts_with s "GP_Pretty_Ada:" then
         raise (Found_Name (String.sub s 14 (String.length s - 14)))
       ) label_set;
     assert false (* There must always be a label *)
   with Found_Name s -> s

let stat subp =
   if Gnat_config.verbose <> Gnat_config.Quiet then begin
     let subp_name = extract_subp_name subp in
      Format.printf "analyzing %s, %d checks@." subp_name !nb_objectives
   end

module Base_Sched = Session_scheduler.Base_scheduler (struct end)
(* a simple scheduler provided by the Why3 library *)

module Scheduler =
   (* Simplify the base scheduler above, and provide the right interface for
    * the Session_scheduler functor *)
  struct

     type key = int

     let create = Keygen.keygen

     let remove _ = ()

     let reset () = ()

     let notify _ = ()
     let init _ _ = ()
     let timeout ~ms x = Base_Sched.timeout ~ms x
     let idle x    = Base_Sched.idle x
     let notify_timer_state _ _ _= ()

     let uninstalled_prover _ _ = Whyconf.CPU_keep

     let main_loop () = Base_Sched.main_loop ()
  end

module M = Session_scheduler.Make (Scheduler)
(* this is the module for interaction with the Why3 scheduler *)

let sched_state : M.t option ref = ref None
let get_sched_state () =
   match !sched_state with
   | Some s -> s
   | None -> assert false

let has_file session =
   (* Check whether the session has a file associated with it. Sessions without
      files can happen in strange cases (gnatwhy3 crashes in the wrong moment)
      *)
   try
      Session.session_iter (fun any ->
         match any with
         | Session.File _ -> raise Exit
         | _ -> ()) session.Session.session;
      false
   with Exit -> true


let iter_main_goals fu =
   (* Main goals are at the following point in the theory:
        session -> file -> theory -> subgoal
                                     *here*

      They correspond to program functions (one big goal for each program)
   *)
   Session.session_iter (fun any ->
      match any with
      | Session.File f ->
            Session.file_iter (fun any ->
               match any with
               | Session.Theory t ->
                     Session.theory_iter (fun any ->
                        match any with
                        | Session.Goal g ->
                              fu g
                        | _ -> ()) t
               | _ -> ()) f
      | _ -> ()) (get_session ()).Session.session

let iter_leafs f g =
      Session.goal_iter (fun any ->
         match any with
         | Session.Transf t
            when t.Session.transf_name = Gnat_config.split_name ->
               Session.transf_iter (fun any ->
                  match any with
                  | Session.Goal g -> f g
                  | _ -> ()) t
         | _ -> ()) g

let iter_leaf_goals ?subp f =
   (* Leaf goals are at the following point in the theory:
        session -> file -> theory -> subgoal -> transformation -> subgoal
                                                                  *here*
      A leaf goal corresponds to a "goal", ie a VC sent to Alt-Ergo
   *)
   match subp with
   | None -> iter_main_goals (iter_leafs f)
   | Some g -> iter_leafs f g

let goal_has_been_tried g =
   (* Check whether the goal has been tried already *)
   try
      Session.goal_iter (fun child ->
         match child with
         | Session.Proof_attempt pa ->
               (* only count non-obsolete proof attempts with identical
                  options *)
               if not pa.Session.proof_obsolete &&
               pa.Session.proof_prover = Gnat_config.prover.Whyconf.prover &&
               pa.Session.proof_timelimit = Gnat_config.timeout then
                  raise Exit
         | _ -> ()) g;
      false
   with Exit -> true

let apply_split_goal_if_needed g =
   (* before doing any proofs, we apply "split" to all "main goals" (see
      iter_main_goals). This function applies that transformation, but only
      when needed. *)
   if Session.PHstr.mem g.Session.goal_transformations Gnat_config.split_name
   then ()
   else
      ignore
        (Session.add_registered_transformation
           ~keygen:Keygen.keygen (get_session ()) Gnat_config.split_name g)

let schedule_goal callback g =
   (* actually schedule the goal, ie call the prover. This function returns
      immediately. *)
   M.prover_on_goal (get_session ()) (get_sched_state ())
     ~callback
     ~timelimit:Gnat_config.timeout
     ~memlimit:0
     Gnat_config.prover.Whyconf.prover g

let do_scheduled_jobs () =
   Scheduler.main_loop ()

let init_subp_vcs goal =
   apply_split_goal_if_needed goal;
   Scheduler.main_loop ()

let init () =
   sched_state := Some (M.init Gnat_config.parallel);
   let project_dir = Session.get_project_dir Gnat_config.filename in
   let env_session, is_new_session =
      (* either create a new session, or read an existing ession *)
      let session, is_new_session =
         if Sys.file_exists project_dir then
            Session.read_session project_dir, false
         else
            Session.create_session project_dir, true in
      let env_session, (_:bool) =
         M.update_session ~allow_obsolete:true session Gnat_config.env
         Gnat_config.config in
      env_session, is_new_session in
   my_session := Some env_session;
   if is_new_session || not (has_file env_session) then begin
      ignore (M.add_file env_session
        (Sysutil.relativize_filename project_dir Gnat_config.filename));
   end

let save_session () =
   Session.save_session Gnat_config.config (get_session ()).Session.session

let display_progress () =
   if Gnat_config.ide_progress_bar then begin
      Format.printf "completed %d out of %d (%d%%)...@."
      !nb_goals_done !total_nb_goals (!nb_goals_done * 100 / !total_nb_goals)
   end

exception Found of Gnat_loc.loc

let extract_sloc main_goal =
   let task = Session.goal_task main_goal in
   let goal_ident = (Task.task_goal task).Decl.pr_name in
   let label_set = goal_ident.Ident.id_label in
   try
      Ident.Slab.iter (fun lab ->
        match Gnat_expl.read_label lab.Ident.lab_string with
        | Some Gnat_expl.Gp_Subp loc -> raise (Found (loc))
        | _ -> ()
      ) label_set;
      assert false
   with Found l -> l

let compare_by_sloc g1 g2 =
   Gnat_loc.compare (extract_sloc g1) (extract_sloc g2)

let iter_subps f =
   let acc = ref [] in
   iter_main_goals (fun g -> acc := g :: !acc);
   let subps = List.sort compare_by_sloc !acc in
   List.iter f subps


let matches_subp_filter subp =
   match Gnat_config.limit_subp with
   | None -> true
   | Some lab ->
         let task = Session.goal_task subp in
         let goal_ident = (Task.task_goal task).Decl.pr_name in
         let label_set = goal_ident.Ident.id_label in
         Ident.Slab.mem lab label_set

module Save_VCs = struct

   let count_map : (int ref) Gnat_expl.HExpl.t = Gnat_expl.HExpl.create 17

   module GM = GoalMap

   let goal_map : string GM.t = GM.create 17

   let find expl =
      try Gnat_expl.HExpl.find count_map expl
      with Not_found ->
         let r = ref 0 in
         Gnat_expl.HExpl.add count_map expl r;
         r

   let vc_file goal =
      GM.find goal_map goal

   let with_fmt_channel filename f =
      let cout = open_out filename in
      let fmt  = Format.formatter_of_out_channel cout in
      f fmt;
      close_out cout

   let vc_name expl =
      let r = find expl in
      incr r;
      let n = !r in
      let base = Gnat_expl.to_filename expl in
      let suffix = ".why" in
      if n = 1 then base ^ suffix
      else base ^ "_" ^ string_of_int n ^ suffix

   let save_vc goal =
      let expl = get_objective goal in
      let task = Session.goal_task goal in
      let dr = Gnat_config.prover_driver in
      let vc_fn = vc_name expl in
      GM.add goal_map goal vc_fn;
      with_fmt_channel vc_fn (fun fmt -> Driver.print_task dr fmt task);
      Format.printf "saved VC to %s@." vc_fn

   let compute_trace =
     let rec compute_trace acc f =
       let acc = Term.t_fold compute_trace acc f in
       match Gnat_expl.extract_explanation f.Term.t_label with
       (* it should be enough to look at the "sloc"s here, and not take into
          account the explanations. *)
       | Gnat_expl.Sloc loc -> Gnat_loc.S.add loc acc
       | _ -> acc
     in
     fun goal ->
       let f = Task.task_goal_fmla (Session.goal_task goal) in
       compute_trace Gnat_loc.S.empty f

   let save_trace goal =
      let expl = get_objective goal in
      let base = Gnat_expl.to_filename ~goal expl in
      let trace = compute_trace goal in
      if not (Gnat_loc.S.is_empty trace) then begin
        let trace_fn = base ^ ".trace" in
        with_fmt_channel trace_fn (fun fmt ->
           Gnat_loc.S.iter (fun l ->
              Format.fprintf fmt "%a@." Gnat_loc.simple_print_loc
             (Gnat_loc.orig_loc l)) trace)
      end

end

let all_split_leaf_goals () =
   iter_leaf_goals (fun goal ->
      let is_registered =
         try ignore (get_objective goal); true
         with Not_found -> false in
      if is_registered then
         if is_full_split_goal goal then begin Save_VCs.save_vc goal end
         else begin
            let new_goals = further_split goal in
            if new_goals = [] then begin Save_VCs.save_vc goal end
            else begin
               List.iter (add_clone goal) new_goals;
               List.iter Save_VCs.save_vc new_goals
            end;
         end
      else ()
   )
