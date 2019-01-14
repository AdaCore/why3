open Why3
open Wstdlib

type goal_id = Session_itp.proofNodeID
(* This is the type of identifier of goal. They can be queried from the session
   through Session_itp functions *)

type subp =
  { subp_goal : goal_id;
    subp_entity : Gnat_expl.subp_entity
  }
(* This type stores the goal which corresponds to a subprogram (the whole
   correctness formula for a subp), together with the entity information which
   describes it *)

type objective = Gnat_expl.check
(* an objective is identified by its explanation, which contains the source
   location and the kind of the check *)

type status =
   | Proved
   | Not_Proved
   | Work_Left
   | Counter_Example

module GoalCmp = struct
   (* module to provide comparison goals *)
  type t = goal_id
  let compare a b = Pervasives.compare a b
end

module GoalMap = Session_itp.Hpn

module GoalSet =
struct
   (* We use an ordered set instead of a hashed set here so that we have
      predictable order of iteration. *)

   module S = Set.Make(GoalCmp)
   type t = S.t ref

   let empty () = ref S.empty
   let is_empty t = S.is_empty !t
   let add t x =
     t := S.add x !t
   let remove t x =
     t := S.remove x !t
   let mem t x =
     S.mem x !t
   let count t =
     S.cardinal !t
   let reset t =
     t := S.empty
   let iter f t =
     S.iter f !t
   let exists f t =
     S.exists f !t
   let for_all f t =
     S.for_all f !t

   exception Found of goal_id
   let choose t =
      try
         iter (fun k -> raise (Found k)) t;
         raise Not_found
      with Found k -> k
end

type objective_rec =
   { to_be_scheduled    : GoalSet.t;
     (* when a goal is scheduled, it is removed from this set *)
     to_be_proved       : GoalSet.t;
     (* when a goal is proved (or unproved), it is removed from this set *)
     toplevel           : GoalSet.t;
     (* the set of top-level goals, that is not obtained by transformation.
      * They are "entry points" of the objective into the Why3 session *)
     mutable not_proved : bool;
   (* when a goal is not proved, the objective is marked "not proved" by
    * setting this boolean to "true" *)
     mutable counter_example : bool;
   (* when a goal is not proved and a counterexample for the goal should
    * be got, the objective is marked "counterexample" by setting this
    * boolean to "true" *)
   }
(* an objective consists of to be scheduled and to be proved goals *)

let empty_objective () =
   { to_be_scheduled = GoalSet.empty ();
     to_be_proved    = GoalSet.empty ();
     toplevel        = GoalSet.empty ();
     not_proved      = false;
     counter_example = false
   }

(* The state of the module consists of these mutable structures *)
let explmap : objective_rec Gnat_expl.HCheck.t = Gnat_expl.HCheck.create 17
(* maps proof objectives to goals *)

let goalmap : Gnat_expl.check GoalMap.t = GoalMap.create 17
(* maps goals to their objectives *)

let total_nb_goals : int ref = ref 0
let nb_objectives : int ref = ref 0

let not_interesting : GoalSet.t = GoalSet.empty ()

let clear () =
   Gnat_expl.HCheck.clear explmap;
   GoalMap.clear goalmap;
   GoalSet.reset not_interesting;
   total_nb_goals := 0;
   nb_objectives := 0

let find e =
   try Gnat_expl.HCheck.find explmap e
   with Not_found ->
      let r = empty_objective () in
      Gnat_expl.HCheck.add explmap e r;
      incr nb_objectives;
      r

let add_to_objective ~toplevel ex go =
  (* add a goal to an objective.
   * A goal can be "top-level", that is a direct goal coming from WP, or not
   * top-level, that is obtained by transformation. *)
   let filter_line =
      match Gnat_config.limit_line with
      | Some (Gnat_config.Limit_Line l) ->
         Gnat_loc.equal_line l (Gnat_expl.get_loc ex)
      | Some (Gnat_config.Limit_Check c) ->
         (c.Gnat_expl.reason = Gnat_expl.get_reason ex)
         && (Gnat_loc.equal_orig_loc c.Gnat_expl.sloc (Gnat_expl.get_loc ex))
      | None -> true
   in
   let filter_region =
      match Gnat_config.limit_region with
      | Some r ->
         Gnat_loc.in_region r (Gnat_expl.get_loc ex)
      | None -> true
   in
   if filter_line && filter_region then begin
      incr total_nb_goals;
      GoalMap.add goalmap go ex;
      let obj = find ex in
      GoalSet.add obj.to_be_scheduled go;
      GoalSet.add obj.to_be_proved go;
      if toplevel then GoalSet.add obj.toplevel go;
   end

let get_objective goal = GoalMap.find goalmap goal

let add_clone derive goal =
   let obj = get_objective derive in
   add_to_objective ~toplevel:false obj goal


let add_to_objective = add_to_objective ~toplevel:true
(* we mask the add_to_objective function here and fix it's toplevel argument to
   "true", so that outside calls always set toplevel to true *)

let set_not_interesting x = GoalSet.add not_interesting x
let is_not_interesting x = GoalSet.mem not_interesting x
let is_interesting x = not (is_not_interesting x)

let next objective =
   (* this lookup should always succeed, otherwise it would mean we have a
      corrupt database *)
   let obj_rec = Gnat_expl.HCheck.find explmap objective in
   let rec build acc n =
     if n = 0 then acc
     else try
        (* the [choose] can fail however, in that case we want to return
           the goals found up to now *)
        let goal = GoalSet.choose obj_rec.to_be_scheduled in
        GoalSet.remove obj_rec.to_be_scheduled goal;
        build (goal :: acc) (n-1)
     with Not_found ->
        acc
   in
   build [] Gnat_config.parallel

let strategy =
  match Gnat_config.proof_mode with
  | Gnat_config.Per_Path -> ["path_split"; Gnat_split_conj.split_conj_name]
  | Gnat_config.Per_Check -> ["split_goal_wp_conj"]
  | _ ->
      ["split_goal_wp_conj";
       Gnat_split_disj.split_disj_name]

let parent_transform_name s goal =
   match Session_itp.get_proof_parent s goal with
   | Session_itp.Trans trid    -> Session_itp.get_transf_name s trid
   | Session_itp.Theory _theory -> assert false

let rev_strategy = List.rev strategy

let last_transform = List.hd rev_strategy

let first_transform = List.hd strategy

(* When provided with a starategy name, returns the successor in the list
   [strategy]. This is done by filling a local hashtable with key elements
   associated to their successor. raise Not_found when asked for successor
   of last transformation. *)
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

let get_first_transform_of_goal s (g: goal_id) : string =
  (* return a "random" (actually the first one) transformation that has been
     applied to the goal. If only gnatprove was run on this file, there is only
     one transformation. *)
  let subtransf = Session_itp.get_transformations s g in
  match subtransf with
  | [] -> assert false
  | hd :: _tl -> Session_itp.get_transf_name s hd

let find_next_transformation s (goal: goal_id) =
  (* the "then" branch corresponds to the "normal" case where only gnatprove
     was applied *)
  let subtransf = Session_itp.get_transformations s goal in
  if subtransf = [] then
    try next_transform (parent_transform_name s goal)
    with Not_found ->
      Gnat_util.abort_with_message ~internal:true
        "unknown transformation found"
  else
    (* in the other case, we just apply the transformation that's there *)
    get_first_transform_of_goal s goal

let is_full_split_goal ses (goal: goal_id) =
   (* check whether other transformations should be applied to the goal. If the
      transformation is part of the strategy, we check if it is the last one.
      Otherwise, the goal is fully split if there are no transformations
      applied to it (that we could follow) *)
  if not (Session_itp.get_transformations ses goal = []) then false
  else
    let tr_name = parent_transform_name ses goal in
    not (List.mem tr_name strategy) || tr_name = last_transform

let has_already_been_applied s trans (goal: goal_id) =
   (* check whether the goal has already been split by the given
      transformation *)
   List.exists (fun x -> Session_itp.get_transf_name s x = trans) (Session_itp.get_transformations s goal)

(* TODO get_project_dir is the one from Session. We should be able to not use it *)
let db_filename = "why3session.xml"

let get_project_dir fname =
  if not (Sys.file_exists fname) then raise Not_found;
  let d =
    if Sys.is_directory fname then fname
    else if Filename.basename fname = db_filename then begin
      Filename.dirname fname
    end
    else
      begin
        try Filename.chop_extension fname
        with Invalid_argument _ -> fname^".w3s"
      end
  in
  d

let get_session_dir () =
  let session_dir =
     let project_dir =
      try get_project_dir Gnat_config.filename
      with Not_found ->
      Gnat_util.abort_with_message ~internal:true
        (Pp.sprintf "could not compute session file for %s" Gnat_config.filename)
     in
     match Gnat_config.proof_dir with
     | None -> project_dir
     | Some dir_name ->
        Filename.concat (Filename.concat dir_name "sessions")
                        (Filename.basename project_dir) in
  session_dir

let has_file (session: Session_itp.session) =
   (* Check whether the session has a file associated with it. Sessions without
      files can happen in strange cases (gnatwhy3 crashes in the wrong moment)
      *)
   try
      Session_itp.Hfile.iter (fun _s -> raise Exit) (Session_itp.get_files session);
      false
   with Exit -> true

(* Initialization of why3server *)
let init () =
  if Gnat_config.stand_alone then begin
    Prove_client.connect_internal ();
    Unix.sleep 1
  end else
  Prove_client.connect_external Gnat_config.socket_name

(* This creates initializes and returns the controller. It also creates the
   session *)
let init_cont () =
  let session_dir = get_session_dir () in
  (* Shape version is always None for gnatwhy3 because we don't use shapes *)
  let is_new_session, (session, _shape_version) =
    if not Gnat_config.force && Sys.file_exists session_dir then
      false, Session_itp.load_session session_dir
    else begin
      if not (Sys.file_exists session_dir) then Unix.mkdir session_dir 0o700;
      true, (Session_itp.empty_session session_dir, None)
    end
  in
  let c = Controller_itp.create_controller Gnat_config.config Gnat_config.env session in
  if is_new_session || not (has_file session) then begin
    try
      Controller_itp.add_file c Gnat_config.filename
    with
    | Controller_itp.Errors_list l ->
        Gnat_util.abort_with_message ~internal:true
          (Pp.sprintf "could not add file %s to the session: %a"
             Gnat_config.filename (Pp.print_list Pp.space Exn_printer.exn_printer) l)
  end;

  (* Init why3server *)
  init ();
  if is_new_session then c
  else
    begin
      let ses = c.Controller_itp.controller_session in
       (* Filenames saved inside the session *)
      let file = ref None in
      let () = (* Find the file defined in the session *)
        let files = Session_itp.get_files ses in
        Session_itp.Hfile.iter (fun _ e ->
            if !file = None then file := Some e else
              Gnat_util.abort_with_message ~internal:true
                "Several files found in session")
          files
      in
      (* This is not possible that no file is found *)
      let file = (Opt.get !file) in
      let abs_file = Session_itp.system_path ses file in
      (if abs_file != Gnat_config.filename then
         (* rename_file takes absolute filenames *)
         let (_: string list * string list) =
           Session_itp.rename_file ses abs_file Gnat_config.filename in
         ());
      try
        let (_ : bool), (_ : bool) = Controller_itp.reload_files c ~shape_version:None in
        c
      with
      | Controller_itp.Errors_list l ->
        Gnat_util.abort_with_message ~internal:true
          (Pp.sprintf "could not reload files of the session: %a"
             (Pp.print_list Pp.space Exn_printer.exn_printer) l)
    end

let objective_status obj =
   let obj_rec = Gnat_expl.HCheck.find explmap obj in
   if obj_rec.counter_example then Counter_Example
   else if GoalSet.is_empty obj_rec.to_be_proved then
     if obj_rec.not_proved then Not_Proved else Proved
   else if GoalSet.is_empty obj_rec.to_be_scheduled then
      Not_Proved
   else
      Work_Left

let has_been_tried_by s (g: goal_id) (prover: Whyconf.prover) =
  (* Check whether the goal has been tried already *)
  let proof_attempt_set = Session_itp.get_proof_attempt_ids s g in
  try
    let paid = Whyconf.Hprover.find proof_attempt_set prover in
    let pa = Session_itp.get_proof_attempt_node s paid in
    (* only count non-obsolete proof attempts with identical
       options *)
    (not pa.Session_itp.proof_obsolete &&
    pa.Session_itp.limit =
      Gnat_config.limit ~prover:prover.Whyconf.prover_name ~warning:false)
  with Not_found -> false

let all_provers_tried s g =
  List.for_all (fun p -> has_been_tried_by s g p) Gnat_config.provers

(* iter_leafs is actually used after the application of gnat_split and it should
   only apply on direct children of transformations called gnat_split (or
   alternatively on the goal itself). *)
let iter_leafs s goal f =
  let tr_list = Session_itp.get_transformations s goal in
  (try
    let tr_gnat_split =
      List.find (fun x -> Session_itp.get_transf_name s x = first_transform)
                tr_list
    in
    let subsubgoals = Session_itp.get_sub_tasks s tr_gnat_split in
    List.iter (fun pn -> f (Session_itp.APn pn)) subsubgoals
  with Not_found -> ())

let iter_leaf_goals s subp f =
  let f x = match x with
  | Session_itp.APn pn -> f pn
  | _ -> () in
  iter_leafs s subp.subp_goal f

let iter f =
   let obj = Gnat_expl.HCheck.fold (fun k _ acc -> k :: acc) explmap [] in
   List.iter f obj

let unproved_vc_continue obj obj_rec =
  (* This function checks whether proof should continue even though we have an
     unproved VC. This function raises Exit when:
     * lazy mode is on (default)
     * no more VCs left
     otherwise it returns obj, Work_Left *)
  obj_rec.not_proved <- true;
  if Gnat_config.lazy_ then raise Exit;
  if GoalSet.is_empty obj_rec.to_be_proved then raise Exit;
  obj, Work_Left

(* This function only gets the subgoals of the gnat_split transformation. It is
   part of a code that should not be used when other transformations (manual
   proof) are applied. *)
let subsubgoals s (g: goal_id) =
  let transfs = Session_itp.get_transformations s g in
  try
    let tr =
      List.find (fun x -> List.mem (Session_itp.get_transf_name s x) strategy)
      transfs
    in
    Session_itp.get_sub_tasks s tr
  with
    Not_found -> []

(* Functor that takes a scheduler and provides functions to schedule
   transformations and proof attempts *)
module Make (S: Controller_itp.Scheduler) = struct

module C = Controller_itp.Make(S)

let further_split (c: Controller_itp.controller) (goal: goal_id) =
   (* check which was the last transformation applied to the goal and
      apply the next one on the list. Note that this may have already been done
      in a previous session, in which case we simply return the underlying
      goals. If it hasn't been done yet, we apply the transformation. If not
      more than one new goal is obtained this way, we move to the next
      transformation in the strategy list. If that still doesn't help, we
      return the empty list. *)
   let rec split trans =
     let s = c.Controller_itp.controller_session in
     if has_already_been_applied s trans goal then
       let _transf = List.find (fun x -> Session_itp.get_transf_name s x = trans)
         (Session_itp.get_transformations s goal) in
         ()
     else
       let callback tr_st =
         match tr_st with
         | Controller_itp.TSdone trid ->
           let new_goals =
             Session_itp.get_sub_tasks c.Controller_itp.controller_session trid in
           if List.length new_goals > 1 then begin
             () (*new_goals *)
           end else begin
              Controller_itp.remove_subtree c (Session_itp.ATn trid)
                 ~removed:(fun _ -> ()) ~notification:(fun _ -> ());
              (try
                let trans' = next_transform trans in
                split trans'
              with Not_found -> ())
           end
         | Controller_itp.TSscheduled  -> ()
         | Controller_itp.TSfailed _ -> ()
         | Controller_itp.TSfatal _ -> ()
       in
       (* Pass empty function for notification as there is no IDE to update *)
       C.schedule_transformation c goal trans [] ~callback:callback
         ~notification:(fun (_x) -> ())
   in
   split (find_next_transformation c.Controller_itp.controller_session goal)

let register_result c goal result : 'a * 'b =
   let obj = get_objective goal in
   let obj_rec = Gnat_expl.HCheck.find explmap obj in
   if obj_rec.counter_example then
     (* The prover run was scheduled just to get counterexample *)
     obj, Not_Proved
   else
     let warn = Gnat_expl.is_warning_reason (Gnat_expl.get_reason obj) in
     if not warn then begin
       (* We first remove the goal from the list of goals to be tried. It may be
        * put back later, see below *)
       GoalSet.remove obj_rec.to_be_proved goal;
       if result then
         (* goal has been proved, we only need to store that info *)
         if not (GoalSet.is_empty obj_rec.to_be_proved) then
           obj, Work_Left
         else
           if obj_rec.not_proved then
             obj, Not_Proved
           else obj, Proved
       else begin try
         (* the goal was not proved. *)
         (* We first check whether another prover may apply *)
         if Gnat_config.manual_prover = None &&
           not (all_provers_tried c.Controller_itp.controller_session goal) then begin
             (* put the goal back to be scheduled and proved *)
             GoalSet.add obj_rec.to_be_scheduled goal;
             GoalSet.add obj_rec.to_be_proved goal;
             obj, Work_Left
           end else begin
             (* This particular goal has been tried with all provers. But maybe
                we can split/apply transformations. *)
             if is_full_split_goal c.Controller_itp.controller_session goal then
               unproved_vc_continue obj obj_rec
             else
               let new_goals =
                 further_split c goal;
                 subsubgoals c.Controller_itp.controller_session goal
               in
               if new_goals = [] then unproved_vc_continue obj obj_rec
               else begin
                 (* if we are here, it means we have simplified the goal. We add the
                    new goals to the set of goals to be proved/scheduled. *)
                 List.iter (add_clone goal) new_goals;
                 obj, Work_Left
               end
           end
       with Exit ->
         (* if we cannot simplify, the objective has been disproved *)
         GoalSet.reset obj_rec.to_be_scheduled;

         if Gnat_config.counterexamples then begin
           (* The goal will be scheduled to get a counterexample *)
           obj_rec.not_proved <- true;
           obj_rec.counter_example <- true;
           GoalSet.add obj_rec.to_be_proved goal;
           (* The goal will be scheduled manually in Gnat_main.handle_result
              so it is not put to the obj_rec.to_be_scheduled *)
           obj, Counter_Example
         end else
           obj, Not_Proved
       end
     end
     else
       obj, (if result then Proved else Not_Proved)

let iter_main_goals s fu =
  (* Main goals are at the following point in the theory:
        session -> file -> theory -> subgoal
                                     *here*

      They correspond to program functions (one big goal for each program)
  *)
  let files = Session_itp.get_files s in
  let theories =
    Session_itp.Hfile.fold (fun _ (x:Session_itp.file) (acc: Session_itp.theory list) ->
                        (Session_itp.file_theories x) @ acc)
    files [] in
  (* We filter detached goals (they don't have task) *)
  let filter_detached goal =
    let goal = Session_itp.APn goal in
    not (Session_itp.is_detached s goal)
  in
  let main_goals =
    List.fold_left (fun acc th ->
        List.filter filter_detached (Session_itp.theory_goals th) @ acc)
      [] theories
  in
  List.iter fu main_goals

exception Prover_Found of Whyconf.prover

(* true if proof_attempt_node [pa] is valid and obsolete *)
let is_valid_and_obsolete pa =
  pa.Session_itp.proof_obsolete = true &&
  (match pa.Session_itp.proof_state with
  | Some pr when pr.Call_provers.pr_answer = Call_provers.Valid -> true
  | _ -> false)

let find_obsolete_valid_proof s g =
  (* if there is an obsolete valid proof of goal g with prover p, such that p
     is among the selected provers, return [Some p], otherwise return None *)
  let proof_attempts = Session_itp.get_proof_attempt_ids s g in
  try
    Whyconf.Hprover.iter (fun _k paid ->
      let pa = Session_itp.get_proof_attempt_node s paid in
      if is_valid_and_obsolete pa then
        begin
          match Gnat_config.is_selected_prover pa.Session_itp.prover with
          | Some p -> raise (Prover_Found p)
          | None -> ()
          end) proof_attempts;
    None
  with Prover_Found p -> Some p

let find_best_untried_prover s g =
  (* return the manual prover, if there is one. Otherwise, if an obsolete valid
     proof exists, try that prover first. Otherwise, just try the first not yet
     tried prover. *)
  match Gnat_config.manual_prover with
  | Some p -> p
  | None ->
      match find_obsolete_valid_proof s g with
      | Some p -> p
      | None ->
          List.find (fun p -> not (has_been_tried_by s g p)) Gnat_config.provers

exception Found_mem

(* Returns true if an elmeent of l satisfies f *)
let mem f l =
  try
    List.iter (fun x -> if f x then raise Found_mem) l; false
  with Found_mem -> true

let apply_split_goal_if_needed c g =
  (* before doing any proofs, we apply "split" to all "main goals" (see
     iter_main_goals). This function applies that transformation, but only
     when needed. *)
  let s = c.Controller_itp.controller_session in
  let transfs = Session_itp.get_transformations s g in
  let tr_found =
    mem (fun x -> let t = Session_itp.get_transf_name s x in t = first_transform) transfs
  in
  if tr_found then
    ()
  else
    C.schedule_transformation c g first_transform []
      ~callback:(fun _ -> ()) ~notification:(fun _ -> ())

exception Found_loc of Gnat_loc.loc

let extract_sloc (s: Session_itp.session) (main_goal: goal_id) =
   let task = Session_itp.get_task s main_goal in
   let goal_ident = (Task.task_goal task).Decl.pr_name in
   let attr_set = goal_ident.Ident.id_attrs in
   try
      Ident.Sattr.iter (fun attr ->
        match Gnat_expl.read_label attr.Ident.attr_string with
        | Some Gnat_expl.Gp_Subp loc -> raise (Found_loc loc)
        | _ -> ()
      ) attr_set;
      Gnat_util.abort_with_message ~internal:true
        (Pp.sprintf "could not find source location for subprogram %s"
        goal_ident.Ident.id_string)
   with Found_loc l -> l

let init_subp_vcs c subp =
  apply_split_goal_if_needed c subp.subp_goal

let save_session c =
   Session_itp.save_session c.Controller_itp.controller_session

let mk_subp_goal s goal =
  { subp_goal = goal;
    subp_entity = extract_sloc s goal
  }

let iter_subps c f =
   let s = c.Controller_itp.controller_session in
   let acc = ref [] in
   let _: unit =
     iter_main_goals s (fun g ->
       let task = Session_itp.get_task s g in
       if task = None then ()
       else acc := mk_subp_goal s g :: !acc) in
   List.iter f !acc

let matches_subp_filter s subp =
   match Gnat_config.limit_subp with
   | None -> true
   | Some attr ->
         let task = Session_itp.get_task s subp.subp_goal in
         let goal_ident = (Task.task_goal task).Decl.pr_name in
         let attr_set = goal_ident.Ident.id_attrs in
         Ident.Sattr.mem attr attr_set

module Save_VCs = struct

  exception Found of Whyconf.prover *  Call_provers.prover_result

  let find_successful_proof s goal =
  (* given a goal, find a successful proof attempt for exactly this goal (not
     counting transformations *)
    try
      Whyconf.Hprover.iter (fun prover paid ->
          let pa = Session_itp.get_proof_attempt_node s paid in
          match pa.Session_itp.proof_obsolete, pa.Session_itp.proof_state with
          | false, Some pr when pr.Call_provers.pr_answer = Call_provers.Valid ->
            raise (Found (prover, pr))
          | _ -> ()) (Session_itp.get_proof_attempt_ids s goal);
      raise Exit
    with Found (prover, pr) -> prover, pr

  let add_to_prover_stat pr stat =
  (* add the result of the prover run to the statistics record for some prover
  *)
    stat.Gnat_report.count <- stat.Gnat_report.count + 1;
    if pr.Call_provers.pr_time > stat.Gnat_report.max_time then
      stat.Gnat_report.max_time <- pr.Call_provers.pr_time;
    if pr.Call_provers.pr_steps > stat.Gnat_report.max_steps then
      stat.Gnat_report.max_steps <- pr.Call_provers.pr_steps

  (* TODO put this in Controller_itp *)
  let is_valid (c: Controller_itp.controller) goal =
    Session_itp.pn_proved c.Controller_itp.controller_session goal

  let add_to_stat prover pr stat =
    (* add the result pr of the prover run of "prover" to the statistics table *)
    if Whyconf.Hprover.mem stat prover then
      add_to_prover_stat pr (Whyconf.Hprover.find stat prover)
    else
      Whyconf.Hprover.add stat prover
        Gnat_report.{ count = 1;
                      max_time = pr.Call_provers.pr_time;
                      max_steps = pr.Call_provers.pr_steps }

  let rec extract_stat_goal c stat stat_transforms goal =
    (* Not obsolete and valid *)
    assert (is_valid c goal);
    let ses = c.Controller_itp.controller_session in
    try
      let prover, pr =
        find_successful_proof c.Controller_itp.controller_session goal in
      add_to_stat prover pr stat
    with Exit ->
    try
      List.iter
        (fun tnid ->
          if Session_itp.tn_proved c.Controller_itp.controller_session tnid then
            let subtasks = Session_itp.get_sub_tasks ses tnid in
            (* The transformation proved the goal *)
            if subtasks = [] then
              stat_transforms := !stat_transforms + 1
            else
              List.iter (extract_stat_goal c stat stat_transforms) subtasks;

          (* need to exit here so once we found a transformation that proves
           * the goal, don't try further *)
          raise Exit)
        (Session_itp.get_transformations ses goal);
    with Exit -> ()

  let extract_stats c (obj : objective) =
    (* Hold the stats for provers *)
    let stats = Whyconf.Hprover.create 5 in
    (* Hold the number of goals proved by a transformation. No timings
       information available. *)
    let stat_transforms = ref 0 in
    let obj_rec = Gnat_expl.HCheck.find explmap obj in
    GoalSet.iter (extract_stat_goal c stats stat_transforms) obj_rec.toplevel;
    (stats, !stat_transforms)

  let count_map : (int ref) Gnat_expl.HCheck.t = Gnat_expl.HCheck.create 17

  module GM = GoalMap

  let goal_map : string GM.t = GM.create 17

  let find check =
    try Gnat_expl.HCheck.find count_map check
    with Not_found ->
      let r = ref 0 in
      Gnat_expl.HCheck.add count_map check r;
      r

  let vc_file goal =
    GM.find goal_map goal

  let with_fmt_channel filename f =
    let cout = open_out filename in
    let fmt  = Format.formatter_of_out_channel cout in
    f fmt;
    close_out cout

  let vc_name check (dr: Driver.driver) =
    let r = find check in
    incr r;
    let n = !r in
    let count_str = if n = 1 then "" else string_of_int n in
    let ext = Driver.get_extension dr in
    Pp.sprintf "%a%s%s" Gnat_expl.to_filename check count_str ext

  let save_vc c goal (prover: Whyconf.prover) =
    let check = get_objective goal in
    let driver =
      snd (Whyconf.Hprover.find c.Controller_itp.controller_provers prover) in
    (* Reusing a filename to get several prover files with the same name is
       unsafe.
    *)
    let vc_fn = Sysutil.uniquify (vc_name check driver) in
    GM.add goal_map goal vc_fn;
    Sysutil.write_file vc_fn "";
    vc_fn

  let compute_trace s =
    let rec compute_trace acc f =
      let acc = Term.t_fold compute_trace acc f in
      match Gnat_expl.extract_sloc f.Term.t_attrs with
      (* it should be enough to look at the "sloc"s here, and not take into
         account the explanations. *)
      | Some loc -> Gnat_loc.S.add loc acc
      | _ -> acc
    in
    fun goal ->
      let task = Session_itp.get_task s goal in
      let f = Task.task_goal_fmla task in
      compute_trace Gnat_loc.S.empty f

  let save_trace s goal =
    let check = get_objective goal in
    let trace_fn = Pp.sprintf "%a.trace" Gnat_expl.to_filename check in
    let trace = compute_trace s goal in
    (* Do not generate an empty file if there is no location at all.
       Do not generate a file with a single location for the goal, as this
       is not useful. *)
    if Gnat_loc.S.cardinal trace > 1 then begin
      with_fmt_channel trace_fn
        (fun fmt ->
          Gnat_loc.S.iter (fun l ->
              Format.fprintf fmt "%a@." Gnat_loc.simple_print_loc
                (Gnat_loc.orig_loc l)) trace);
      (trace_fn, trace)
    end
    else ("", Gnat_loc.S.empty)

  (* Group of functions to build a json object for a session tree.
     More precisely a session forest, because we start with a list of
     goals for a given check. See gnat_report.mli for the JSON
     structure that we use here. *)
  let rec check_to_json session obj =
    let obj_rec = Gnat_expl.HCheck.find explmap obj in
    let l = ref [] in
    GoalSet.iter (fun x -> l := goal_to_json session x :: !l) obj_rec.toplevel;
    Json_base.List !l
  and goal_to_json session g =
    let s = Mstr.empty in
    Json_base.Record
      (Mstr.add "proof_attempts" (proof_attempts_to_json session g)
         (Mstr.add "transformations" (transformations_to_json session g) s))
  and proof_attempts_to_json session g =
    let s = Mstr.empty in
    let r = Whyconf.Hprover.fold
        (fun prover paid acc ->
           let pa = Session_itp.get_proof_attempt_node session paid in
           let pr_name = prover.Whyconf.prover_name in
           match pa.Session_itp.proof_obsolete, pa.Session_itp.proof_state with
           | false, Some pr ->
             Mstr.add pr_name (proof_result_to_json pr) acc
           | _, _ -> acc)
        (Session_itp.get_proof_attempt_ids session g) s in
    Json_base.Record r

  and proof_result_to_json r =
    let answer =
      Pp.sprintf "%a"
        Call_provers.print_prover_answer r.Call_provers.pr_answer in
    let s = Mstr.empty in
    let r =
      Mstr.add "time" (Json_base.Float r.Call_provers.pr_time)
        (Mstr.add "steps" (Json_base.Int r.Call_provers.pr_steps)
           (Mstr.add "result" (Json_base.String answer) s)) in
    Json_base.Record r
  and transformations_to_json session g =
    let map =
      List.fold_left (fun acc tfid ->
          let tf_name = Session_itp.get_transf_name session tfid in
          Mstr.add tf_name (transformation_to_json session tfid) acc)
        Mstr.empty
        (Session_itp.get_transformations session g)
    in
    Json_base.Record map
  and transformation_to_json session tf =
    let transf_goals = Session_itp.get_sub_tasks session tf in
    Json_base.List (List.map (goal_to_json session) transf_goals)

end

open Save_VCs

let run_goal ?save_to ?limit ~callback c prover g =
  (* spawn a prover and return immediately. The return value is a tuple of type
     Call_provers.prover_call * Session.goal. The next step of the program
     is now directly in the callback. *)
  let session = c.Controller_itp.controller_session in
  let config_prover = fst (Whyconf.Hprover.find c.Controller_itp.controller_provers prover) in
  let callback _x _t = callback _x _t in
  let notification _x = () in
  if config_prover.Whyconf.interactive then
    let old_paid =
      Whyconf.Hprover.find_opt
        (Session_itp.get_proof_attempt_ids session g)
        prover
    in
    let old_file =
      Opt.get_def None (Opt.map
        (fun x -> let pa_node = Session_itp.get_proof_attempt_node session x in
          pa_node.Session_itp.proof_script) old_paid)
    in
    begin
      match old_file with
      | None ->
        let check = get_objective g in
        let new_file = Gnat_manual.create_prover_file c g check prover in
        let _paid, _file, _ores = C.prepare_edition c ~file:new_file
          g prover ~notification in
        C.schedule_proof_attempt ?save_to ~limit:Call_provers.empty_limit
          c g prover ~callback ~notification
      | Some old_file ->
        let _paid, _file, _ores = C.prepare_edition c ~file:old_file
          g prover ~notification in
        C.schedule_proof_attempt ?save_to:None
          ~limit:Call_provers.empty_limit c g prover
          ~callback ~notification
    end
  else
    let check = get_objective g in
    let warn = Gnat_expl.is_warning_reason (Gnat_expl.get_reason check) in
    let limit =
      match limit with
(* TODO we should pass the type prover not a string here ? *)
      | None -> Gnat_config.limit ~prover:prover.Whyconf.prover_name ~warning:warn
      | Some x -> x in
    C.schedule_proof_attempt ?save_to ~limit ~callback ~notification c g prover

let goal_has_splits session (goal: goal_id) =
  let goal_transformations = Session_itp.get_transformations session goal in
  not ([] = goal_transformations)

let schedule_goal_with_prover ~callback c g p =
(* actually schedule the goal, i.e., call the prover. This function returns
   immediately. *)
  let save_to =
    if Gnat_config.debug || Gnat_config.debug_save_vcs then
      Some (save_vc c g p)
    else
      None
  in
  run_goal ?save_to ~callback c p g

let schedule_goal ~cntexample ~callback c g =
   (* actually schedule the goal, ie call the prover. This function returns
      immediately. *)
  let check = get_objective g in
  let warn = Gnat_expl.is_warning_reason (Gnat_expl.get_reason check) in
  let p = if warn then Opt.get (Gnat_config.prover_warn)
    else if cntexample then Opt.get (Gnat_config.prover_ce)
    else find_best_untried_prover c.Controller_itp.controller_session g in
  schedule_goal_with_prover ~callback c g p

let clean_automatic_proofs c =
  let seen = GoalSet.empty () in
  let s = c.Controller_itp.controller_session in
  (fun g ->
    if not (GoalSet.mem seen g) then begin
      GoalSet.add seen g;
      List.iter (fun prover ->
        Whyconf.Hprover.iter (fun _prover panid ->
          let pan = Session_itp.get_proof_attempt_node s panid in
          if not pan.Session_itp.proof_obsolete &&
            pan.Session_itp.prover = prover &&
            pan.Session_itp.limit =
              Gnat_config.limit ~prover:prover.Whyconf.prover_name ~warning:false
          then
            Controller_itp.remove_subtree c (Session_itp.APa panid)
              ~removed:(fun _ -> ()) ~notification:(fun _ -> ())
          else
            ())
          (Session_itp.get_proof_attempt_ids s g)) Gnat_config.provers
    end)



let all_split_leaf_goals () =
  assert false (* TODO *)
  (* ??? disabled for now *)
(*
  iter_main_goals (fun g ->
    iter_leafs g
     (fun goal ->
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
   ))
*)

let is_valid_not_ce session g =
  (* More efficient to first check if it is correct and only then check if it
     was not generated by a counterexample prover *)
  Session_itp.pn_proved session g &&
  let list_pa = Session_itp.get_proof_attempt_ids session g in
  let list_pa = Whyconf.Hprover.fold (fun _ pa l -> pa :: l) list_pa [] in
  let transformations_list = Session_itp.get_transformations session g in
  let b = List.exists (fun x -> (not (Gnat_config.is_ce_prover session x) &&
                       Session_itp.any_proved session (Session_itp.APa x)))
                       list_pa in
  let b' = List.exists (fun x -> Session_itp.tn_proved session x)
                       transformations_list in
  (b || b')

let session_proved_status c obj =
   let obj_rec = Gnat_expl.HCheck.find explmap obj in
   let session = c.Controller_itp.controller_session in
   GoalSet.for_all (fun x -> is_valid_not_ce session x) obj_rec.toplevel

let finished_but_not_valid_or_unedited pa =
  (* return true if the proof attempt in argument has terminated, but did not
     prove the goal. *)
  match pa.Session_itp.proof_state with
  | None -> false
  | Some pr ->
    begin
      match pr.Call_provers.pr_answer with
      | Call_provers.Valid -> false
      | _ -> true
    end

(* TODO replay *)
let is_valid_pa pa =
  match pa.Session_itp.proof_state with
  | Some pr when pr.Call_provers.pr_answer = Call_provers.Valid -> true
  | _ -> false

let remove_all_valid_ce_attempt s =
  Session_itp.fold_all_session s
    (fun () any ->
      match any with
      | Session_itp.APa paid ->
          let pa = Session_itp.get_proof_attempt_node s paid in
          if is_valid_pa pa && Gnat_config.is_ce_prover s paid then
            Session_itp.remove_subtree
              ~notification:(fun _ -> ()) ~removed:(fun _ -> ())
              s any
      | _ -> ()) ()


(* exception Goal_Found of goal *)
exception PA_Found of Session_itp.proofAttemptID

let is_most_appropriate_prover obj_rec prover =
  if obj_rec.counter_example then begin
    match Gnat_config.prover_ce with
    | Some p -> prover = p
    | _ -> true
  end else
    List.exists (fun p -> p = prover)
    Gnat_config.provers

let select_appropriate_proof_attempt obj_rec pa =
(* helper function that helps finding the most appropriate proof attempt. In
  the normal case, we want to have an unsuccessful proof attempt of the
  counter example prover. If a CE prover is not available, we want a proof
  attempt that corresponds to a selected prover. *)
  if pa.Session_itp.proof_obsolete then false
  else
    if obj_rec.counter_example then
      match Gnat_config.prover_ce with
      | Some p -> pa.Session_itp.prover = p
      | _ -> finished_but_not_valid_or_unedited pa &&
          is_most_appropriate_prover obj_rec pa.Session_itp.prover
    else
      finished_but_not_valid_or_unedited pa &&
      is_most_appropriate_prover obj_rec pa.Session_itp.prover

let session_find_unproved_pa c obj =
  let obj_rec = Gnat_expl.HCheck.find explmap obj in
  let session = c.Controller_itp.controller_session in
  let traversal_function () g =
    match g with
    | Session_itp.APn g ->
        if is_valid_not_ce c.Controller_itp.controller_session g then
          ()
        else
          let pa_ids_list = Session_itp.get_proof_attempt_ids session g in
          Whyconf.Hprover.iter (fun _ panid ->
            let pa = Session_itp.get_proof_attempt_node session panid in
            if select_appropriate_proof_attempt obj_rec pa then
              raise (PA_Found panid)) pa_ids_list
    | _ -> () in

  let iter_on_sub_goal g =
    Session_itp.fold_all_any session traversal_function () (Session_itp.APn g) in

  try
    GoalSet.iter iter_on_sub_goal obj_rec.toplevel;
    None
  with PA_Found p ->
    Some p

exception Found_goal_id of Session_itp.proofNodeID

let session_find_unproved_goal c obj =

  let obj_rec = Gnat_expl.HCheck.find explmap obj in
  let session = c.Controller_itp.controller_session in
  let traversal_function () g =
    match g with
    | Session_itp.APn g ->
        if not (Session_itp.pn_proved session g) then
          raise (Found_goal_id g)
    | _ -> () in

  let iter_on_sub_goal g =
    Session_itp.fold_all_any session traversal_function () (Session_itp.APn g) in

  try
    GoalSet.iter iter_on_sub_goal obj_rec.toplevel;
    None
  with Found_goal_id p ->
    Some p

let compute_replay_limit_from_pas pas =
  match pas with
  | { Call_provers.pr_steps = steps } ->
    let steps = steps + steps / 10 + 1 in
    { Call_provers.empty_limit with
      Call_provers.limit_steps = steps }

let for_some_proof_attempt pred map =
  try
    List.iter (fun pa -> if pred pa then raise Exit else ()) map;
    false
  with Exit -> true

let for_some_transformation pred map =
  try
    List.iter (fun tf -> if pred tf then raise Exit else ()) map;
    false
  with Exit -> true

let rec is_obsolete_verified session goal =
  (* Check if a goal is or was verified, including using obsolete proofs *)
  Session_itp.pn_proved session goal ||
  for_some_proof_attempt is_valid_pa (Session_itp.get_proof_attempts session goal) ||
    for_some_transformation
    (fun tf -> List.for_all (is_obsolete_verified session) (Session_itp.get_sub_tasks session tf))
    (Session_itp.get_transformations session goal)

let trans_is_obsolete_verified session tn =
  Session_itp.tn_proved session tn ||
  let sub_tasks = Session_itp.get_sub_tasks session tn in
  List.for_all (is_obsolete_verified session) sub_tasks

let rec replay_transf c tf =
  let session = c.Controller_itp.controller_session in
  if trans_is_obsolete_verified session tf then
    List.iter (replay_goal c) (Session_itp.get_sub_tasks session tf)
  else
    ()

and replay_goal c goal =
  let session = c.Controller_itp.controller_session in
  if not (is_obsolete_verified session goal) then ()
  else
    try
      (* first try to find a proof_attempt that proves this goal entirely. This
       * will raise PA_Found if such a PA is found. *)

(* TODO this should be in controller *)
      let proof_attempt_ids = Session_itp.get_proof_attempt_ids session goal in
      Whyconf.Hprover.iter (fun _ paid ->
        let pa = Session_itp.get_proof_attempt_node session paid in
        if is_valid_pa pa then raise (PA_Found paid)) proof_attempt_ids;
      (* we go here only if no such PA was found. We now replay the
         transformations *)

      let transforms = Session_itp.get_transformations session goal in
      List.iter (replay_transf c) transforms
    with PA_Found pa ->
      let pa_prover =
        (Session_itp.get_proof_attempt_node session pa).Session_itp.prover in
      let prover =
        try
          Some (List.find (fun p -> p = pa_prover) Gnat_config.provers)
        with Not_found ->
          Gnat_report.add_warning
          ("could not replay goal due to missing prover " ^
            pa_prover.Whyconf.prover_name);
          None in
      Opt.iter (fun prover ->
          let pa_node = Session_itp.get_proof_attempt_node session pa in
          let limit =
            match pa_node.Session_itp.proof_state with
            | Some pas when pas.Call_provers.pr_answer = Call_provers.Valid ->
                compute_replay_limit_from_pas pas
            | _ -> assert false in
          C.schedule_proof_attempt ?save_to:None c goal prover
            ~limit ~callback:(fun _ _ -> ())
            ~notification:(fun _ -> ())) prover


let replay_obj session obj =
  let obj_rec = Gnat_expl.HCheck.find explmap obj in
  GoalSet.iter (replay_goal session) obj_rec.toplevel

let replay session =
  iter (replay_obj session)

(* This register an observer that can monitor the number of provers
   scheduled/running/finished *)
let (_: unit) = C.register_observer (fun x y z ->
  if x = 0 && y = 0 && z = 0 then
    raise Exit)

end
