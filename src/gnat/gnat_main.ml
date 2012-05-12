open Why3
open Term
open Ident

type loc  = { file : string; line : int ; col : int }


type my_expl =
   { mutable loc : Gnat_expl.loc option ;
     mutable reason : Gnat_expl.reason option ;
     mutable subp : Gnat_expl.loc option }

type node_info =
   | Expl of Gnat_expl.expl
   | Sloc of Gnat_expl.loc
   | No_Info

let extract_explanation s =
   (* We start with an empty record; We fill it up by iterating over all labels
      of the node. If the record is entirely filled, we return it; otherwise we
      return "None" *)
   let b = { loc = None; reason = None; subp = None } in
   Slab.iter
     (fun x ->
        let s = x.lab_string in
        if Gnat_util.starts_with s "GP_" then
           match Util.colon_split s with
           | ["GP_Reason"; reason] ->
                 b.reason <- Some (Gnat_expl.reason_from_string reason)
           | ["GP_Subp"; file; line] ->
                 begin try
                    b.subp <-
                       Some (Gnat_expl.mk_loc_line file (int_of_string line))
                 with Failure "int_of_string" ->
                    Format.printf "GP_Subp: cannot parse string: %s" s;
                    Gnat_util.abort_with_message ""
                 end
           | "GP_Sloc" :: rest ->
                 begin try
                    b.loc <- Some (Gnat_expl.parse_loc rest)
                 with Failure "int_of_string" ->
                    Format.printf "GP_Sloc: cannot parse string: %s" s;
                    Gnat_util.abort_with_message ""
                 end
           | _ ->
                 Gnat_util.abort_with_message
                     "found malformed GNATprove label"
     ) s;
     (* We potentially need to rectify in the case of loop invariants: We need
        to check whether the VC is for initialization or preservation *)
     if b.reason = Some Gnat_expl.VC_Loop_Invariant then begin
        Slab.iter (fun x ->
           let s = x.lab_string in
           if Gnat_util.starts_with s "expl:" then
              if s = "expl:loop invariant init" then
                 b.reason <- Some Gnat_expl.VC_Loop_Invariant_Init
              else
                 b.reason <- Some Gnat_expl.VC_Loop_Invariant_Preserv) s
     end;
     match b with
     | { loc = Some sloc ; reason = Some reason; subp = Some subp } ->
           Expl (Gnat_expl.mk_expl reason sloc subp)
     | { loc = Some sloc ; reason = _; subp = _ } ->
           Sloc sloc
     | _ ->
           No_Info

type vc_info =
   { expl : Gnat_expl.expl option; trace : Gnat_expl.loc list }

let rec search_labels acc f =
   let acc =
      match extract_explanation f.t_label with
      | Expl e ->
            begin match acc.expl with
            | Some e_old ->
                  { expl = Some e;
                    trace = Gnat_expl.get_loc e_old :: acc.trace }
            | None -> { expl = Some e; trace = acc.trace }
            end
      | Sloc s -> { acc with trace = s :: acc.trace }
      | No_Info -> acc in
   match f.t_node with
   | Ttrue | Tfalse | Tconst _ | Tvar _ | Tapp _  -> acc
   | Tif (c,t1,t2) ->
         search_labels (search_labels (search_labels acc c) t1) t2
   | Tcase (c, tbl) ->
         List.fold_left (fun acc b ->
            let _, t = t_open_branch b in
            search_labels acc t) (search_labels acc c) tbl
   | Tnot t -> search_labels acc t
   | Tbinop (Timplies,t1,t2) ->
         search_labels (search_labels acc t1) t2
   | Tbinop (_,t1,t2) -> search_labels (search_labels acc t1) t2
   | Tlet (_,tb) | Teps tb ->
         let _, t = t_open_bound tb in
         search_labels acc t
   | Tquant (_,tq) ->
         let _,_,t = t_open_quant tq in
         search_labels acc t

let search_labels f =
   search_labels { expl = None; trace = [] } f

type key = int
type goal = key Session.goal

module GoalHash = struct
   type t = goal
   let equal a b = a.Session.goal_key = b.Session.goal_key
   let hash a = a.Session.goal_key
end
module GoalMap = Hashtbl.Make (GoalHash)

module GoalSet : sig
   type t
   val empty : unit -> t
   val is_empty : t -> bool
   val add : t -> goal -> unit
   val remove : t -> goal -> unit
   val choose : t -> goal
   val mem    : t -> goal -> bool
   val count  : t -> int
end =
struct
   type t = unit GoalMap.t

   let empty () = GoalMap.create 3
   let is_empty t = GoalMap.length t = 0
   let add t x = GoalMap.add t x ()
   let remove t x = GoalMap.remove t x
   let mem t x = GoalMap.mem t x
   let count t = GoalMap.length t

   exception Found of goal
   let choose t =
      try
         GoalMap.iter (fun k () -> raise (Found k)) t;
         raise Not_found
      with Found k -> k
end

module Objectives : sig
   val add_to_expl : Gnat_expl.expl -> goal -> Gnat_expl.loc list -> unit
   (* Mark goal for proof if in the requested target *)

   val add_expl         : Gnat_expl.expl -> unit
   val discharge        : goal -> GoalSet.t

   val set_not_interesting : goal -> unit
   val is_not_interesting : goal -> bool
   val is_interesting : goal -> bool

   val get_goals : Gnat_expl.expl -> GoalSet.t
   val get_objective : goal -> Gnat_expl.expl
   val get_trace : goal -> Gnat_expl.loc list

   val iter : (Gnat_expl.expl -> GoalSet.t -> unit) -> unit

   val stat : unit -> unit
   val get_num_goals : unit -> int
end = struct

   let nb_objectives = ref 0
   let nb_goals = ref 0

   let explmap : GoalSet.t Gnat_expl.HExpl.t = Gnat_expl.HExpl.create 17
   (* maps proof objectives to goals *)

   let goalmap : Gnat_expl.expl GoalMap.t = GoalMap.create 17
   (* maps goals to their objectives *)

   let tracemap : Gnat_expl.loc list GoalMap.t = GoalMap.create 17

   let get_goals expl = Gnat_expl.HExpl.find explmap expl
   let get_objective goal = GoalMap.find goalmap goal
   let get_trace goal = GoalMap.find tracemap goal

   let find e =
      try get_goals e
      with Not_found ->
         let r = GoalSet.empty () in
         Gnat_expl.HExpl.add explmap e r;
         incr nb_objectives;
         r

   let add_to_expl ex go trace_list =
      let filter =
         match Gnat_config.limit_line with
         | Some l -> Gnat_expl.equal_line l (Gnat_expl.get_loc ex)
         | None ->
             match Gnat_config.limit_subp with
             | None -> true
             | Some l -> Gnat_expl.equal_line l (Gnat_expl.get_subp_loc ex)
      in
      if filter then begin
         incr nb_goals;
         GoalMap.add goalmap go ex;
         let set = find ex in
         GoalSet.add set go;
         GoalMap.add tracemap go trace_list
      end

   let add_expl e = ignore (find e)

   let discharge goal =
      let expl = get_objective goal in
      let goalset = get_goals expl in
      GoalSet.remove goalset goal;
      goalset

   let not_interesting : GoalSet.t = GoalSet.empty ()
   let set_not_interesting x = GoalSet.add not_interesting x
   let is_not_interesting x = GoalSet.mem not_interesting x
   let is_interesting x = not (is_not_interesting x)

   let iter f = Gnat_expl.HExpl.iter f explmap

   let stat () =
      Format.printf "Obtained %d proof objectives and %d VCs@."
        !nb_objectives !nb_goals

   let get_num_goals () = !nb_goals
end

let print ?(endline=true) b expl =
   if endline then
      Format.printf "%a@." (Gnat_expl.print_expl b) expl
   else
      Format.printf "%a" (Gnat_expl.print_expl b) expl

let has_parent g =
  match g.Session.goal_parent with
  | Session.Parent_transf _ -> true
  | _ -> false

let count = ref 0

let keygen ?parent () =
   ignore (parent);
   incr count;
   !count

module Scheduler = Session_scheduler.Base_scheduler (struct end)
module Implem =
  struct

     type key = int

     let create = keygen

     let remove _ = ()

     let reset () = ()

     let notify _ = ()
     let init _ _ = ()
     let timeout ~ms x = Scheduler.timeout ~ms x
     let idle x    = Scheduler.idle x
     let notify_timer_state _ _ _= ()

     let uninstalled_prover _ _ = Whyconf.CPU_keep
  end

module M = Session_scheduler.Make (Implem)

let sched_state = M.init Gnat_config.parallel
let project_dir = Session.get_project_dir Gnat_config.filename

let env_session, is_new_session =
   let session, is_new_session =
      if Sys.file_exists project_dir then
         Session.read_session project_dir, false
      else
         Session.create_session project_dir, true in
   let env_session, (_:bool) =
      M.update_session ~allow_obsolete:true session Gnat_config.env
      Gnat_config.config in
   env_session, is_new_session

exception Not_Proven of Call_provers.prover_answer

let iter_main_goals fu =
   (* Main goals are at the following point in the theory:
        session -> file -> theory -> subgoal
                                     *here*
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
      | _ -> ()) env_session.Session.session

let iter_leaf_goals f =
   iter_main_goals (fun g ->
      Session.goal_iter (fun any ->
         match any with
         | Session.Transf t
            when t.Session.transf_name = Gnat_config.split_name ->
               Session.transf_iter (fun any ->
                  match any with
                  | Session.Goal g -> f g
                  | _ -> ()) t
         | _ -> ()) g)

let rec is_trivial_autogen fml =
   match fml.t_node with
   | Ttrue ->
         Slab.mem Gnat_config.autogen_label fml.t_label
   | Tquant (_,tq) ->
         let _,_,t = t_open_quant tq in
         is_trivial_autogen t
   | Tlet (_,tb) ->
         let _, t = t_open_bound tb in
         is_trivial_autogen t
   | Tbinop (Timplies,_,t2) ->
         is_trivial_autogen t2
   | Tcase (_,tbl) ->
         List.for_all (fun b ->
            let _, t = t_open_branch b in
            is_trivial_autogen t) tbl
   | _ ->
         false

let register_goal goal =
   let task = Session.goal_task goal in
   let fml = Task.task_goal_fmla task in
   match is_trivial_autogen fml, search_labels fml with
   | true, _ ->
         Objectives.set_not_interesting goal
   | _, { expl = None } ->
         Gnat_util.abort_with_message
         "Task has no tracability label."
   | _, { expl = Some e ; trace = l } ->
         Objectives.add_to_expl e goal l


let goal_has_been_tried g =
   try
      Session.goal_iter_proof_attempt
         (fun pa ->
            (* only count non-obsolete proof attempts with identical options *)
            if not pa.Session.proof_obsolete &&
               pa.Session.proof_prover = Gnat_config.prover.Whyconf.prover &&
               pa.Session.proof_timelimit = Gnat_config.timeout then
                  raise Exit
         ) g;
      false
   with Exit -> true

module Save_VCs : sig
   val save_vc : goal -> unit
   val save_trace : goal -> unit
end = struct

   let count_map : (int ref) Gnat_expl.HExpl.t = Gnat_expl.HExpl.create 17

   let find expl =
      try Gnat_expl.HExpl.find count_map expl
      with Not_found ->
         let r = ref 0 in
         Gnat_expl.HExpl.add count_map expl r;
         r

   let vc_name expl =
      let r = find expl in
      incr r;
      let n = !r in
      let base = Gnat_expl.to_filename expl in
      let suffix = ".why" in
      if n = 1 then base ^ suffix
      else base ^ "_" ^ string_of_int n ^ suffix

   let save_vc goal =
      let expl = Objectives.get_objective goal in
      let task = Session.goal_task goal in
      let dr = Gnat_config.prover_driver in
      let vc_fn = vc_name expl in
      let cout = open_out vc_fn in
      let fmt  = Format.formatter_of_out_channel cout in
      Driver.print_task dr fmt task;
      Format.printf "saved VC to %s@." vc_fn;
      close_out cout

   let save_trace goal =
      let expl = Objectives.get_objective goal in
      let fn = Gnat_expl.to_filename expl ^ ".trace" in
      let cout = open_out fn in
      let fmt  = Format.formatter_of_out_channel cout in
      List.iter (fun l ->
         Format.fprintf fmt "%a@." Gnat_expl.simple_print_loc
         (Gnat_expl.orig_loc l))
        (Objectives.get_trace goal);
      close_out cout

end

module Display_Progress : sig
  val set_num_goals : int -> unit
  val complete_goals : int -> unit
end = struct

  let total_num_goals = ref 0
  let current_num_goals = ref 0

  let set_num_goals num = total_num_goals := num

  let complete_goals num =
    if Gnat_config.ide_progress_bar then begin
      current_num_goals := !current_num_goals + num;
      Format.printf "completed %d out of %d (%d%%)...@."
        !current_num_goals !total_num_goals
        (!current_num_goals * 100 / !total_num_goals)
    end
end

let rec handle_vc_result goal result detailed =
   let remaining = Objectives.discharge goal in
   if result then begin
      Display_Progress.complete_goals 1;
      if GoalSet.is_empty remaining then begin
         match Gnat_config.report with
         | (Gnat_config.Verbose | Gnat_config.Detailed) ->
               print true (Objectives.get_objective goal)
         | _ -> ()
      end else begin
         schedule_goal (GoalSet.choose remaining)
      end
   end else begin
      Display_Progress.complete_goals (GoalSet.count remaining + 1);
      if Gnat_config.report = Gnat_config.Detailed && detailed <> None then
      begin
         let detailed =
            match detailed with None -> assert false | Some x -> x in
         print ~endline:false false (Objectives.get_objective goal);
         Format.printf " (%a)@." Call_provers.print_prover_answer detailed
      end else begin
         print false (Objectives.get_objective goal)
      end;
      Save_VCs.save_trace goal;
      Format.printf "%a@."
        (Driver.print_task Gnat_config.gnat_driver) (Session.goal_task goal)
   end

and interpret_result pa pas =
   match pas with
   | Session.Done r ->
         let goal = pa.Session.proof_parent in
         if (Objectives.is_interesting goal) then begin
            let answer = r.Call_provers.pr_answer in
            if answer = Call_provers.HighFailure then begin
               Format.eprintf "An error occured when calling alt-ergo:@.";
               Format.eprintf "%s@." r.Call_provers.pr_output;
            end;
            handle_vc_result goal (answer = Call_provers.Valid) (Some answer)
         end
   | _ -> ()


and schedule_goal g =
   (* first deal with command line options *)
   if Gnat_config.debug then
      Save_VCs.save_vc g;
   if Gnat_config.force then
      actually_schedule_goal g
   else
      (* then implement reproving logic *)
      begin
      (* Maybe the goal is already proved *)
      if g.Session.goal_verified then begin
         handle_vc_result g true None
      (* Maybe there was a previous proof attempt with identical parameters *)
      end else if goal_has_been_tried g then begin
         (* the proof attempt was necessarily false *)
         handle_vc_result g false None
      end else begin
         actually_schedule_goal g
      end;
   end

and actually_schedule_goal g =
   M.prover_on_goal env_session sched_state
     ~callback:interpret_result
     ~timelimit:Gnat_config.timeout
     ~memlimit:0
     Gnat_config.prover.Whyconf.prover g

let apply_split_goal_if_needed g =
   if Session.PHstr.mem g.Session.goal_transformations Gnat_config.split_name
   then ()
   else
      ignore
        (Session.add_registered_transformation
           ~keygen env_session Gnat_config.split_name g)

let has_file session =
   try
      Session.session_iter (fun any ->
         match any with
         | Session.File _ -> raise Exit
         | _ -> ()) session.Session.session;
      false
   with Exit -> true

let _ =
   try
      if is_new_session || not (has_file env_session) then begin
         (* This is a brand new session, simply apply the transformation
            "split_goal" to the entire file *)
         let file = M.add_file env_session
           (Sysutil.relativize_filename project_dir Gnat_config.filename) in
         M.transform env_session sched_state ~context_unproved_goals_only:false
         Gnat_config.split_name (Session.File file)
      end else begin
         iter_main_goals apply_split_goal_if_needed
      end;
      (* apply transformation *)
      Scheduler.main_loop ();
      iter_leaf_goals register_goal;
      if Gnat_config.verbose then begin
         Objectives.stat ()
      end;
      Display_Progress.set_num_goals (Objectives.get_num_goals ());
      Objectives.iter (fun _ goalset -> schedule_goal (GoalSet.choose goalset));
      Scheduler.main_loop ();
      Session.save_session Gnat_config.config env_session.Session.session
    with e when not (Debug.test_flag Debug.stack_trace) ->
       Format.eprintf "%a.@." Exn_printer.exn_printer e;
       Gnat_util.abort_with_message ""
