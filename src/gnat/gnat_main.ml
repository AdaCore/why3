open Why3
open Term

type vc_info =
   { expl : Gnat_expl.expl option; trace : Gnat_loc.loc list }
(* The VC information that has been found in a VC *)

let rec search_labels acc f =
   (* This function takes a VC formula, and returns the VC info found in that
      formula. The argument "acc" will be enriched at each node. *)
   let acc =
      match Gnat_expl.extract_explanation f.t_label with
      | Gnat_expl.Expl e ->
            begin match acc.expl with
            | Some e_old ->
                  { expl = Some e;
                    trace = Gnat_expl.get_loc e_old :: acc.trace }
            | None -> { expl = Some e; trace = acc.trace }
            end
      | Gnat_expl.Sloc s -> { acc with trace = s :: acc.trace }
      | Gnat_expl.No_Info -> acc in
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
   (* This is a wrapper around the previous function, with an empty vc_info as
      accumulator *)
   search_labels { expl = None; trace = [] } f

let print ?(endline=true) b task expl =
   (* Print a positive or negative message for objectives *)
   if endline then
      Format.printf "%a@." (Gnat_expl.print_expl b task) expl
   else
      Format.printf "%a" (Gnat_expl.print_expl b task) expl

let rec is_trivial fml =
   (* Check wether the formula is trivial.  *)
   match fml.t_node with
   | Ttrue -> true
   | Tquant (_,tq) ->
         let _,_,t = t_open_quant tq in
         is_trivial t
   | Tlet (_,tb) ->
         let _, t = t_open_bound tb in
         is_trivial t
   | Tbinop (Timplies,_,t2) ->
         is_trivial t2
   | Tcase (_,tbl) ->
         List.for_all (fun b ->
            let _, t = t_open_branch b in
            is_trivial t) tbl
   | _ -> false

let register_goal goal =
   (* Register the goal by extracting the explanation and trace. If the goal is
    * trivial, do not register *)
   let task = Session.goal_task goal in
   let fml = Task.task_goal_fmla task in
   match is_trivial fml, search_labels fml with
   | true, { expl = None } ->
         Gnat_objectives.set_not_interesting goal
   | _, { expl = None } ->
         Gnat_util.abort_with_message
         "Task has no tracability label."
   | _, { expl = Some e ; trace = l } ->
         Gnat_objectives.add_to_objective e goal l

module Save_VCs : sig
   (* Provide saving of VCs, traces *)

   val save_vc : Gnat_objectives.goal -> unit
   (* Save the goal to a file *)

   val save_trace : Gnat_objectives.goal -> unit
   (* save the trace to a file *)

   val vc_file : Gnat_objectives.goal -> string
   (* get the file name for a given goal *)
end = struct

   let count_map : (int ref) Gnat_expl.HExpl.t = Gnat_expl.HExpl.create 17

   module GM = Gnat_objectives.GoalMap

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
      let expl = Gnat_objectives.get_objective goal in
      let task = Session.goal_task goal in
      let dr = Gnat_config.prover_driver in
      let vc_fn = vc_name expl in
      GM.add goal_map goal vc_fn;
      with_fmt_channel vc_fn (fun fmt -> Driver.print_task dr fmt task);
      Format.printf "saved VC to %s@." vc_fn

   let save_trace goal =
      let expl = Gnat_objectives.get_objective goal in
      let base = Gnat_expl.to_filename expl in
      let trace_fn = base ^ ".trace" in
      with_fmt_channel trace_fn (fun fmt ->
         List.iter (fun l ->
            Format.fprintf fmt "%a@." Gnat_loc.simple_print_loc
           (Gnat_loc.orig_loc l))
      (Gnat_objectives.get_trace goal))

end

let is_full_split_goal goal =
   Session.PHstr.mem goal.Session.goal_transformations
      Gnat_split_conj.split_conj_name

let rec handle_vc_result goal result detailed =
   (* This function is called when the prover has returned from a VC.
       goal      is the VC that the prover has dealt with
       result    a boolean, true if the prover has proved the VC
       detailed  a boolean, true if detailed reports are requested
   *)
   let obj, status = Gnat_objectives.register_result goal result in
   Gnat_objectives.display_progress ();
   match status with
   | Gnat_objectives.Proved ->
         begin match Gnat_config.report with
         | (Gnat_config.Verbose | Gnat_config.Detailed) ->
               print true (Session.goal_task goal) obj
         | _ -> ()
         end
   | Gnat_objectives.Not_Proved ->
         if Gnat_config.report = Gnat_config.Detailed && detailed <> None then
         begin
            let detailed =
               match detailed with None -> assert false | Some x -> x in
            print ~endline:false false (Session.goal_task goal)
               (Gnat_objectives.get_objective goal);
            Format.printf " (%a)@." Call_provers.print_prover_answer detailed
         end else begin
            print false (Session.goal_task goal)
              (Gnat_objectives.get_objective goal)
         end;
         Save_VCs.save_trace goal
   | Gnat_objectives.Work_Left ->
         match Gnat_objectives.next obj with
         | Some g -> schedule_goal g
         | None -> ()

and interpret_result pa pas =
   (* callback function for the scheduler, here we filter if an interesting
      goal has been dealt with, and only then pass on to handle_vc_result *)
   match pas with
   | Session.Done r ->
         let goal = pa.Session.proof_parent in
         let answer = r.Call_provers.pr_answer in
         if answer = Call_provers.HighFailure then begin
            Format.eprintf "An error occured when calling alt-ergo@.";
            if Gnat_config.verbose then begin
               Format.eprintf "%s@." r.Call_provers.pr_output
            end;
         end;
         handle_vc_result goal (answer = Call_provers.Valid) (Some answer)
   | _ ->
         ()


and schedule_goal (g : Gnat_objectives.goal) =
   (* schedule a goal for proof - the goal may not be scheduled actually,
      because we detect that it is not necessary. This may have several
      reasons:
         * command line given to skip proofs
         * goal already proved
         * goal already attempted with identical options
   *)

   (* first deal with command line options *)
   if Gnat_config.debug then begin
      Save_VCs.save_vc g;
   end;
   if Gnat_config.force then
      actually_schedule_goal g
   else
      (* then implement reproving logic *)
      begin
      (* Maybe the goal is already proved *)
      if g.Session.goal_verified then begin
         handle_vc_result g true None
      (* Maybe there was a previous proof attempt with identical parameters *)
      end else if Gnat_objectives.goal_has_been_tried g then begin
         (* the proof attempt was necessarily false *)
         handle_vc_result g false None
      end else begin
         actually_schedule_goal g
      end;
   end

and actually_schedule_goal g =
   Gnat_objectives.schedule_goal interpret_result g

let _ =
   (* This is the main code. We read the file into the session if not already
      done, we apply the split_goal transformation when needed, and we schedule
      the first VC of all objectives. When done, we save the session.
   *)
   try
      Gnat_objectives.init ();
      Gnat_objectives.iter_leaf_goals register_goal;
      if Gnat_config.verbose then begin
         Gnat_objectives.stat ()
      end;
      Gnat_objectives.iter (fun obj ->
         if Gnat_objectives.objective_status obj =
            Gnat_objectives.Proved then begin
            Format.printf "%a@." Gnat_expl.print_simple_proven obj
         end else begin
            match Gnat_objectives.next obj with
            | Some g -> schedule_goal g
            | None -> ()
         end);
      Gnat_objectives.do_scheduled_jobs ();
      (* should do nothing *)
      Gnat_objectives.save_session ()
    with e when not (Debug.test_flag Debug.stack_trace) ->
       Format.eprintf "%a.@." Exn_printer.exn_printer e;
       Gnat_util.abort_with_message ""
