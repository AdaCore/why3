open Why3
open Term
open Ident

let rec extract_explanation expl gnat s =
   if Slab.is_empty s then expl, gnat
   else
      let x = Slab.choose s in
      let rest = Slab.remove x s in
      let x = to_string x in
      if Gnat_util.starts_with x "expl:" then
         let s = String.sub x 5 (String.length x - 5) in
         extract_explanation s gnat rest
      else if Gnat_util.starts_with x "gnatprove:" then
         let s = String.sub x 10 (String.length x - 10) in
         extract_explanation expl s rest
      else
         extract_explanation expl gnat rest

let rec search_labels acc f =
   if acc <> None then acc
   else
      let expl, gnat = extract_explanation "" "" f.t_label in
      if gnat <> "" then begin
         let pos = Util.of_option f.t_loc in
         Some (Gnat_expl.expl_from_label_info pos gnat expl)
      end else
         match f.t_node with
         | Ttrue | Tfalse | Tconst _ | Tvar _ | Tapp _  -> None
         | Tif (_,t1,t2) ->
               search_labels (search_labels acc t1) t2
         | Tcase (_, tbl) ->
               List.fold_left (fun acc b ->
                  let _, t = t_open_branch b in
                  search_labels acc t) acc tbl
         | Tnot t -> search_labels acc t
         | Tbinop (Timplies,_,t2) ->
               search_labels acc t2
         | Tbinop (_,t1,t2) -> search_labels (search_labels acc t1) t2
         | Tlet (_,tb) | Teps tb ->
               let _, t = t_open_bound tb in
               search_labels acc t
         | Tquant (_,tq) ->
               let _,_,t = t_open_quant tq in
               search_labels acc t

let expl_map = ref Gnat_expl.MExpl.empty
let nb_vcs   = ref 0
let nb_po    = ref 0

let find_expl e =
   try Gnat_expl.MExpl.find e !expl_map
   with Not_found ->
      incr nb_po;
      []

let add_entry e t =
   expl_map := Gnat_expl.MExpl.add e t !expl_map

let add_task e t =
   let l = find_expl e in
   incr nb_vcs;
   add_entry e (t::l)

let add_empty_task e =
   let l = find_expl e in
   add_entry e l

let do_task t =
   let fml = Task.task_goal_fmla t in
   match fml.t_node , search_labels None fml with
   | Ttrue, None -> ()
   | Ttrue, Some e -> add_empty_task e
   | _, None ->
         Gnat_util.abort_with_message "Task has no tracability label."
   | _, Some e -> add_task e t

let do_unsplitted_task t =
   let tasks = Trans.apply Gnat_config.split_trans t in
   List.iter do_task tasks

let do_theory _ th =
   let tasks = Task.split_theory th None None in
   List.iter do_unsplitted_task tasks

let vc_name expl n =
   let base = Gnat_expl.to_filename expl in
   let suffix = ".why" in
   if n = 1 then base ^ suffix
   else base ^ "_" ^ string_of_int n ^ suffix

let save_vc t expl n =
   let dr = Gnat_config.altergo_driver in
   let vc_fn = vc_name expl n in
   let cout = open_out vc_fn in
   let fmt  = Format.formatter_of_out_channel cout in
   Driver.print_task dr fmt t;
   Format.printf "saved VC to %s@." vc_fn


let prove_task t expl n =
   if Gnat_config.debug then save_vc t expl n;
   let pr_call =
      Driver.prove_task ~command:Gnat_config.alt_ergo_command
                        ~timelimit:Gnat_config.timeout
                        Gnat_config.altergo_driver t () in
   let res = Call_provers.wait_on_call pr_call () in
   (* if there was a problem, always report something to stderr *)
   let answer = res.Call_provers.pr_answer in
   if answer = Call_provers.HighFailure then begin
      Format.eprintf "An error occured when calling alt-ergo:@.";
      Format.eprintf "%s@." res.Call_provers.pr_output;
   end;
   answer

let report =
   let print fmt ?(endline=true) b expl =
      if endline then
         Format.fprintf fmt "%a@." (Gnat_expl.print_expl b) expl
      else
         Format.fprintf fmt "%a" (Gnat_expl.print_expl b) expl
   in
   fun fmt result expl ->
      (* always print to output file *)
      print fmt (result = Call_provers.Valid) expl;
      (* now print (possibly detailed) messages to stdout *)
      let print = print Format.std_formatter in
      if result = Call_provers.Valid then begin
         match Gnat_config.report with
         | (Gnat_config.Verbose | Gnat_config.Detailed) -> print true expl
         | _ -> ()
      end else
         if Gnat_config.report = Gnat_config.Detailed then begin
            print ~endline:false false expl;
            Format.printf " (%a)@." Call_provers.print_prover_answer result
         end else print false expl

exception Not_Proven of Call_provers.prover_answer

let prove_objective fmt expl tl =
   if Gnat_config.noproof then
      Format.printf "%a@." Gnat_expl.print_skipped expl
   else
      try
         let cnt = ref 0 in
         List.iter (fun t ->
            incr cnt;
            let result = prove_task t expl !cnt in
            if result <> Call_provers.Valid then raise (Not_Proven result)) tl;
         report fmt Call_provers.Valid expl
      with Not_Proven result -> report fmt result expl

let _ =
   if Gnat_config.report_mode then begin
      let filter =
         if not (Gnat_config.report = Gnat_config.Fail) then (fun _ -> true)
         else (fun s -> Gnat_util.ends_with s "not proved")
      in
      Gnat_util.cat filter Gnat_config.result_file;
      exit 0
   end;
   try
      let m = Env.read_file Gnat_config.env Gnat_config.filename in
      (* fill map of explanations *)
      Util.Mstr.iter do_theory m;
      if Gnat_config.verbose then
         Format.printf "Obtained %d proof objectives and %d VCs@."
            !nb_po !nb_vcs;
      let outbuf = Buffer.create 1024 in
      let fmt = Format.formatter_of_buffer outbuf in
      Gnat_expl.MExpl.iter (prove_objective fmt) !expl_map;
      Gnat_util.output_buffer outbuf Gnat_config.result_file
    with e when not (Debug.test_flag Debug.stack_trace) ->
       Format.eprintf "%a.@." Exn_printer.exn_printer e;
       Gnat_util.abort_with_message ""
