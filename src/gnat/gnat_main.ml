open Why3
open Term

let opt_verbose = ref false
let opt_timeout = ref 10
let opt_steps = ref 0
let opt_filename : string option ref = ref None

let abort_with_message s =
   Format.eprintf s;
   Format.eprintf " Aborting.@.";
   exit 1

let set_filename s =
   if !opt_filename = None then
      opt_filename := Some s
   else
      abort_with_message "Only one file name should be given."

let usage_msg =
  "Usage: gnatwhy3 [options] file"

let options = Arg.align [
   "-v", Arg.Set opt_verbose, "Output extra verbose information";
   "--verbose", Arg.Set opt_verbose, "Output extra verbose information";

   "-t", Arg.Set_int opt_timeout,
          "Set the timeout in seconds (default is 10 seconds)";
   "--timeout", Arg.Set_int opt_timeout,
          "Set the timeout in seconds (default is 10 seconds)";

   "-s", Arg.Set_int opt_steps,
          "Set the maximal number of proof steps";
   "--steps", Arg.Set_int opt_steps,
          "Set the maximal number of proof steps";
]

let filename =
   Arg.parse options set_filename usage_msg;
   match !opt_filename with
   | None -> abort_with_message "No file given."
   | Some s -> s

let config =
   try Whyconf.read_config (Some "why3.conf")
   with Rc.CannotOpen _ ->
      abort_with_message "Cannot read file why3.conf."

let config_main = Whyconf.get_main (config)

let env =
   Env.create_env_of_loadpath (Whyconf.loadpath config_main)

let is_not_why_loc s =
   not (Filename.check_suffix s "why" ||
        Filename.check_suffix s "mlw")

let suffix = ".mlw"

let split_trans = Trans.lookup_transform_l "split_goal" env

let split_list l =
   List.fold_left (fun acc t ->
      List.rev_append (Trans.apply split_trans t) acc) [] l

let provers : Whyconf.config_prover Util.Mstr.t =
   Whyconf.get_provers config

let alt_ergo : Whyconf.config_prover =
  try
    Util.Mstr.find "alt-ergo" provers
  with Not_found ->
    abort_with_message "Prover alt-ergo not installed or not configured."

(* loading the Alt-Ergo driver *)
let altergo_driver : Driver.driver =
  try
    Driver.load_driver env alt_ergo.Whyconf.driver
  with e ->
    Format.eprintf "Failed to load driver for alt-ergo: %a"
       Exn_printer.exn_printer e;
    abort_with_message ""

let alt_ergo_command =
   let command = alt_ergo.Whyconf.command in
   if !opt_steps = 0 then command
   else command ^ Printf.sprintf " -steps %d" !opt_steps

let starts_with s start =
   if String.length start > String.length s then false
   else
      try
         for i = 0 to String.length start - 1 do
            if s.[i] <> start.[i] then raise Exit
         done;
         true
      with Exit -> false

let rec extract_explanation expl gnat l =
    match l with
   | [] -> expl, gnat
   | x::rest when starts_with x "expl:" ->
         let s = String.sub x 5 (String.length x - 5) in
         extract_explanation s gnat rest
   | x::rest when starts_with x "gnatprove:" ->
         let s = String.sub x 10 (String.length x - 10) in
         extract_explanation expl s rest
   | _::xs -> extract_explanation expl gnat xs

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

let find_expl e =
   try Gnat_expl.MExpl.find e !expl_map
   with Not_found -> []

let add_task e t =
   let l = find_expl e in
   expl_map := Gnat_expl.MExpl.add e (t::l) !expl_map

let do_task t =
   let fml = Task.task_goal_fmla t in
   match fml.t_node with
   | Ttrue -> ()
   | _ ->
         let expl = search_labels None fml in
         match expl with
         | None ->
               abort_with_message "Task has no tracability label."

         | Some e ->
               add_task e t

let do_unsplitted_task t =
   let tasks = Trans.apply split_trans t in
   List.iter do_task tasks

let do_theory _ th =
   let tasks = Task.split_theory th None None in
   List.iter do_unsplitted_task tasks

let prove_task t =
   let pr_call =
      Driver.prove_task ~command:alt_ergo_command
                        ~timelimit:!opt_timeout altergo_driver t () in
   let res = Call_provers.wait_on_call pr_call () in
   match res.Call_provers.pr_answer with
   | Call_provers.Valid -> true
   | Call_provers.Failure s ->
         if !opt_verbose then begin
            Format.eprintf "An error occured when calling alt-ergo: ";
            Format.eprintf "%s" s;
            Format.eprintf "@.";
         end;
         false
   | Call_provers.HighFailure ->
         if !opt_verbose then begin
            Format.eprintf "An error occured when calling alt-ergo@."
         end;
         false
   | _ ->
         false

exception Not_Proven

let _ =
   try
      let m = Env.read_file env filename in
      (* fill map of explanations *)
      Util.Mstr.iter do_theory m;
      Gnat_expl.MExpl.iter
         (fun expl tl ->
            try
               List.iter (fun t -> if not (prove_task t) then raise Not_Proven)
               tl;
               Format.printf "%a@." (Gnat_expl.print_expl true) expl
            with Not_Proven ->
               Format.printf "%a@." (Gnat_expl.print_expl false) expl)
         !expl_map
    with e when not (Debug.test_flag Debug.stack_trace) ->
       Format.eprintf "%a.@." Exn_printer.exn_printer e;
       abort_with_message ""
