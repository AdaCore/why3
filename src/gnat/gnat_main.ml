open Why3
open Term

let config =
   try Whyconf.read_config (Some "why3.conf")
   with Rc.CannotOpen _ ->
      prerr_endline "Cannot file why3.conf. Aborting.";
      exit 1

let config_main = Whyconf.get_main (config)

let env =
   let loadpath = "." :: Whyconf.loadpath config_main in
   Env.create_env_of_loadpath loadpath

let is_not_why_loc s =
   not (Filename.check_suffix s "why" ||
        Filename.check_suffix s "mlw")

let filename =
   if Array.length (Sys.argv) < 2 then begin
      prerr_endline "No file given. Aborting";
      exit 1
   end;
   Sys.argv.(1)

let suffix = ".mlw"

let basename =
   if Filename.check_suffix filename suffix then
      Filename.chop_suffix filename suffix
   else begin
      Format.eprintf
        "File should have suffix .mlw, but the file is %s. Aborting."
        filename;
      exit 1
   end

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
    Format.eprintf "Prover alt-ergo not installed or not configured@.";
    exit 0

(* loading the Alt-Ergo driver *)
let altergo_driver : Driver.driver =
  try
    Driver.load_driver env alt_ergo.Whyconf.driver
  with e ->
    Format.eprintf "Failed to load driver for alt-ergo: %a@."
      Exn_printer.exn_printer e;
    exit 1

(*
   let _ = Debug.set_flag (Debug.lookup_flag "print_labels")
let _ = Debug.set_flag (Debug.lookup_flag "print_locs") *)

let starts_with s start =
   if String.length start > String.length s then false
   else
      try
         for i = 0 to String.length start - 1 do
            if s.[i] <> start.[i] then raise Exit
         done;
         true
      with Exit -> false

let asym_split = Term.asym_label
let stop_split = "stop_split"

let asym f = List.mem asym_split f.t_label
let stop f = List.mem stop_split f.t_label

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
         (* VC_INVARIANT is the only one where we actually need a Why
            explanation *)
         Some (Gnat_expl.expl_from_label_info pos gnat  expl)
      end else
         match f.t_node with
         | Ttrue | Tfalse | Tconst _ | Tvar _ | Tapp _  -> None
         | Tif (_,t1,t2) ->
               search_labels (search_labels acc t1) t2
         | Teps _ | Tcase _ -> assert false
         | Tnot t -> search_labels acc t
         | Tbinop (Timplies,_,t2) ->
               search_labels acc t2
         | Tbinop (_,t1,t2) -> search_labels (search_labels acc t1) t2
         | Tlet (_,tb) ->
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
         | None -> assert false
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
      Driver.prove_task ~command:alt_ergo.Whyconf.command
                        ~timelimit:10 altergo_driver t () in
   let res = Call_provers.wait_on_call pr_call () in
   if res.Call_provers.pr_answer = Call_provers.Valid then true
   else false

exception Not_Proven

let _ =
   if Array.length (Sys.argv) < 2 then begin
      prerr_endline "No file given. Aborting";
      exit 1
   end;
   let fn = Sys.argv.(1) in
   try
      let m = Env.read_file env fn in
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
      Format.eprintf "%a@." Exn_printer.exn_printer e;
      exit 1



