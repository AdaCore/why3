open Why3
open Term

let config_main = Whyconf.get_main (Whyconf.read_config None)
let loadpath = Whyconf.loadpath config_main
let env = Env.create_env_of_loadpath loadpath

let printer = Ident.create_ident_printer []

let split_trans = Trans.lookup_transform_l "split_goal" env

let apply_split acc t = List.rev_append (Trans.apply split_trans t) acc

let why3_driver =
   Driver.load_driver env "/usr/local/share/why3/drivers/why3.drv"

let _ = Debug.set_flag (Debug.lookup_flag "print_labels")
let _ = Debug.set_flag (Debug.lookup_flag "print_locs")

let starts_with s start =
   if String.length start > String.length s then false
   else
      try
         for i = 0 to String.length start - 1 do
            if s.[i] <> start.[i] then raise Exit
         done;
         true
      with Exit -> false

let rec extract_explanation l =
   match l with
   | [] -> None
   | x::_ when starts_with x "expl:" ->
         Some (String.sub x 5 (String.length x - 5))
   | _::xs -> extract_explanation xs

let search_labels =
   let rec search_labels expl_found loc_found fml =
      let expl = extract_explanation fml.t_label in
      let expl_found = if expl = None then expl_found else expl in
      let loc_found =
         match fml.t_loc with
         | None -> loc_found
         | Some _ -> fml.t_loc
      in
      match fml.t_node with
      | Ttrue | Tfalse | Tconst _ | Tvar _ | Tapp _  -> expl_found, loc_found
      | Tif _ | Teps _ | Tcase _ -> assert false
      | Tnot t -> search_labels expl_found loc_found t
      | Tbinop (_,t1,t2) ->
            ignore (search_labels expl_found loc_found t1);
            search_labels expl_found loc_found t2
      | Tlet (t,tb) ->
            ignore (search_labels expl_found loc_found t);
            let _, t = t_open_bound tb in
            search_labels expl_found loc_found t
      | Tquant (_,tq) ->
            let _,_,t = t_open_quant tq in
            search_labels expl_found loc_found t
   in
   search_labels None None

let search_labels_task t =
   let fml = Task.task_goal_fmla t in
   search_labels fml

let do_task t =
   let g = Task.task_goal t in
   let l,p = search_labels_task t in
   let l =
      match l with
      | None -> assert false
      | Some l -> l in
   let p =
      match p with
      | None -> assert false
      | Some p -> p in
   Driver.print_task why3_driver Format.std_formatter t;
   Format.printf "@.=====================@.";
   Format.printf "%s:--%s@." (Ident.id_unique printer g.Decl.pr_name) l;
   let file, line, col, en = Loc.get p in
   Format.printf "%s: line %d, col %d - %d@." file line col en


let do_theory s th =
   Format.printf "%s@." s;
   let tasks = Task.split_theory th None None in
   let tasks = List.fold_left apply_split [] tasks in
   List.iter do_task tasks

let _ =
   if Array.length (Sys.argv) < 2 then begin
      prerr_endline "No file given. Aborting";
      exit 1
   end;
   let fn = Sys.argv.(1) in
   let m = Env.read_file env fn in
   Util.Mstr.iter do_theory m


