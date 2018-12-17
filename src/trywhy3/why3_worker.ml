(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


(* Interface to Why3 and Alt-Ergo *)

let why3_conf_file = "/trywhy3.conf"

open Why3
open Format
open Worker_proto

module Sys_js = Js_of_ocaml.Sys_js
module Worker = Js_of_ocaml.Worker

let () = log_time ("Initialising why3 worker: start ")

(* Name of the pseudo file *)

let temp_file_name = "/trywhy3_input.mlw"

(* reads the config file *)
let config : Whyconf.config = Whyconf.read_config (Some why3_conf_file)
(* the [main] section of the config file *)
let main : Whyconf.main = Whyconf.get_main config
(* all the provers detected, from the config file *)
let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers config

(* One prover named Alt-Ergo in the config file *)
let alt_ergo : Whyconf.config_prover =
  if Whyconf.Mprover.is_empty provers then begin
    eprintf "Prover Alt-Ergo not installed or not configured@.";
    exit 0
  end else snd (Whyconf.Mprover.choose provers)

(* builds the environment from the [loadpath] *)
let env : Env.env = Env.create_env (Whyconf.loadpath main)

let alt_ergo_driver : Driver.driver =
  try
    Printexc.record_backtrace true;
    Whyconf.load_driver main env alt_ergo.Whyconf.driver []
  with e ->
    let s = Printexc.get_backtrace () in
    eprintf "Failed to load driver for alt-ergo: %a@.%s@."
      Exn_printer.exn_printer e s;
  exit 1

let () = log_time ("Initialising why3 worker: end ")

let split_trans = Trans.lookup_transform_l "split_vc" env

(* CF gmain.ml ligne 568 et suivante *)
module W =
  struct
    let send msg =
      ignore (Worker.post_message (marshal msg))

    let set_onmessage f =
      Worker.set_onmessage (fun data -> f (unmarshal data))
  end

(* Task Management *)
module Why3Task = Task (* prevent shadowing *)

module Task =
  struct
    type task_info =
      { task : [ `Theory of Theory.theory | `Task of Task.task ];
	parent_id : id;
	mutable status : status;
	mutable subtasks : id list;
	loc : why3_loc list;
	expl : string;
        pretty : string;
      }

    let task_table : (id, task_info) Hashtbl.t = Hashtbl.create 17

    let clear_table () = Hashtbl.clear task_table
    let get_info id = Hashtbl.find task_table id
    let get_info_opt id =
      try
        Some (get_info id)
      with
        Not_found -> None

    let get_parent_id id = (get_info id).parent_id

    let mk_loc (f, a,b,c) =
      if f = temp_file_name then
        Some (a,b,c)
      else None


    let warnings = ref []
    let clear_warnings () = warnings := []
    let () =
      Warning.set_hook (fun ?(loc=(Loc.user_position "" 1 0 0)) msg ->
                        let _, a,b,_ = Loc.get loc in
                        warnings := ((a-1,b), msg) :: !warnings)


    let premise_kind = function
      | { Term. t_node = Term.Tnot _; t_loc = None } -> "why3-loc-neg-premise"
      | _ -> "why3-loc-premise"

    let collect_locs t =
      (* from why 3 ide *)
      let locs = ref [] in
      let rec get_locs kind f =
        Opt.iter (fun loc ->
            match mk_loc (Loc.get loc) with
              None -> ()
            | Some l -> locs := (kind, l) :: !locs) f.Term.t_loc;
        Term.t_fold (fun () t -> get_locs kind t ) () f
      in
      let rec get_t_locs f =
        match f.Term.t_node with
        | Term.Tbinop (Term.Timplies,f1,f2) ->
           get_locs (premise_kind f1) f1;
           get_t_locs f2
        | Term.Tlet (t,fb) ->
           let _,f1 = Term.t_open_bound fb in
           get_locs (premise_kind t) t;
           get_t_locs f1
        | Term.Tquant (Term.Tforall,fq) ->
           let _,_,f1 = Term.t_open_quant fq in
           get_t_locs f1
        | _ ->
           get_locs "why3-loc-goal" f
      in
      match t with
      | Some { Task.task_decl =
                 { Theory.td_node =
                     Theory.Decl { Decl.d_node = Decl.Dprop (Decl.Pgoal, _, f)}}} ->
         get_t_locs f; !locs
      |  _ -> []

    let task_to_string t =
      Format.asprintf "%a" (Driver.print_task alt_ergo_driver) t

    let gen_id =
      let c = ref 0 in
      fun () -> incr c; "id" ^ (string_of_int !c)

    let task_text t =
      Pp.string_of Pretty.print_task t

    let register_task parent_id task =
      let id = gen_id () in
      let vid, expl, _ = Termcode.goal_expl_task ~root:false task in
      let id_loc = match vid.Ident.id_loc with
          None -> []
        | Some l -> begin match mk_loc (Loc.get l) with
              Some l -> [ ("why3-loc-goal", l) ]
            | None -> []
          end
      in
      let task_info =
        { task = `Task(task);
	  parent_id = parent_id;
	  status = `New;
	  subtasks = [];
	  loc = id_loc @  (collect_locs task);
	  expl = expl;
          pretty = task_text task;
        }
      in
      Hashtbl.add task_table id task_info;
      id

    let register_theory th_name th =
      let th_id = gen_id () in
      let tasks = Why3Task.split_theory th None None in
      let task_ids = List.fold_left (fun acc t ->
				     let tid = register_task th_id t in
				     tid:: acc) [] tasks in
      Hashtbl.add task_table th_id  { task = `Theory(th);
				      parent_id = "theory-list";
				      status = `New;
				      subtasks = List.rev task_ids;
				      loc = [];
				      expl = th_name;
                                      pretty = "";
                                    };
      th_id

    let get_task = function `Task t -> t
                          | `Theory _ -> log ("called get_task on a theory !"); assert false

    let set_status id st =
      let rec loop id st acc =
        match get_info_opt id with
        | Some info when info.status <> st ->
	   info.status <- st;
           let acc = (UpdateStatus (st, id)) :: acc in
           begin
             match get_info_opt info.parent_id with
               None -> acc
             | Some par_info ->
	        let has_new, has_unknown =
	          List.fold_left
	            (fun (an, au) id ->
	             let info = Hashtbl.find task_table id in
	             (an || info.status = `New), (au || info.status = `Unknown))
	            (false, false) par_info.subtasks
	        in
	        let par_status = if has_new then `New else if
			           has_unknown then `Unknown
			         else `Valid
	        in
	        if par_info.status <> par_status then
	          loop info.parent_id par_status acc
                else acc
           end
        | _ -> acc

      in
      loop id st []

    let rec clean_task id =
      try
        let info = get_info id in
        List.iter clean_task info.subtasks;
        Hashtbl.remove task_table id
      with
        Not_found -> ()

  end



(* External API *)


let rec why3_prove ?(steps= ~-1) id =
  let open Task in
  let t = get_info id in
  match t.subtasks with
    [] ->  t.status <- `Unknown;
	  let task = get_task t.task in
	  let msg = Task (id, t.parent_id, t.expl, task_to_string task, t.loc, t.pretty, steps) in
	  W.send msg;
	  let l = set_status id `New in
          List.iter W.send l
  | l -> List.iter (why3_prove ~steps) l


let why3_split id =
  let open Task in
  let t = get_info id in
  match t.subtasks with
    [] ->
    begin
      match Trans.apply split_trans (get_task t.task), t.task with
	[], _ -> ()
      | [ child ], `Task(orig) when Why3.Task.task_equal child orig -> ()
      | subtasks, _ ->
          t.subtasks <- List.map (fun t -> register_task id t) subtasks;
          List.iter why3_prove t.subtasks
    end
  | _ -> ()



let why3_clean id =
  let open Task in
  try
    let t = get_info id in
    List.iter clean_task t.subtasks;
    t.subtasks <- [];
    let l = set_status id `Unknown in
    List.iter W.send l
  with
    Not_found -> ()

let why3_prove_all () =
  Hashtbl.iter
    (fun _ info ->
     match info.Task.task with
       `Theory _ -> List.iter (fun i -> why3_prove i) info.Task.subtasks
     | _ -> ()) Task.task_table


let why3_parse_theories theories =
  let theories =
    Wstdlib.Mstr.fold
      (fun thname th acc ->
       let loc =
         Opt.get_def Loc.dummy_position th.Theory.th_name.Ident.id_loc
       in
       (loc, (thname, th)) :: acc) theories []
  in
  let theories = List.sort  (fun (l1,_) (l2,_) -> Loc.compare l1 l2) theories in
  List.iter
    (fun (_, (th_name, th)) ->
     let th_id = Task.register_theory th_name th in
     W.send (Theory(th_id, th_name));
     let subs = (Task.get_info th_id).Task.subtasks in
     W.send (UpdateStatus( (if subs == [] then `Valid else `New) , th_id));
     List.iter (fun i -> why3_prove i) subs
    ) theories

let why3_execute modules =
  let result =
    let mods =
      Wstdlib.Mstr.fold
	(fun _k m acc ->
         let th = m.Pmodule.mod_theory in
         let modname = th.Theory.th_name.Ident.id_string in
         try
           let rs = Pmodule.ns_find_rs m.Pmodule.mod_export ["main"]
           in
           let result = Pp.sprintf "%a" (Pinterp.eval_global_symbol env m) rs in
           let loc =
             Opt.get_def Loc.dummy_position th.Theory.th_name.Ident.id_loc
           in
           (loc, modname ^ ".main() returns " ^ result)
           :: acc
         with Not_found -> acc)
	modules []
    in
    match mods with
    | [] -> Error "No main function found"
    | _ ->
       let s =
	 List.sort
           (fun (l1,_) (l2,_) -> Loc.compare l2 l1)
           mods
       in
       (Result (List.rev_map snd s) )
  in
  W.send result


let () = Sys_js.create_file ~name:temp_file_name ~content:""

let why3_run f lang code =
  try
    let ch = open_out temp_file_name in
    output_string ch code;
    close_out ch;

    let theories = Env.read_file lang env temp_file_name in
    W.send (Warning !Task.warnings);
    f theories
  with
  | Loc.Located(loc,e') ->
     let _, l, b, e = Loc.get loc in
     W.send (ErrorLoc ((l-1,b, l-1, e),
		     Pp.sprintf
		       "error line %d, columns %d-%d: %a" l b e
		       Exn_printer.exn_printer e'))
  | e ->
     W.send (Error (Pp.sprintf
		      "unexpected exception: %a (%s)" Exn_printer.exn_printer e
		      (Printexc.to_string e)))


let () =
  W.set_onmessage
    (fun msg ->
     let () =
       match msg with
       | Transform (`Split, id) -> why3_split id
       | Transform (`Prove(steps), id) -> why3_prove ~steps id
       | Transform (`Clean, id) -> why3_clean id
       | ProveAll -> why3_prove_all ()
       | ParseBuffer code ->
          Task.clear_warnings ();
          Task.clear_table ();
          why3_run why3_parse_theories Env.base_language code
       | ExecuteBuffer code ->
          Task.clear_warnings ();
	  Task.clear_table ();
	  why3_run why3_execute Pmodule.mlw_language code
       | SetStatus (st, id) -> List.iter W.send (Task.set_status id st)
     in
     W.send Idle
    )
(*
Local Variables:
compile-command: "unset LANG; make -C ../.. trywhy3"
End:
*)
