(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
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


(* TODO:

* when proof attempt is finished and is it the one currently selected,
the new output should be displayed on upper-right window

* when returning from edited proofs: should we run the prover again
   immediately ?

* bug trouve par Johannes:

Pour reproduire le bug :

1) Partir d'un répértoire sans fichier de projet
2) Lancer why3db, ajouter un fichier
3) Prouver quelques buts (pas tous)
4) Choisir "Hide Proved Goals"
5) Prouver le reste des buts, la fênetre devient vide
6) Décocher "Hide Proved Goals"

Maintenant, le fichier réapparait dans la liste, mais on ne peut pas le
déplier, donc accéder au sous-buts, stats des appels de prouvers etc ...

Ce n'est pas un bug très grave, parce qu'il suffit de quitter l'ide,
puis le relancer, et là on peut de nouveau déplier le fichier.

* Francois :

   - Les temps indiqués sont très bizarre, mais cela doit-être un bug
   plus profond, au niveau de l'appel des prouveurs (wall time au lieu
   de cpu time?)

   - Si on modifie le fichier à droite, les buts ne sont pas marqués
   obsolètes ou ajouté à gauche.

*)



open Format

let () =
  eprintf "Init the GTK interface...@?";
  ignore (GtkMain.Main.init ());
  eprintf " done.@."


open Why
open Whyconf
open Gconfig

(************************)
(* parsing command line *)
(************************)

let includes = ref []
let file = ref None
let opt_version = ref false

let spec = Arg.align [
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> add s to loadpath") ;
(*
  ("-f",
   Arg.String (fun s -> input_files := s :: !input_files),
   "<f> add file f to the project (ignored if it is already there)") ;
*)
  ("-v",
   Arg.Set opt_version,
   " print version information") ;
]

let version_msg = sprintf "Why3 IDE, version %s (build date: %s)"
  Config.version Config.builddate

let usage_str = sprintf
  "Usage: %s [options] [<file.why>|<project directory>]"
  (Filename.basename Sys.argv.(0))

let set_file f = match !file with
  | Some _ ->
      raise (Arg.Bad "only one parameter")
  | None ->
      file := Some f

let () = Arg.parse spec set_file usage_str

let () =
  if !opt_version then begin
    printf "%s@." version_msg;
    exit 0
  end

let fname = match !file with
  | None ->
      Arg.usage spec usage_str;
      exit 1
  | Some f ->
      f

let lang =
  let main = get_main () in
  let load_path = Filename.concat (datadir main) "lang" in
  let languages_manager =
    GSourceView2.source_language_manager ~default:true
  in
  languages_manager#set_search_path
    (load_path :: languages_manager#search_path);
  match languages_manager#language "why" with
    | None ->
        Format.eprintf "language file for 'why' not found in directory %s@."
          load_path;
        exit 1
    | Some _ as l -> l

let source_text fname =
  let ic = open_in fname in
  let size = in_channel_length ic in
  let buf = String.create size in
  really_input ic buf 0 size;
  close_in ic;
  buf

(********************************)
(* loading WhyIDE configuration *)
(********************************)

let gconfig =
  let c = Gconfig.config in
  let loadpath = (Whyconf.loadpath (get_main ())) @ List.rev !includes in
  c.env <- Lexer.create_env loadpath;
  let provers = Whyconf.get_provers c.Gconfig.config in
  c.provers <-
    Util.Mstr.fold (Gconfig.get_prover_data c.env) provers Util.Mstr.empty;
  c

let () =
  Whyconf.load_plugins (get_main ())


(********************)
(* opening database *)
(********************)

let project_dir, file_to_read =
  if Sys.file_exists fname then
    begin
      if Sys.is_directory fname then
        begin
          eprintf "Info: found directory '%s' for the project@." fname;
          fname, None
        end
      else
        begin
          eprintf "Info: found regular file '%s'@." fname;
          let d =
            try Filename.chop_extension fname
            with Invalid_argument _ -> fname
          in
          eprintf "Info: using '%s' as directory for the project@." d;
          d, Some (Filename.concat Filename.parent_dir_name
		     (Filename.basename fname))
        end
    end
  else
    fname, None

let () =
  if not (Sys.file_exists project_dir) then
    begin
      eprintf "Info: '%s' does not exists. Creating directory of that name \
 for the project@." project_dir;
      Unix.mkdir project_dir 0o777
    end

let () =
  let dbfname = Filename.concat project_dir "project.db" in
  try
    Db.init_base dbfname
  with e ->
    eprintf "Error while opening database '%s'@." dbfname;
    eprintf "Aborting...@.";
    raise e


let read_file fn =
  let fn = Filename.concat project_dir fn in
  let theories = Env.read_file gconfig.env fn in
  let theories =
    Theory.Mnm.fold
      (fun name th acc ->
         match th.Theory.th_name.Ident.id_origin with
           | Ident.User l -> (l,name,th)::acc
           | _ -> (Loc.dummy_position,name,th)::acc)
      theories []
  in
  let theories = List.sort
    (fun (l1,_,_) (l2,_,_) -> Loc.compare l1 l2)
    theories
  in theories

(*******************************************)
(* Scheduler for long-running computations *)
(*******************************************)

(*

This home made scheduler allows to run long computations "in background"
that is without freezing the GUI for too long time.

It works by using: 
* a queue Qa of atomic actions to process:
   One element of Qa is processed whenever the GUI is idle. Actions can be
   of 3 kinds:
   . production of an external proof attempt
   . application of a transformation
   . editing a proof
* a queue Qp of prover calls ready to start
   one element is queued by an action of kind "add proof attempt"
* a set E of prover calls to check for termination:
   all elements of E are check at regular time steps.
   if there are less elements than a given maximum number of parallel 
   processes then a new prover_call is extracted from Qp

*)

module Gscheduler = struct

type proof_attempt_status =
  | Scheduled (** external proof attempt is scheduled *)
  | Running (** external proof attempt is in progress *)
  | Done of Call_provers.prover_result (** external proof done *)
  | InternalFailure of exn (** external proof aborted by internal error *)


(* timeout handler *)

let maximum_running_proofs = ref 2
let running_proofs = ref []

let proof_attempts_queue = Queue.create ()

let timeout_handler_activated = ref false
let timeout_handler_running = ref false

let timeout_handler () =
  assert (not !timeout_handler_running);
  timeout_handler_running := true;
  let l = List.fold_left
    (fun acc ((callback,call) as c) ->
       match Call_provers.query_call call with
	 | None -> c::acc
	 | Some post ->
	     let res = post () in callback (Done res);
	     acc)
    [] !running_proofs
  in
  let l =
    if List.length l < !maximum_running_proofs then
      begin try 
	let (callback,pre_call) = Queue.pop proof_attempts_queue in
	callback Running;
	let call = pre_call () in
	(callback,call)::l
      with Queue.Empty -> l
      end
    else l
  in
  running_proofs := l;
  let continue = match l with | [] -> false | _ -> true in
  timeout_handler_activated := continue; 
  timeout_handler_running := false;
  continue
      

let run_timeout_handler () =
  if !timeout_handler_activated then () else
    begin
      timeout_handler_activated := true;
      let (_ : GMain.Timeout.id) = 
	GMain.Timeout.add ~ms:100 ~callback:timeout_handler 
      in ()
    end
	     
(* idle handler *)


type action =
  | Proof_attempt of bool * int * int * in_channel option * string * Driver.driver *
    (proof_attempt_status -> unit) * Task.task

let actions_queue = Queue.create ()

let idle_handler_activated = ref false

let idle_handler () =
  try
    begin
      match Queue.pop actions_queue with
	| Proof_attempt(debug,timelimit,memlimit,old,command,driver,
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
    end;
    true
  with Queue.Empty ->
    idle_handler_activated := false;
    false

let run_idle_handler () =
  if !idle_handler_activated then () else
    begin
      idle_handler_activated := true;
      let (_ : GMain.Idle.id) = GMain.Idle.add idle_handler in
      ()
    end

(* main scheduling functions *)

let schedule_proof_attempt ~debug ~timelimit ~memlimit ?old
    ~command ~driver ~callback goal =
  Queue.push 
    (Proof_attempt(debug,timelimit,memlimit,old,command,driver,
			callback,goal))
    actions_queue;
  run_idle_handler ()

let apply_transformation ~callback transf goal =
  callback (Trans.apply transf goal)

let apply_transformation_l ~callback transf goal =
  callback (Trans.apply transf goal)

let edit_proof ~debug:_ ~editor ~file ~driver ~callback goal =
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
  let _ = Sys.command(editor ^ " " ^ file) in
  callback ()

end

(****************)
(* goals widget *)
(****************)


module Model = struct

  type proof_attempt =
      { prover : prover_data;
        proof_goal : goal;
        proof_row : Gtk.tree_iter;
        proof_db : Db.proof_attempt;
	mutable proof_state : Gscheduler.proof_attempt_status;
        mutable proof_obsolete : bool;
        mutable edited_as : string;
      }

  and goal_parent =
    | Theory of theory
    | Transf of transf

  and goal =
      { goal_name : string;
	parent : goal_parent;
        task: Task.task;
        goal_row : Gtk.tree_iter;
        goal_db : Db.goal;
        mutable proved : bool;
        external_proofs: (string, proof_attempt) Hashtbl.t;
        transformations : (string, transf) Hashtbl.t;
      }

  and transf =
      { parent_goal : goal;
	mutable transf_proved : bool;
(*
        transf : Task.task Trans.trans;
*)
        transf_row : Gtk.tree_iter;
        transf_db : Db.transf;
        mutable subgoals : goal list;
      }

  and theory =
      { theory : Theory.theory;
        theory_row : Gtk.tree_iter;
        theory_db : Db.theory;
        theory_parent : file;
        mutable goals : goal list;
        mutable verified : bool;
      }

  and file =
      { file_name : string;
        file_row : Gtk.tree_iter;
        file_db : Db.file;
        mutable theories: theory list;
        mutable file_verified : bool;
      }


  type any_row =
    | Row_file of file
    | Row_theory of theory
    | Row_goal of goal
    | Row_proof_attempt of proof_attempt
    | Row_transformation of transf

  let all_files : file list ref = ref []

  let toggle_hide_proved_goals = ref false

  let cols = new GTree.column_list
  let name_column = cols#add Gobject.Data.string
  let icon_column = cols#add Gobject.Data.gobject
  let index_column : any_row GTree.column = cols#add Gobject.Data.caml
  let status_column = cols#add Gobject.Data.gobject
  let time_column = cols#add Gobject.Data.string
  let visible_column = cols#add Gobject.Data.boolean
(*
  let bg_column = cols#add (Gobject.Data.unsafe_boxed
  (Gobject.Type.from_name "GdkColor"))
*)

  let name_renderer = GTree.cell_renderer_text [`XALIGN 0.]
  let renderer = GTree.cell_renderer_text [`XALIGN 0.]
  let image_renderer = GTree.cell_renderer_pixbuf [ ]
  let icon_renderer = GTree.cell_renderer_pixbuf [ ]

  let view_name_column =
    GTree.view_column ~title:"Theories/Goals" ()

  let () =
    view_name_column#pack icon_renderer ;
    view_name_column#add_attribute icon_renderer "pixbuf" icon_column ;
    view_name_column#pack name_renderer;
    view_name_column#add_attribute name_renderer "text" name_column;
    view_name_column#set_resizable true;
    view_name_column#set_max_width 400;
(*
    view_name_column#add_attribute name_renderer "background-gdk" bg_column
*)
    ()

  let view_status_column =
    GTree.view_column ~title:"Status"
      ~renderer:(image_renderer, ["pixbuf", status_column])
      ()

  let view_time_column =
    GTree.view_column ~title:"Time"
      ~renderer:(renderer, ["text", time_column]) ()

  let () =
    view_status_column#set_resizable false;
    view_status_column#set_visible true;
    view_time_column#set_resizable false;
    view_time_column#set_visible true


  let create ~packing () =
    let model = GTree.tree_store cols in
    let model_filter = GTree.model_filter model in
    model_filter#set_visible_column visible_column;
    let view = GTree.view ~model:model_filter ~packing () in
(*
    let () = view#selection#set_mode `SINGLE in
*)
    let () = view#selection#set_mode `MULTIPLE in
    let () = view#set_rules_hint true in
    ignore (view#append_column view_name_column);
    ignore (view#append_column view_status_column);
    ignore (view#append_column view_time_column);
    model,model_filter,view

  let clear model = model#clear ()

end


(***************)
(* Main window *)
(***************)

let exit_function () =
  eprintf "saving IDE config file@.";
  save_config ();
  GMain.quit ()

let w = GWindow.window
  ~allow_grow:true ~allow_shrink:true
  ~width:gconfig.window_width
  ~height:gconfig.window_height
  ~title:"why GUI with database" ()

let (_ : GtkSignal.id) = w#connect#destroy ~callback:exit_function

let (_ : GtkSignal.id) =
  w#misc#connect#size_allocate
    ~callback:
    (fun {Gtk.width=w;Gtk.height=h} ->
       gconfig.window_height <- h;
       gconfig.window_width <- w)

let vbox = GPack.vbox ~packing:w#add ()

(* Menu *)

let menubar = GMenu.menu_bar ~packing:vbox#pack ()

let factory = new GMenu.factory menubar

let accel_group = factory#accel_group

let hb = GPack.hbox ~packing:vbox#add ~border_width:2 ()

let tools_window_vbox =
  try
    GPack.vbox ~packing:(hb#pack ~expand:false) ~border_width:2 ()
  with Gtk.Error _ -> assert false

let context_frame =
  GBin.frame ~label:"Context"
    ~packing:(tools_window_vbox#pack ~expand:false) ()

let context_box =
  GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
    ~packing:context_frame#add ()

let context_unproved_goals_only = ref true

let () =
  let b1 = GButton.radio_button
    ~packing:context_box#add ~label:"Unproved goals" ()
  in
  let (_ : GtkSignal.id) =
    b1#connect#clicked
      ~callback:(fun () -> context_unproved_goals_only := true)
  in
  let b2 = GButton.radio_button
    ~group:b1#group ~packing:context_box#add ~label:"All goals" ()
  in
  let (_ : GtkSignal.id) =
    b2#connect#clicked
      ~callback:(fun () -> context_unproved_goals_only := false)
  in ()


let provers_frame =
  GBin.frame ~label:"Provers"
    ~packing:(tools_window_vbox#pack ~expand:false) ()

let provers_box =
  GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
  ~packing:provers_frame#add ()

let () = provers_frame#set_resize_mode `PARENT

let transf_frame =
  GBin.frame ~label:"Transformations"
    ~packing:(tools_window_vbox#pack ~expand:false) ()

let transf_box =
  GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
  ~packing:transf_frame#add ()

let tools_frame =
  GBin.frame ~label:"Tools"
    ~packing:(tools_window_vbox#pack ~expand:false) ()

let tools_box =
  GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
  ~packing:tools_frame#add ()

let cleaning_frame =
  GBin.frame ~label:"Cleaning"
    ~packing:(tools_window_vbox#pack ~expand:false) ()

let cleaning_box =
  GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
  ~packing:cleaning_frame#add ()


(* horizontal paned *)

let hp = GPack.paned `HORIZONTAL ~packing:hb#add ()


(* tree view *)
let scrollview =
  try
    GBin.scrolled_window ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~width:gconfig.tree_width
      ~packing:hp#add ()
  with Gtk.Error _ -> assert false

let () = scrollview#set_shadow_type `ETCHED_OUT
let (_ : GtkSignal.id) =
  scrollview#misc#connect#size_allocate
    ~callback:
    (fun {Gtk.width=w;Gtk.height=_h} ->
       gconfig.tree_width <- w)

let goals_model,filter_model,goals_view =
  Model.create ~packing:scrollview#add ()

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


let info_window ?(callback=(fun () -> ())) mt s =
  let buttons = match mt with
    | `INFO -> GWindow.Buttons.close
    | `WARNING -> GWindow.Buttons.close
    | `QUESTION -> GWindow.Buttons.ok_cancel
    | `ERROR -> GWindow.Buttons.close
  in
  let d = GWindow.message_dialog
    ~message:s
    ~message_type:mt
    ~buttons
    ~title:"Why3 info or error"
    ~show:true ()
  in
  let (_ : GtkSignal.id) =
    d#connect#response
      ~callback:(function x -> d#destroy ();
		   if x = `OK then callback ())
  in ()



  let expl_regexp = Str.regexp "expl:\\(.*\\)"

  let rec get_labels f =
    f.Term.f_label @
    match f.Term.f_node with
      | Term.Fbinop(Term.Fimplies,_,f) -> get_labels f
      | Term.Fquant(Term.Fforall,fq) ->
	  let (_,_,f) = Term.f_open_quant fq in get_labels f
      | _ -> []

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
      (get_labels fmla @ id.Ident.id_label);
    !r


module Helpers = struct

  open Model
  open Gscheduler

  let image_of_result ~obsolete result =
    match result with
    | Scheduled -> !image_scheduled
    | Running -> !image_running
    | InternalFailure _ -> !image_failure
    | Done r -> match r.Call_provers.pr_answer with
	| Call_provers.Valid ->
	    if obsolete then !image_valid_obs else !image_valid
	| Call_provers.Invalid ->
	    if obsolete then !image_invalid_obs else !image_invalid
	| Call_provers.Timeout ->
	    if obsolete then !image_timeout_obs else !image_timeout
	| Call_provers.Unknown _ ->
	    if obsolete then !image_unknown_obs else !image_unknown
	| Call_provers.Failure _ ->
	    if obsolete then !image_failure_obs else !image_failure
	| Call_provers.HighFailure ->
	    if obsolete then !image_failure_obs else !image_failure

  let set_row_status b row =
    if b then
      begin
	goals_view#collapse_row (goals_model#get_path row);
	goals_model#set ~row ~column:status_column !image_yes;
	if !toggle_hide_proved_goals then
	  goals_model#set ~row ~column:visible_column false
      end
    else
      begin
	goals_model#set ~row ~column:status_column !image_unknown;
	if !toggle_hide_proved_goals then
	  goals_model#set ~row ~column:visible_column true
      end

  let check_file_verified f =
    let b = List.for_all (fun t -> t.verified) f.theories in
    if f.file_verified <> b then
      begin
	f.file_verified <- b;
	set_row_status b f.file_row
      end

  let check_theory_proved t =
    let b = List.for_all (fun g -> g.proved) t.goals in
    if t.verified <> b then
      begin
	t.verified <- b;
	set_row_status b t.theory_row;
	check_file_verified t.theory_parent
      end

  let rec check_goal_proved g =
    let b1 = Hashtbl.fold
      (fun _ a acc -> acc ||
	 match a.proof_state with
	   | Done { Call_provers.pr_answer = Call_provers.Valid} -> true
	   | _ -> false) g.external_proofs false
    in
    let b = Hashtbl.fold
      (fun _ t acc -> acc || t.transf_proved) g.transformations b1
    in
    if g.proved <> b then
      begin
	g.proved <- b;
	set_row_status b g.goal_row;
	match g.parent with
          | Theory t -> check_theory_proved t
          | Transf t -> check_transf_proved t
      end

  and check_transf_proved t =
    let b = List.for_all (fun g -> g.proved) t.subgoals in
    if t.transf_proved <> b then
      begin
	t.transf_proved <- b;
	set_row_status b t.transf_row;
	check_goal_proved t.parent_goal
      end


  (* deprecated *)
  let set_file_verified f =
    f.file_verified <- true;
    let row = f.file_row in
    goals_view#collapse_row (goals_model#get_path row);
    goals_model#set ~row ~column:status_column !image_yes;
    if !toggle_hide_proved_goals then
      goals_model#set ~row ~column:visible_column false

  (* deprecated *)
  let set_theory_proved ~propagate  t =
    t.verified <- true;
    let row = t.theory_row in
    goals_view#collapse_row (goals_model#get_path row);
    goals_model#set ~row ~column:status_column !image_yes;
    if !toggle_hide_proved_goals then
      goals_model#set ~row ~column:visible_column false;
    let f = t.theory_parent in
    if propagate then
      if List.for_all (fun t ->
(*
                         let tname = t.theory.Theory.th_name.Ident.id_string in
                         eprintf "checking theory %s@." tname;
*)
                         t.verified) f.theories then
        set_file_verified f

  let rec set_proved ~propagate g =
    let row = g.goal_row in
    g.proved <- true;
    goals_view#collapse_row (goals_model#get_path row);
    goals_model#set ~row ~column:status_column !image_yes;
    if !toggle_hide_proved_goals then
      goals_model#set ~row ~column:visible_column false;
    if propagate then
      match g.parent with
        | Theory t ->
            if List.for_all (fun g -> g.proved) t.goals then
              set_theory_proved ~propagate t
        | Transf t ->
            if List.for_all (fun g -> g.proved) t.subgoals then
              begin
                set_proved ~propagate t.parent_goal;
              end

  let set_proof_state ~obsolete a res =
    a.proof_state <- res;
    let row = a.proof_row in
    goals_model#set ~row ~column:status_column
      (image_of_result ~obsolete res);

    let t = match res with
      | Done { Call_provers.pr_time = time } ->
          Format.sprintf "%.2f" time
      | _ -> ""
    in
    let t = if obsolete then t ^ " (obsolete)" else t in
    goals_model#set ~row:a.Model.proof_row ~column:Model.time_column t


  let add_external_proof_row ~obsolete ~edit g p db_proof result (*_time*) =
    let parent = g.goal_row in
    let name = p.prover_name in
    let row = goals_model#prepend ~parent () in
    goals_model#set ~row ~column:icon_column !image_prover;
    goals_model#set ~row ~column:name_column
      (name ^ " " ^ p.prover_version);
    goals_model#set ~row ~column:visible_column true;
    goals_view#expand_row (goals_model#get_path parent);
    let a = { prover = p;
              proof_goal = g;
              proof_row = row;
              proof_db = db_proof;
(*
              status = status;
*)
              proof_obsolete = obsolete;
(*
              time = time;
              output = "";
*)
	      proof_state = result;
              edited_as = edit;
            }
    in
    goals_model#set ~row ~column:index_column (Row_proof_attempt a);
    Hashtbl.add g.external_proofs p.prover_id a;
    set_proof_state ~obsolete a result;
    a


  let add_goal_row parent name info t db_goal =
    let parent_row = match parent with
      | Theory mth -> mth.theory_row
      | Transf mtr -> mtr.transf_row
    in
    let row = goals_model#append ~parent:parent_row () in
    let goal = { goal_name = name;
		 parent = parent;
                 task = t ;
                 goal_row = row;
                 goal_db = db_goal;
                 external_proofs = Hashtbl.create 7;
                 transformations = Hashtbl.create 3;
                 proved = false;
               }
    in
    let text = match info with
      | None -> name
      | Some s -> s
    in
    goals_model#set ~row ~column:name_column text;
    goals_model#set ~row ~column:icon_column !image_file;
    goals_model#set ~row ~column:index_column (Row_goal goal);
    goals_model#set ~row ~column:visible_column true;
    goal


  let add_transformation_row g db_transf tr_name =
    let parent = g.Model.goal_row in
    let row = goals_model#append ~parent () in
    let tr = { Model.parent_goal = g;
               Model.transf_proved = false;
               Model.transf_row = row;
               Model.transf_db = db_transf;
               subgoals = [];
             }
    in
    goals_model#set ~row ~column:Model.name_column tr_name;
    goals_model#set ~row ~column:Model.icon_column !image_transf;
    goals_model#set ~row ~column:Model.index_column
      (Model.Row_transformation tr);
    goals_model#set ~row ~column:Model.visible_column true;
    goals_view#expand_row (goals_model#get_path parent);
    tr


  let add_theory_row mfile th db_theory =
    let tname = th.Theory.th_name.Ident.id_string in
    let parent = mfile.file_row in
    let row = goals_model#append ~parent () in
    let mth = { theory = th;
                theory_row = row;
                theory_db = db_theory;
                theory_parent = mfile;
                goals = [] ;
                verified = false }
    in
    goals_model#set ~row ~column:name_column tname;
    goals_model#set ~row ~column:icon_column !image_directory;
    goals_model#set ~row ~column:index_column (Row_theory mth);
    goals_model#set ~row ~column:visible_column true;
    mth

  let add_theory mfile th =
    let tasks = List.rev (Task.split_theory th None None) in
    let tname = th.Theory.th_name.Ident.id_string in
    let db_theory = Db.add_theory mfile.file_db tname in
    let mth = add_theory_row mfile th db_theory in
    let goals =
      List.fold_left
        (fun acc t ->
           let id = (Task.task_goal t).Decl.pr_name in
           let name = id.Ident.id_string in
           let expl = get_explanation id (Task.task_goal_fmla t) in
           let sum = task_checksum t in
           let db_goal = Db.add_goal db_theory name sum in
           let goal = add_goal_row (Theory mth) name expl t db_goal in
           goal :: acc)
        []
        tasks
    in
    mth.goals <- List.rev goals;
    if goals = [] then set_theory_proved ~propagate:false mth;
    mth

  let add_file_row f dbfile =
      let parent = goals_model#append () in
      let mfile = { file_name = f;
                    file_row = parent;
                    file_db = dbfile;
                    theories = [] ;
                    file_verified = false }
      in
      all_files := !all_files @ [mfile];
      let name = Filename.basename f in
      goals_model#set ~row:parent ~column:name_column name;
      goals_model#set ~row:parent ~column:icon_column !image_directory;
      goals_model#set ~row:parent ~column:index_column (Row_file mfile);
      goals_model#set ~row:parent ~column:visible_column true;
      mfile

  let add_file f =
    let theories = read_file f in
    let dbfile = Db.add_file f in
    let mfile = add_file_row f dbfile in
    let mths =
      List.fold_left
        (fun acc (_,thname,t) ->
           eprintf "Adding theory '%s'@." thname;
           let mth = add_theory mfile t in
           mth :: acc
        )
        [] theories
    in
    mfile.theories <- List.rev mths;
    if theories = [] then set_file_verified mfile

end

(*********************************)
(*  read previous data from db   *)
(*********************************)

type trans =
  | Trans_one of Task.task Trans.trans
  | Trans_list of Task.task Trans.tlist

let lookup_trans name =
  try
    let t = Trans.lookup_transform name gconfig.env in
    Trans_one t
  with Trans.UnknownTrans _ ->
    let t = Trans.lookup_transform_l name gconfig.env in
    Trans_list t

let trans_list =
  ["split_goal"; "inline_goal" ; "introduce_premises" ]

let trans_of_name =
  let h = Hashtbl.create 13 in
  List.iter
    (fun n -> Hashtbl.add h n (lookup_trans n))
    trans_list;
  Hashtbl.find h

let split_transformation = trans_of_name "split_goal"
let inline_transformation = trans_of_name "inline_goal"
let intro_transformation = trans_of_name "introduce_premises"


exception Not_applicable

let apply_trans t task =
  match t with
    | Trans_one t ->
	let t' = Trans.apply t task in
	if task == t' then raise Not_applicable; [t']
    | Trans_list t ->
	match Trans.apply t task with
	  | [t'] as l -> if task == t' then raise Not_applicable; l
	  | l -> l

let apply_transformation ~callback t task =
   match t with
    | Trans_one t ->
	let callback t = callback [t] in
	Gscheduler.apply_transformation ~callback t task
    | Trans_list t ->
	Gscheduler.apply_transformation_l ~callback t task


let rec reimport_any_goal parent gid gname t db_goal goal_obsolete =
  let info = get_explanation gid (Task.task_goal_fmla t) in
  let goal = Helpers.add_goal_row parent gname info t db_goal in
  let proved = ref false in
  let external_proofs = Db.external_proofs db_goal in
  Db.Hprover.iter
    (fun pid a ->
       let pname = Db.prover_name pid in
       try
         let p = Util.Mstr.find pname gconfig.provers in
         let s,t,o,edit = Db.status_and_time a in
         if goal_obsolete && not o then Db.set_obsolete a;
         let obsolete = goal_obsolete or o in
         let s = match s with
           | Db.Undone -> Call_provers.HighFailure
           | Db.Done r ->
	       if r = Call_provers.Valid then
		 if not obsolete then proved := true;
	       r
         in
	 let r = { Call_provers.pr_answer = s;
		   Call_provers.pr_output = "";
		   Call_provers.pr_time = t;
		 }
	 in
         let (_pa : Model.proof_attempt) =
           Helpers.add_external_proof_row ~obsolete ~edit goal p a
	     (Gscheduler.Done r)
         in
         ((* something TODO ?*))
       with Not_found ->
         eprintf
           "Warning: prover %s appears in database but is not installed.@."
           pname
    )
    external_proofs;
  let transformations = Db.transformations db_goal in
  Db.Htransf.iter
    (fun tr_id tr ->
       let trname = Db.transf_name tr_id in
       eprintf "Reimporting transformation %s for goal %s @." trname gname;
       let trans = trans_of_name trname in
       let subgoals = apply_trans trans t in
       let mtr = Helpers.add_transformation_row goal tr trname in
       let db_subgoals = Db.subgoals tr in
       let reimported_goals,db_subgoals,_ =
         List.fold_left
           (fun (acc,db_subgoals,count) subtask ->
              let id = (Task.task_goal subtask).Decl.pr_name in
              let subgoal_name = gname ^ "." ^ (string_of_int count) in
              let sum = task_checksum subtask in
              let subtask_db,db_subgoals =
                try
		  let g = Util.Mstr.find sum db_subgoals in
		  (* a subgoal has the same check sum *)
		  (Some g, Util.Mstr.remove sum db_subgoals)
                with Not_found -> None,db_subgoals
              in
              ((count,id,subgoal_name,subtask,sum,subtask_db) :: acc,
	       db_subgoals,
	       count+1))
           ([],db_subgoals,1) subgoals
       in
       let other_goals =
	 Util.Mstr.fold
	   (fun _ g acc -> (Db.goal_name g,g)::acc)
	   db_subgoals
	   []
       in
       let other_goals =
	 List.sort (fun (s1,_) (s2,_) -> String.compare s1 s2) other_goals
       in
       let rec merge_goals new_goals old_goals proved acc =
	 match new_goals with
	   | [] -> acc, proved
	   | (_,id,subgoal_name,subtask,sum,g_opt)::rem ->
	       let db_g,subgoal_obsolete,old_goals =
		 match g_opt with
		   | Some g -> g,false,old_goals
		   | None ->
		       match old_goals with
			 | [] ->
			     (* create a new goal in db *)
			     Db.add_subgoal tr subgoal_name sum,
			     false, old_goals
			 | (_goal_name,g) :: r ->
			     g, true, r
	       in
               let subgoal,subgoal_proved =
                 reimport_any_goal
                   (Model.Transf mtr) id
                   subgoal_name subtask db_g subgoal_obsolete
              in
              merge_goals rem old_goals (proved && subgoal_proved)
		(subgoal :: acc)
       in
       let goals, subgoals_proved =
	 merge_goals (List.rev reimported_goals) other_goals true []
       in
(*
       let goals,_,subgoals_proved =
         List.fold_left
           (fun (acc,count,proved) subtask ->
              let _id = (Task.task_goal subtask).Decl.pr_name in
              let subgoal_name = gname ^ "." ^ (string_of_int count) in
              let sum = task_checksum subtask in
              let subtask_db =
                try Util.Mstr.find sum db_subgoals
		  (* a subgoal has the same check sum *)
                with Not_found ->
		  (* otherwise, create a new one *)
                  Db.add_subgoal tr subgoal_name sum
              in
              let subgoal,subgoal_proved =
                reimport_any_goal
                  (Model.Transf mtr) subgoal_name subtask subtask_db
                  false (* subgoal_obsolete *)
              in
              (subgoal :: acc, count+1,proved && subgoal_proved))
           ([],1,true) subgoals
       in
*)
       mtr.Model.subgoals <- List.rev goals;
       if subgoals_proved (* TODO : && not obsolete *)
       then proved := true
    )
    transformations;
  if !proved then Helpers.set_proved ~propagate:false goal;
  goal,!proved


let reimport_root_goal mth tname goals t : Model.goal * bool =
  (* re-imports DB informations of a goal in theory mth (named tname)
     goals is a table, indexed by names of DB goals formerly known to be
     a in theory mth.  returns true whenever the task t is known to be
     proved *)
  let id = (Task.task_goal t).Decl.pr_name in
  let gname = id.Ident.id_string
  in
  let sum = task_checksum t in
  let db_goal,goal_obsolete =
    try
      let dbg = Util.Mstr.find gname goals in
      let db_sum = Db.task_checksum dbg in
      let goal_obsolete = sum <> db_sum in
      if goal_obsolete then
        begin
          eprintf "Goal %s.%s has changed@." tname gname;
          Db.change_checksum dbg sum
        end;
      dbg,goal_obsolete
    with Not_found ->
      let dbg = Db.add_goal mth.Model.theory_db gname sum in
      dbg,false
  in
  reimport_any_goal (Model.Theory mth) id gname t db_goal goal_obsolete

(* reimports all files *)
let files_in_db = Db.files ()

let () =
  List.iter
    (fun (f,fn) ->
       eprintf "Reimporting file '%s'@." fn;
       let mfile = Helpers.add_file_row fn f in
       try
	 let theories = read_file fn in
	 let ths = Db.theories f in
	 let (mths,file_proved) =
	   List.fold_left
             (fun (acc,file_proved) (_,tname,th) ->
		eprintf "Reimporting theory '%s'@."tname;
		let db_th =
		  try
                    Util.Mstr.find tname ths
		  with Not_found -> Db.add_theory f tname
		in
		let mth = Helpers.add_theory_row mfile th db_th in
		let goals = Db.goals db_th in
		let tasks = List.rev (Task.split_theory th None None) in
		let goals,proved = List.fold_left
		  (fun (acc,proved) t ->
                     let (g,p) = reimport_root_goal mth tname goals t in
                     (g::acc,proved && p))
		  ([],true) tasks
		in
		mth.Model.goals <- List.rev goals;
		(* TODO: what to do with remaining tasks in Db ???
		   for the moment they remain in the db, but they are not shown
		*)
		if proved then Helpers.set_theory_proved ~propagate:false mth;
		(mth::acc,file_proved && proved))
             ([],true) theories
	 in
	 (* TODO: detecter d'eventuelles vieilles theories, qui seraient donc
            dans [ths] mais pas dans [theories]
	 *)
	 mfile.Model.theories <- List.rev mths;
	 if file_proved then Helpers.set_file_verified mfile
      with e ->
	eprintf "@[Error while reading file@ '%s':@ %a@.@]" fn
          Exn_printer.exn_printer e;
	exit 1
    )
    files_in_db

(**********************************)
(* add new file from command line *)
(**********************************)

let () =
  match file_to_read with
    | None -> ()
    | Some fn ->
        if List.exists (fun (_,f) -> f = fn) files_in_db then
          eprintf "Info: file %s already in database@." fn
        else
          try
            Helpers.add_file fn
          with e ->
	    eprintf "@[Error while reading file@ '%s':@ %a@.@]" fn
              Exn_printer.exn_printer e;
	    exit 1


(**********************)
(* set up scheduler   *)
(**********************)

let () =
  begin
    Gscheduler.maximum_running_proofs := gconfig.max_running_processes
  end


(*****************************************************)
(* method: run a given prover on each unproved goals *)
(*****************************************************)

(* q is a queue of proof attempt where to put the new one *)
let redo_external_proof g a =
  let p = a.Model.prover in
  let callback result =
    Helpers.set_proof_state ~obsolete:false a result (*time*) ;
    let db_res, time =
      match result with
	| Gscheduler.Scheduled | Gscheduler.Running ->
	    Db.Undone, 0.0
	| Gscheduler.InternalFailure _ ->
	    Db.Done Call_provers.HighFailure, 0.0
	| Gscheduler.Done r ->
	    if r.Call_provers.pr_answer = Call_provers.Valid then
	      Helpers.set_proved ~propagate:true a.Model.proof_goal;
	    Db.Done r.Call_provers.pr_answer, r.Call_provers.pr_time
    in
    Db.set_status a.Model.proof_db db_res time
  in
  let old = if a.Model.edited_as = "" then None else
    begin
      eprintf "Info: proving using edited file %s@." a.Model.edited_as;
      (Some (open_in a.Model.edited_as))
    end
  in
  Gscheduler.schedule_proof_attempt
    ~debug:(gconfig.verbose > 0) ~timelimit:gconfig.time_limit ~memlimit:0
    ?old ~command:p.command ~driver:p.driver
    ~callback
    g.Model.task

let rec prover_on_goal p g =
  let id = p.prover_id in
  let a =
    try Hashtbl.find g.Model.external_proofs id
    with Not_found ->
      let db_prover = Db.prover_from_name id in
      let db_pa = Db.add_proof_attempt g.Model.goal_db db_prover in
      Helpers.add_external_proof_row ~obsolete:false ~edit:""
	g p db_pa Gscheduler.Scheduled
  in
  let () = redo_external_proof g a in
  Hashtbl.iter
    (fun _ t -> List.iter (prover_on_goal p) t.Model.subgoals)
    g.Model.transformations

let rec prover_on_goal_or_children p g =
  if not (g.Model.proved && !context_unproved_goals_only) then
    begin
      let r = ref true in
      Hashtbl.iter
	(fun _ t ->
	   r := false;
           List.iter (prover_on_goal_or_children p)
             t.Model.subgoals) g.Model.transformations;
      if !r then prover_on_goal p g
    end

let prover_on_selected_goal_or_children pr row =
  let row = filter_model#get_iter row in
  match filter_model#get ~row ~column:Model.index_column with
    | Model.Row_goal g ->
        prover_on_goal_or_children pr g
    | Model.Row_theory th ->
        List.iter (prover_on_goal_or_children pr) th.Model.goals
    | Model.Row_file file ->
        List.iter
          (fun th ->
             List.iter (prover_on_goal_or_children pr) th.Model.goals)
          file.Model.theories
    | Model.Row_proof_attempt a ->
        prover_on_goal_or_children pr a.Model.proof_goal
    | Model.Row_transformation tr ->
        List.iter (prover_on_goal_or_children pr) tr.Model.subgoals

let prover_on_selected_goals pr =
  List.iter
    (prover_on_selected_goal_or_children pr)
    goals_view#selection#get_selected_rows




(*****************************************************)
(* method: split selected goals *)
(*****************************************************)

let transformation_on_goal g trans_name trans =
  if not g.Model.proved then
    let callback subgoals =
      let b =
 	match subgoals with
	  | [task] ->
              let s1 = task_checksum g.Model.task in
              let s2 = task_checksum task in
	      (*
                eprintf "Transformation returned only one task. sum before = %s, sum after = %s@." (task_checksum g.Model.task) (task_checksum task);
                eprintf "addresses: %x %x@." (Obj.magic g.Model.task) (Obj.magic task);
	      *)
              s1 <> s2
                (* task != g.Model.task *)
	  | _ -> true
      in
      if b then
	let transf_id = Db.transf_from_name trans_name in
	let db_transf = Db.add_transformation g.Model.goal_db transf_id	in
	let tr = Helpers.add_transformation_row g db_transf trans_name in
	let goal_name = g.Model.goal_name in
	let fold =
	  fun (acc,count) subtask ->
	    let id = (Task.task_goal subtask).Decl.pr_name in
            let expl = 
              get_explanation id (Task.task_goal_fmla subtask)
            in
	    let subgoal_name =
	      goal_name ^ "." ^ (string_of_int count)
	    in
	    let sum = task_checksum subtask in
	    let subtask_db =
	      Db.add_subgoal db_transf subgoal_name sum
	    in
	    let goal =
	      Helpers.add_goal_row (Model.Transf tr)
		subgoal_name expl subtask subtask_db
	    in
	    (goal :: acc, count+1)
	in
	let goals,_ =
	  List.fold_left fold ([],1) subgoals
	in
	tr.Model.subgoals <- List.rev goals;
	Hashtbl.add g.Model.transformations trans_name tr
    in
    apply_transformation ~callback
      trans g.Model.task

let split_goal g = transformation_on_goal g "split_goal" split_transformation

let inline_goal g = transformation_on_goal g "inline_goal" inline_transformation

let rec split_goal_or_children g =
  if not g.Model.proved then
    begin
      let r = ref true in
      Hashtbl.iter
	(fun _ t ->
	   r := false;
           List.iter split_goal_or_children
             t.Model.subgoals) g.Model.transformations;
      if !r then split_goal g
    end

let rec inline_goal_or_children g =
  if not g.Model.proved then
    begin
      let r = ref true in
      Hashtbl.iter
	(fun _ t ->
	   r := false;
           List.iter inline_goal_or_children
             t.Model.subgoals) g.Model.transformations;
      if !r then inline_goal g
    end

let split_selected_goal_or_children row =
  let row = filter_model#get_iter row in
  match filter_model#get ~row ~column:Model.index_column with
    | Model.Row_goal g ->
        split_goal_or_children g
    | Model.Row_theory th ->
        List.iter split_goal_or_children th.Model.goals
    | Model.Row_file file ->
        List.iter
          (fun th ->
             List.iter split_goal_or_children th.Model.goals)
          file.Model.theories
    | Model.Row_proof_attempt a ->
        split_goal_or_children a.Model.proof_goal
    | Model.Row_transformation tr ->
        List.iter split_goal_or_children tr.Model.subgoals


let inline_selected_goal_or_children row =
  let row = filter_model#get_iter row in
  match filter_model#get ~row ~column:Model.index_column with
    | Model.Row_goal g ->
        inline_goal_or_children g
    | Model.Row_theory th ->
        List.iter inline_goal_or_children th.Model.goals
    | Model.Row_file file ->
        List.iter
          (fun th ->
             List.iter inline_goal_or_children th.Model.goals)
          file.Model.theories
    | Model.Row_proof_attempt a ->
        inline_goal_or_children a.Model.proof_goal
    | Model.Row_transformation tr ->
        List.iter inline_goal_or_children tr.Model.subgoals

let split_selected_goals () =
  List.iter
    split_selected_goal_or_children
    goals_view#selection#get_selected_rows


let inline_selected_goals () =
  List.iter
    inline_selected_goal_or_children
    goals_view#selection#get_selected_rows


(*********************************)
(* add a new file in the project *)
(*********************************)

let filter_all_files () =
  let f = GFile.filter ~name:"All" () in
  f#add_pattern "*" ;
  f

let filter_why_files () =
  GFile.filter
    ~name:"Why3 source files"
    ~patterns:[ "*.why"; "*.mlw"] ()

let select_file () =
  let d = GWindow.file_chooser_dialog ~action:`OPEN
    ~title:"Why3: Add file in project"
    ()
  in
  d#add_button_stock `CANCEL `CANCEL ;
  d#add_select_button_stock `OPEN `OPEN ;
  d#add_filter (filter_why_files ()) ;
  d#add_filter (filter_all_files ()) ;
  begin match d#run () with
  | `OPEN ->
      begin
        match d#filename with
          | None -> ()
          | Some f ->
	      let f = Sysutil.relativize_filename project_dir f in
              eprintf "Adding file '%s'@." f;
              try
                Helpers.add_file f
              with e ->
	        fprintf str_formatter
                  "@[Error while reading file@ '%s':@ %a@]" f
                  Exn_printer.exn_printer e;
	        let msg = flush_str_formatter () in
	        info_window `ERROR msg
      end
  | `DELETE_EVENT | `CANCEL -> ()
  end ;
  d#destroy ()


let not_implemented () =
  info_window `INFO "This feature is not yet implemented, sorry."

(*************)
(* File menu *)
(*************)

let file_menu = factory#add_submenu "_File"
let file_factory = new GMenu.factory file_menu ~accel_group

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~key:GdkKeysyms._A
    ~label:"_Add file" ~callback:select_file
    ()

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~label:"_Preferences" ~callback:
    (fun () ->
       Gconfig.preferences gconfig;
       Gscheduler.maximum_running_proofs := gconfig.max_running_processes)
    ()

let refresh_provers = ref (fun () -> ())

let add_refresh_provers f =
  let rp = !refresh_provers in
  refresh_provers := (fun () -> rp (); f ())

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~label:"_Detect provers" ~callback:
    (fun () -> Gconfig.run_auto_detection gconfig; !refresh_provers () )
    ()

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~key:GdkKeysyms._Q ~label:"_Quit"
    ~callback:exit_function ()

(*************)
(* View menu *)
(*************)

let view_menu = factory#add_submenu "_View"
let view_factory = new GMenu.factory view_menu ~accel_group
let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._E
    ~label:"Expand all" ~callback:(fun () -> goals_view#expand_all ()) ()



let rec collapse_proved_goal g =
  if g.Model.proved then
    begin
      let row = g.Model.goal_row in
      goals_view#collapse_row (goals_model#get_path row);
    end
  else
    Hashtbl.iter
      (fun _ t -> List.iter collapse_proved_goal t.Model.subgoals)
      g.Model.transformations

let collapse_verified_theory th =
  if th.Model.verified then
    begin
      let row = th.Model.theory_row in
      goals_view#collapse_row (goals_model#get_path row);
    end
  else
    List.iter collapse_proved_goal th.Model.goals

let collapse_verified_file f =
  if f.Model.file_verified then
    begin
      let row = f.Model.file_row in
      goals_view#collapse_row (goals_model#get_path row);
    end
  else
    List.iter collapse_verified_theory f.Model.theories

let collapse_all_verified_things () =
  List.iter collapse_verified_file !Model.all_files

let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._C
    ~label:"Collapse proved goals"
    ~callback:collapse_all_verified_things
    ()

let rec hide_proved_in_goal g =
  if g.Model.proved then
    begin
      let row = g.Model.goal_row in
      goals_view#collapse_row (goals_model#get_path row);
      goals_model#set ~row ~column:Model.visible_column false
    end
  else
    Hashtbl.iter
      (fun _ t -> List.iter hide_proved_in_goal t.Model.subgoals)
      g.Model.transformations

let hide_proved_in_theory th =
  if th.Model.verified then
    begin
      let row = th.Model.theory_row in
      goals_view#collapse_row (goals_model#get_path row);
      goals_model#set ~row ~column:Model.visible_column false
    end
  else
    List.iter hide_proved_in_goal th.Model.goals

let hide_proved_in_file f =
  if f.Model.file_verified then
    begin
      let row = f.Model.file_row in
      goals_view#collapse_row (goals_model#get_path row);
      goals_model#set ~row ~column:Model.visible_column false
    end
  else
    List.iter hide_proved_in_theory f.Model.theories

let hide_proved_in_files () =
  List.iter hide_proved_in_file !Model.all_files

let rec show_all_in_goal g =
  let row = g.Model.goal_row in
  goals_model#set ~row ~column:Model.visible_column true;
  if g.Model.proved then
    goals_view#collapse_row (goals_model#get_path row)
  else
    goals_view#expand_row (goals_model#get_path row);
  Hashtbl.iter
    (fun _ t -> List.iter show_all_in_goal t.Model.subgoals)
    g.Model.transformations

let show_all_in_theory th =
  let row = th.Model.theory_row in
  goals_model#set ~row ~column:Model.visible_column true;
  if th.Model.verified then
    goals_view#collapse_row (goals_model#get_path row)
  else
    begin
      goals_view#expand_row (goals_model#get_path row);
      List.iter show_all_in_goal th.Model.goals
    end

let show_all_in_file f =
  let row = f.Model.file_row in
  goals_model#set ~row ~column:Model.visible_column true;
  if f.Model.file_verified then
    goals_view#collapse_row (goals_model#get_path row)
  else
    begin
      goals_view#expand_row (goals_model#get_path row);
      List.iter show_all_in_theory f.Model.theories
    end

let show_all_in_files () =
  List.iter show_all_in_file !Model.all_files


let (_ : GMenu.check_menu_item) = view_factory#add_check_item
  ~callback:(fun b ->
               Model.toggle_hide_proved_goals := b;
               if b then hide_proved_in_files ()
               else show_all_in_files ())
  "Hide proved goals"


(**************)
(* Tools menu *)
(**************)


let () = add_refresh_provers (fun () ->
  List.iter (fun item -> item#destroy ()) provers_box#all_children)

let tools_menu = factory#add_submenu "_Tools"
let tools_factory = new GMenu.factory tools_menu ~accel_group

let () = add_refresh_provers (fun () ->
  List.iter (fun item -> item#destroy ()) tools_menu#all_children)

let () =
  let add_item_provers () =
    Util.Mstr.iter
      (fun _ p ->
         let n = p.prover_name ^ " " ^ p.prover_version in
         let (_ : GMenu.image_menu_item) =
           tools_factory#add_image_item ~label:n
             ~callback:(fun () -> prover_on_selected_goals p)
             ()
         in
         let b = GButton.button ~packing:provers_box#add ~label:n () in
(* prend de la place pour rien
         let i = GMisc.image ~pixbuf:(!image_prover) () in
         let () = b#set_image i#coerce in
*)
         let (_ : GtkSignal.id) =
           b#connect#pressed
             ~callback:(fun () -> prover_on_selected_goals p)
         in ())
      gconfig.provers
  in
  add_refresh_provers add_item_provers;
  add_item_provers ()

let () =
  let add_item_split () =
    ignore(tools_factory#add_image_item
             ~label:"Split selection"
             ~callback:split_selected_goals
             () : GMenu.image_menu_item) in
  add_refresh_provers add_item_split;
  add_item_split ()


let () =
  let b = GButton.button ~packing:transf_box#add ~label:"Split" () in
  let i = GMisc.image ~pixbuf:(!image_transf) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:split_selected_goals
  in ()

let () =
  let b = GButton.button ~packing:transf_box#add ~label:"Inline" () in
(**)
  let i = GMisc.image ~pixbuf:(!image_transf) () in
  let () = b#set_image i#coerce in
(**)
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:inline_selected_goals
  in ()



(*************)
(* Help menu *)
(*************)


let help_menu = factory#add_submenu "_Help"
let help_factory = new GMenu.factory help_menu ~accel_group

let (_ : GMenu.image_menu_item) =
  help_factory#add_image_item
    ~label:"Legend"
    ~callback:show_legend_window
    ()

let (_ : GMenu.image_menu_item) =
  help_factory#add_image_item
    ~label:"About"
    ~callback:show_about_window
    ()


(******************************)
(* vertical paned on the right*)
(******************************)

let right_vb = GPack.vbox ~packing:hp#add ()

let vp =
  try
    GPack.paned `VERTICAL ~packing:right_vb#add ()
  with Gtk.Error _ -> assert false

let right_hb = GPack.hbox ~packing:(right_vb#pack ~expand:false) ()

let file_info = GMisc.label ~text:""
  ~packing:(right_hb#pack ~fill:true) ()

let current_file = ref ""

let set_current_file f =
  current_file := f;
  file_info#set_text ("file: " ^ !current_file)

(******************)
(* goal text view *)
(******************)

let scrolled_task_view = GBin.scrolled_window
  ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
  ~packing:vp#add ()

let () = scrolled_task_view#set_shadow_type `ETCHED_OUT

let (_ : GtkSignal.id) =
  scrolled_task_view#misc#connect#size_allocate
    ~callback:
    (fun {Gtk.width=_w;Gtk.height=h} ->
       gconfig.task_height <- h)

let task_view =
  GSourceView2.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_task_view#add
    ~height:gconfig.task_height
    ()

let () = task_view#source_buffer#set_language lang
let () = task_view#set_highlight_current_line true

(***************)
(* source view *)
(***************)

let scrolled_source_view = GBin.scrolled_window
  ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
  ~packing:vp#add
  ()

let () = scrolled_source_view#set_shadow_type `ETCHED_OUT

let source_view =
  GSourceView2.source_view
    ~auto_indent:true
    ~insert_spaces_instead_of_tabs:true ~tab_width:2
    ~show_line_numbers:true
    ~right_margin_position:80 ~show_right_margin:true
    (* ~smart_home_end:true *)
    ~packing:scrolled_source_view#add
    ()

(*
  source_view#misc#modify_font_by_name font_name;
*)
let () = source_view#source_buffer#set_language lang
let () = source_view#set_highlight_current_line true
(*
let () = source_view#source_buffer#set_text (source_text fname)
*)

let move_to_line (v : GSourceView2.source_view) line =
  if line <= v#buffer#line_count && line <> 0 then begin
    let it = v#buffer#get_iter (`LINE line) in
    let mark = `MARK (v#buffer#create_mark it) in
    v#scroll_to_mark ~use_align:true ~yalign:0.0 mark
  end

let orange_bg = source_view#buffer#create_tag
  ~name:"orange_bg" [`BACKGROUND "orange"]

let erase_color_loc (v:GSourceView2.source_view) =
  let buf = v#buffer in
  buf#remove_tag orange_bg ~start:buf#start_iter ~stop:buf#end_iter

let color_loc (v:GSourceView2.source_view) l b e =
  let buf = v#buffer in
  let top = buf#start_iter in
  let start = top#forward_lines (l-1) in
  let start = start#forward_chars b in
  let stop = start#forward_chars (e-b) in
  buf#apply_tag ~start ~stop orange_bg

let scroll_to_id id =
  match id.Ident.id_origin with
    | Ident.User loc ->
        let (f,l,b,e) = Loc.get loc in
        if f <> !current_file then
          begin
            source_view#source_buffer#set_text (source_text f);
            set_current_file f;
          end;
        move_to_line source_view (l-1);
        erase_color_loc source_view;
        color_loc source_view l b e
    | Ident.Fresh ->
        source_view#source_buffer#set_text
          "Fresh ident (no position available)\n";
        set_current_file ""
    | Ident.Derived _ ->
        source_view#source_buffer#set_text
          "Derived ident (no position available)\n";
        set_current_file ""

let color_loc loc =
  let f, l, b, e = Loc.get loc in
  if f = !current_file then color_loc source_view l b e

let rec color_f_locs () f =
  Util.option_iter color_loc f.Term.f_loc;
  Term.f_fold color_t_locs color_f_locs () f

and color_t_locs () t =
  Util.option_iter color_loc t.Term.t_loc;
  Term.t_fold color_t_locs color_f_locs () t

let scroll_to_source_goal g =
  let t = g.Model.task in
  let id = (Task.task_goal t).Decl.pr_name in
  scroll_to_id id;
  match t with
    | Some
        { Task.task_decl =
            { Theory.td_node =
                Theory.Decl { Decl.d_node = Decl.Dprop (Decl.Pgoal, _, f)}}} ->
        color_f_locs () f
    | _ ->
        assert false

let scroll_to_theory th =
  let t = th.Model.theory in
  let id = t.Theory.th_name in
  scroll_to_id id

(* to be run when a row in the tree view is selected *)
let select_row p =
  let row = filter_model#get_iter p in
  match filter_model#get ~row ~column:Model.index_column with
    | Model.Row_goal g ->
        let t = g.Model.task in
        let t = match apply_trans intro_transformation t with
	  | [t] -> t
	  | _ -> assert false
	in
        let task_text = Pp.string_of Pretty.print_task t in
        task_view#source_buffer#set_text task_text;
        task_view#scroll_to_mark `INSERT;
        scroll_to_source_goal g
    | Model.Row_theory th ->
        task_view#source_buffer#set_text "";
        scroll_to_theory th
    | Model.Row_file _file ->
        task_view#source_buffer#set_text "";
        (* scroll_to_file file *)
    | Model.Row_proof_attempt a ->
	let o =
          match a.Model.proof_state with
	    | Gscheduler.Done r -> r.Call_provers.pr_output;
	    | _ -> "No information available"
	in
	task_view#source_buffer#set_text o;
        scroll_to_source_goal a.Model.proof_goal
    | Model.Row_transformation tr ->
        task_view#source_buffer#set_text "";
        scroll_to_source_goal tr.Model.parent_goal




(*****************************)
(* method: edit current goal *)
(*****************************)


let ft_of_th th =
  (Filename.basename th.Model.theory_parent.Model.file_name,
   th.Model.theory.Theory.th_name.Ident.id_string)

let rec ft_of_goal g =
  match g.Model.parent with
    | Model.Transf tr -> ft_of_goal tr.Model.parent_goal
    | Model.Theory th -> ft_of_th th

let ft_of_pa a =
  ft_of_goal a.Model.proof_goal

let edit_selected_row p =
  let row = filter_model#get_iter p in
  match filter_model#get ~row ~column:Model.index_column with
    | Model.Row_goal _g ->
        ()
    | Model.Row_theory _th ->
        ()
    | Model.Row_file _file ->
        ()
    | Model.Row_proof_attempt a ->
        let g = a.Model.proof_goal in
	let t = g.Model.task in
	let driver = a.Model.prover.driver in
	let file =
          match a.Model.edited_as with
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
		a.Model.edited_as <- file;
		Db.set_edited_as a.Model.proof_db file;
		file
	    | f -> f
	in
        let old_status = a.Model.proof_state in
        Helpers.set_proof_state ~obsolete:false a Gscheduler.Running;
        let callback () =
          Helpers.set_proof_state ~obsolete:false a old_status;
        in
        let editor =
          match a.Model.prover.editor with
            | "" -> gconfig.default_editor
            | _ -> a.Model.prover.editor
        in
        Gscheduler.edit_proof ~debug:false ~editor
          ~file
          ~driver
          ~callback
          t
    | Model.Row_transformation _tr ->
        ()

let edit_current_proof () =
  match goals_view#selection#get_selected_rows with
    | [] -> ()
    | [r] -> edit_selected_row r
    | _ ->
	info_window `INFO "Please select exactly one proof to edit"


let add_item_edit () =
  ignore (tools_factory#add_image_item
            ~label:"Edit current proof"
            ~callback:edit_current_proof
            () : GMenu.image_menu_item)

let () =
  add_refresh_provers add_item_edit;
  add_item_edit ()


let () =
  let b = GButton.button ~packing:tools_box#add ~label:"Edit" () in
  let i = GMisc.image ~pixbuf:(!image_editor) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:edit_current_proof
  in ()

let () =
  let b = GButton.button ~packing:tools_box#add ~label:"(Replay)" () in
(*
  let i = GMisc.image ~pixbuf:(!image_replay) () in
  let () = b#set_image i#coerce in
*)
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:not_implemented
  in ()

(*************)
(* removing  *)
(*************)

let remove_proof_attempt a =
  Db.remove_proof_attempt a.Model.proof_db;
  let (_:bool) = goals_model#remove a.Model.proof_row in
  let g = a.Model.proof_goal in
  Hashtbl.remove g.Model.external_proofs a.Model.prover.prover_id;
  Helpers.check_goal_proved g

let remove_transf t =
  (* TODO: remove subgoals first !!! *)
  Db.remove_transformation t.Model.transf_db;
  let (_:bool) = goals_model#remove t.Model.transf_row in
  let g = t.Model.parent_goal in
  Hashtbl.remove g.Model.transformations "split" (* hack !! *);
  Helpers.check_goal_proved g


let confirm_remove_row r =
  let row = filter_model#get_iter r in
  match filter_model#get ~row ~column:Model.index_column with
    | Model.Row_goal _g ->
	info_window `ERROR "Cannot remove a goal"
    | Model.Row_theory _th ->
	info_window `ERROR "Cannot remove a theory"
    | Model.Row_file _file ->
	info_window `ERROR "Cannot remove a file"
    | Model.Row_proof_attempt a ->
	info_window
	  ~callback:(fun () -> remove_proof_attempt a)
	  `QUESTION
	  "Do you really want to remove the selected proof attempt?"
    | Model.Row_transformation tr ->
	info_window
	  ~callback:(fun () -> remove_transf tr)
	  `QUESTION
	  "Do you really want to remove the selected transformation
and all its subgoals?"

let confirm_remove_selection () =
  match goals_view#selection#get_selected_rows with
    | [] -> ()
    | [r] -> confirm_remove_row r
    | _ ->
        info_window `INFO "Please select exactly one item to remove"

let () =
  let b = GButton.button ~packing:cleaning_box#add ~label:"Remove" () in
  let i = GMisc.image ~pixbuf:(!image_remove) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:confirm_remove_selection
  in ()


(***************)
(* Bind events *)
(***************)

(* row selection on tree view on the left *)
let (_ : GtkSignal.id) =
  goals_view#selection#connect#after#changed ~callback:
    begin fun () ->
      match goals_view#selection#get_selected_rows with
        | [p] -> select_row p
        | [] -> ()
        | _ -> ()
    end

let () = w#add_accel_group accel_group
let () = w#show ()
let () = GMain.main ()

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
