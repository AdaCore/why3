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
    Util.Mstr.fold (Session.get_prover_data c.env) provers Util.Mstr.empty;
  c

let () =
  Whyconf.load_plugins (get_main ())



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
  ~title:"Why Graphical session manager" ()

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
  b1#misc#set_tooltip_markup "When selected, tools below are applied\nonly on <b>unproved</b> goals";
  let (_ : GtkSignal.id) =
    b1#connect#clicked
      ~callback:(fun () -> context_unproved_goals_only := true)
  in
  let b2 = GButton.radio_button
    ~group:b1#group ~packing:context_box#add ~label:"All goals" ()
  in
  b2#misc#set_tooltip_markup "When selected, tools below are applied\nto all goals";
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


(* connecting to the Session model *)


(****************)
(* goals widget *)
(****************)

let cols = new GTree.column_list
let name_column = cols#add Gobject.Data.string
let icon_column = cols#add Gobject.Data.gobject
let status_column = cols#add Gobject.Data.gobject
let time_column = cols#add Gobject.Data.string
let index_column = cols#add Gobject.Data.int

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


let goals_model,goals_view =
  eprintf "Creating tree model...@?";
  let model = GTree.tree_store cols in
  let view = GTree.view ~model ~packing:scrollview#add () in
  (*
    let () = view#selection#set_mode `SINGLE in
  *)
  let () = view#selection#set_mode `MULTIPLE in
  let () = view#set_rules_hint true in
  ignore (view#append_column view_name_column);
  ignore (view#append_column view_status_column);
  ignore (view#append_column view_time_column);
  eprintf " done@.";
  model,view

let clear model = model#clear ()

let image_of_result ~obsolete result =
  match result with
    | Session.Undone -> !image_scheduled (* TODO *)
    | Session.Scheduled -> !image_scheduled
    | Session.Running -> !image_running
    | Session.InternalFailure _ -> !image_failure
    | Session.Done r -> match r.Call_provers.pr_answer with
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


module M = Session.Make
  (struct
     type key = Gtk.tree_iter

     let create ?parent () = goals_model#append ?parent ()

     let remove row =
       let (_:bool) = goals_model#remove row in ()

     let idle f =
       let (_ : GMain.Idle.id) = GMain.Idle.add f in
       ()

     let timeout ~ms f =
       let (_ : GMain.Timeout.id) = GMain.Timeout.add ~ms ~callback:f in
       ()

   end)

let set_row_status row b =
  if b then
    begin
      goals_view#collapse_row (goals_model#get_path row);
      goals_model#set ~row ~column:status_column !image_yes;
    end
  else
    begin
      goals_model#set ~row ~column:status_column !image_unknown;
    end

let set_proof_state ~obsolete a =
  let row = a.M.proof_key in
  let res = a.M.proof_state in
  goals_model#set ~row ~column:status_column
    (image_of_result ~obsolete res);
  let t = match res with
    | Session.Done { Call_provers.pr_time = time } ->
	Format.sprintf "%.2f" time
    | _ -> ""
  in
  let t = if obsolete then t ^ " (obsolete)" else t in
  goals_model#set ~row ~column:time_column t

let model_index = Hashtbl.create 17

let get_any row = 
  try 
    let row = goals_model#get_iter row in
    let idx = goals_model#get ~row ~column:index_column in
    Hashtbl.find model_index idx
  with Not_found -> invalid_arg "Gmain.get_index"

let init = 
  let cpt = ref 0 in 
  fun row any ->
    incr cpt;
    Hashtbl.add model_index !cpt any;
    goals_model#set ~row ~column:index_column !cpt;
    goals_model#set ~row ~column:icon_column 
      (match any with
	 | M.Goal _ -> !image_file
	 | M.Theory _ 
	 | M.File _ -> !image_directory
	 | M.Proof_attempt _ -> !image_prover
	 | M.Transformation _ -> !image_transf);
    goals_model#set ~row ~column:name_column 
      (match any with
	 | M.Goal g -> 
	     (match g.M.goal_expl with 
		| None -> g.M.goal_name
		| Some s -> s)
	 | M.Theory th -> th.M.theory.Theory.th_name.Ident.id_string
	 | M.File f -> Filename.basename f.M.file_name
	 | M.Proof_attempt a -> let p = a.M.prover in
	   p.Session.prover_name ^ " " ^ p.Session.prover_version
	 | M.Transformation tr -> Session.transformation_id tr.M.transf)
      
let notify any =
  match any with
    | M.Goal g ->
	set_row_status g.M.goal_key g.M.proved
    | M.Theory th ->
	set_row_status th.M.theory_key th.M.verified
    | M.File file ->
	set_row_status file.M.file_key file.M.file_verified
    | M.Proof_attempt a ->
	set_proof_state ~obsolete:false a
    | M.Transformation tr ->
	set_row_status tr.M.transf_key tr.M.transf_proved


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
  let dbfname = Filename.concat project_dir "project.xml" in
  try
    eprintf "Opening session...@?";
    M.open_session ~init ~notify dbfname;
    M.maximum_running_proofs := gconfig.max_running_processes;
    eprintf " done@."
  with e ->
    eprintf "Error while opening session with database '%s'@." dbfname;
    eprintf "Aborting...@.";
    raise e


let read_file fn =
  let fn = Filename.concat project_dir fn in
  Env.read_file gconfig.env fn





(* *)

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




(*
  let check_file_verified f =
    let b = List.for_all (fun t -> t.M.verified) f.M.theories in
    if f.M.file_verified <> b then
      begin
	f.M.file_verified <- b;
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

*)

(*

  (* deprecated *)
  let set_file_verified f =
    f.file_verified <- true;
    let row = f.file_row in
    goals_view#collapse_row (goals_model#get_path row);
    goals_model#set ~row ~column:status_column !image_yes
(*
    if !toggle_hide_proved_goals then
      goals_model#set ~row ~column:visible_column false
*)

  (* deprecated *)
  let set_theory_proved ~propagate  t =
    t.verified <- true;
    let row = t.theory_row in
    goals_view#collapse_row (goals_model#get_path row);
    goals_model#set ~row ~column:status_column !image_yes;
(*
    if !toggle_hide_proved_goals then
      goals_model#set ~row ~column:visible_column false;
*)
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
(*
    if !toggle_hide_proved_goals then
      goals_model#set ~row ~column:visible_column false;
*)
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
(*
    goals_model#set ~row ~column:visible_column true;
*)
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
(*
    goals_model#set ~row ~column:visible_column true;
*)
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
    Hashtbl.add g.Model.transformations tr_name tr;
    goals_model#set ~row ~column:Model.name_column tr_name;
    goals_model#set ~row ~column:Model.icon_column !image_transf;
    goals_model#set ~row ~column:Model.index_column
      (Model.Row_transformation tr);
(*
    goals_model#set ~row ~column:Model.visible_column true;
*)
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
(*
    goals_model#set ~row ~column:visible_column true;
*)
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
(*
      goals_model#set ~row:parent ~column:visible_column true;
*)
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

*)


(**********************************)
(* add new file from command line *)
(**********************************)

let () =
  match file_to_read with
    | None -> ()
    | Some fn ->
        if M.file_exists fn then
          eprintf "Info: file %s already in database@." fn
        else
          try
            M.add_file fn (read_file fn)
          with e ->
	    eprintf "@[Error while reading file@ '%s':@ %a@.@]" fn
              Exn_printer.exn_printer e;
	    exit 1




(*****************************************************)
(* method: run a given prover on each unproved goals *)
(*****************************************************)

let prover_on_selected_goals pr =
  List.iter
    (fun row ->
       let a = get_any row in
        M.run_prover
          ~context_unproved_goals_only:!context_unproved_goals_only
          pr a)
    goals_view#selection#get_selected_rows

(**********************************)
(* method: replay obsolete proofs *)
(**********************************)

let replay_obsolete_proofs () =
  List.iter
    (fun row ->
       let a = get_any row in
       M.replay ~context_unproved_goals_only:!context_unproved_goals_only a)
    goals_view#selection#get_selected_rows



(*****************************************************)
(* method: split selected goals *)
(*****************************************************)

let lookup_trans = Session.lookup_transformation gconfig.env
let split_transformation = lookup_trans "split_goal"
let inline_transformation = lookup_trans "inline_goal"
let intro_transformation = lookup_trans "introduce_premises"


let apply_trans_on_selection tr =
  List.iter
    (fun row ->
       let a = get_any row in
        M.transform
          ~context_unproved_goals_only:!context_unproved_goals_only
	  tr
          a)
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
                M.add_file f (read_file f)
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
       M.maximum_running_proofs := gconfig.max_running_processes)
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
  if g.M.proved then
    begin
      let row = g.M.goal_key in
      goals_view#collapse_row (goals_model#get_path row);
    end
  else
    Hashtbl.iter
      (fun _ t -> List.iter collapse_proved_goal t.M.subgoals)
      g.M.transformations

let collapse_verified_theory th =
  if th.M.verified then
    begin
      let row = th.M.theory_key in
      goals_view#collapse_row (goals_model#get_path row);
    end
  else
    List.iter collapse_proved_goal th.M.goals

let collapse_verified_file f =
  if f.M.file_verified then
    begin
      let row = f.M.file_key in
      goals_view#collapse_row (goals_model#get_path row);
    end
  else
    List.iter collapse_verified_theory f.M.theories

let collapse_all_verified_things () =
  List.iter collapse_verified_file (M.get_all_files ())

let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._C
    ~label:"Collapse proved goals"
    ~callback:collapse_all_verified_things
    ()

(*
let rec hide_proved_in_goal g =
  if g.M.proved then
    begin
      let row = g.M.goal_row in
      goals_view#collapse_row (goals_model#get_path row);
(*
      goals_model#set ~row ~column:M.visible_column false
*)
    end
  else
    Hashtbl.iter
      (fun _ t -> List.iter hide_proved_in_goal t.M.subgoals)
      g.M.transformations

let hide_proved_in_theory th =
  if th.M.verified then
    begin
      let row = th.M.theory_row in
      goals_view#collapse_row (goals_model#get_path row);
      goals_model#set ~row ~column:M.visible_column false
    end
  else
    List.iter hide_proved_in_goal th.M.goals

let hide_proved_in_file f =
  if f.M.file_verified then
    begin
      let row = f.M.file_row in
      goals_view#collapse_row (goals_model#get_path row);
      goals_model#set ~row ~column:M.visible_column false
    end
  else
    List.iter hide_proved_in_theory f.M.theories

let hide_proved_in_files () =
  List.iter hide_proved_in_file !M.all_files

let rec show_all_in_goal g =
  let row = g.M.goal_row in
  goals_model#set ~row ~column:M.visible_column true;
  if g.M.proved then
    goals_view#collapse_row (goals_model#get_path row)
  else
    goals_view#expand_row (goals_model#get_path row);
  Hashtbl.iter
    (fun _ t -> List.iter show_all_in_goal t.M.subgoals)
    g.M.transformations

let show_all_in_theory th =
  let row = th.M.theory_row in
  goals_model#set ~row ~column:M.visible_column true;
  if th.M.verified then
    goals_view#collapse_row (goals_model#get_path row)
  else
    begin
      goals_view#expand_row (goals_model#get_path row);
      List.iter show_all_in_goal th.M.goals
    end

let show_all_in_file f =
  let row = f.M.file_row in
  goals_model#set ~row ~column:M.visible_column true;
  if f.M.file_verified then
    goals_view#collapse_row (goals_model#get_path row)
  else
    begin
      goals_view#expand_row (goals_model#get_path row);
      List.iter show_all_in_theory f.M.theories
    end

let show_all_in_files () =
  List.iter show_all_in_file !M.all_files


let (_ : GMenu.check_menu_item) = view_factory#add_check_item
  ~callback:(fun b ->
               M.toggle_hide_proved_goals := b;
               if b then hide_proved_in_files ()
               else show_all_in_files ())
  "Hide proved goals"

*)

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
         let n = p.Session.prover_name ^ " " ^ p.Session.prover_version in
         let (_ : GMenu.image_menu_item) =
           tools_factory#add_image_item ~label:n
             ~callback:(fun () -> prover_on_selected_goals p)
             ()
         in
         let b = GButton.button ~packing:provers_box#add ~label:n () in
         b#misc#set_tooltip_markup "Click to start this prover\non the <b>selected</b> goal(s)";

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

let split_selected_goals () =
  apply_trans_on_selection split_transformation

let inline_selected_goals () =
  apply_trans_on_selection inline_transformation

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
  b#misc#set_tooltip_markup "Click to apply transformation <tt>split_goal</tt> to the <b>selected goals</b>";

  let i = GMisc.image ~pixbuf:(!image_transf) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:split_selected_goals
  in
  ()

let () =
  let b = GButton.button ~packing:transf_box#add ~label:"Inline" () in
  b#misc#set_tooltip_markup "Click to apply transformation <tt>inline_goal</tt> to the <b>selected goals</b>";
  let i = GMisc.image ~pixbuf:(!image_transf) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:inline_selected_goals
  in 
  ()



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
  let t = g.M.task in
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
  let t = th.M.theory in
  let id = t.Theory.th_name in
  scroll_to_id id

(* to be run when a row in the tree view is selected *)
let select_row p =
  let a = get_any p in
  match a with
    | M.Goal g ->
	let callback = function
	  | [t] -> 
              let task_text = Pp.string_of Pretty.print_task t in
              task_view#source_buffer#set_text task_text;
              task_view#scroll_to_mark `INSERT;
              scroll_to_source_goal g
	  | _ -> assert false
	in	
        M.apply_transformation ~callback intro_transformation g.M.task

    | M.Theory th ->
        task_view#source_buffer#set_text "";
        scroll_to_theory th
    | M.File _file ->
        task_view#source_buffer#set_text "";
        (* scroll_to_file file *)
    | M.Proof_attempt a ->
	let o =
          match a.M.proof_state with
	    | Session.Done r -> r.Call_provers.pr_output;
	    | _ -> "No information available"
	in
	task_view#source_buffer#set_text o;
        scroll_to_source_goal a.M.proof_goal
    | M.Transformation tr ->
        task_view#source_buffer#set_text "";
        scroll_to_source_goal tr.M.parent_goal




(*****************************)
(* method: edit current goal *)
(*****************************)

let edit_selected_row p =
  match get_any p with
    | M.Goal _g ->
        ()
    | M.Theory _th ->
        ()
    | M.File _file ->
        ()
    | M.Proof_attempt a ->
        M.edit_proof ~default_editor:gconfig.default_editor
          ~project_dir a
    | M.Transformation _ -> ()

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
  b#misc#set_tooltip_markup "Click to edit the <b>selected proof</b>\nwith the appropriate editor";

  let i = GMisc.image ~pixbuf:(!image_editor) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:edit_current_proof
  in ()

let () =
  let b = GButton.button ~packing:tools_box#add ~label:"Replay" () in
  b#misc#set_tooltip_markup "Replay all the <b>successful</b> but <b>obsolete</b> proofs below the current selection";

  let i = GMisc.image ~pixbuf:(!image_replay) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:replay_obsolete_proofs
  in ()

(*************)
(* removing  *)
(*************)

(*

let confirm_remove_row r =
  let row = goals_model#get_iter r in
  match goals_model#get ~row ~column:M.index_column with
    | M.Row_goal _g ->
	info_window `ERROR "Cannot remove a goal"
    | M.Row_theory _th ->
	info_window `ERROR "Cannot remove a theory"
    | M.Row_file _file ->
	info_window `ERROR "Cannot remove a file"
    | M.Row_proof_attempt a ->
	info_window
	  ~callback:(fun () -> remove_proof_attempt a)
	  `QUESTION
	  "Do you really want to remove the selected proof attempt?"
    | M.Row_transformation tr ->
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
  b#misc#set_tooltip_markup "Removes the selected\n<b>proof</b> or <b>transformation</b>";
  let i = GMisc.image ~pixbuf:(!image_remove) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:confirm_remove_selection
  in ()

let rec clean_goal g =
  if g.M.proved then
    begin
      Hashtbl.iter
        (fun _ a ->
           if a.M.proof_obsolete || not (proof_successful a) then
             remove_proof_attempt a)
        g.M.external_proofs;
      Hashtbl.iter
        (fun _ t ->
           if not t.M.transf_proved then
             remove_transf t)
        g.M.transformations
    end
  else
    Hashtbl.iter
      (fun _ t -> List.iter clean_goal t.M.subgoals)
      g.M.transformations


let clean_row r =
  let row = goals_model#get_iter r in
  match goals_model#get ~row ~column:M.index_column with
    | M.Row_goal g -> clean_goal g
    | M.Row_theory th ->
        List.iter clean_goal th.M.goals
    | M.Row_file file ->
        List.iter
          (fun th ->
             List.iter clean_goal th.M.goals)
          file.M.theories
    | M.Row_proof_attempt a ->
        clean_goal a.M.proof_goal
    | M.Row_transformation tr ->
        List.iter clean_goal tr.M.subgoals

let clean_selection () =
  List.iter clean_row goals_view#selection#get_selected_rows

let () =
  let b = GButton.button ~packing:cleaning_box#add ~label:"Clean" () in
  b#misc#set_tooltip_markup "Removes non successful proof_attempts\nassociated to a proved goal";
  let i = GMisc.image ~pixbuf:(!image_cleaning) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:clean_selection
  in ()

*)

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
