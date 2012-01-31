(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
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


open Format

let () =
  eprintf "[Info] Init the GTK interface...@?";
  ignore (GtkMain.Main.init ());
  eprintf " done.@."


open Why3
open Whyconf
open Gconfig
open Util
open Debug
module C = Whyconf

let debug = register_flag "gui"

(************************)
(* parsing command line *)
(************************)

let includes = ref []
let file = ref None
let opt_version = ref false
let opt_config = ref None

let spec = Arg.align [
  ("-L",
   Arg.String (fun s -> includes := s :: !includes),
   "<s> add s to loadpath") ;
  ("--library",
   Arg.String (fun s -> includes := s :: !includes),
   " same as -L") ;
  ("-I",
   Arg.String (fun s -> includes := s :: !includes),
   " same as -L (obsolete)") ;
  "-C", Arg.String (fun s -> opt_config := Some s),
      "<file> Read configuration from <file>";
  "--config", Arg.String (fun s -> opt_config := Some s),
      " same as -C";
(*
  ("-f",
   Arg.String (fun s -> input_files := s :: !input_files),
   "<f> add file f to the project (ignored if it is already there)") ;
*)
  Debug.Opt.desc_debug_list;
  Debug.Opt.desc_debug_all;
  Debug.Opt.desc_debug;
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

let () = Gconfig.read_config !opt_config

let fname = match !file with
  | None ->
      Arg.usage spec usage_str;
      exit 1
  | Some f ->
      f

let (why_lang, any_lang) =
  let main = get_main () in
  let load_path = Filename.concat (datadir main) "lang" in
  let languages_manager =
    GSourceView2.source_language_manager ~default:true
  in
  languages_manager#set_search_path
    (load_path :: languages_manager#search_path);
  let why_lang =
    match languages_manager#language "why" with
    | None ->
        Format.eprintf "language file for 'why' not found in directory %s@."
          load_path;
        exit 1
    | Some _ as l -> l in
  let any_lang filename =
    match languages_manager#guess_language ~filename () with
    | None -> why_lang
    | Some _ as l -> l in
  (why_lang, any_lang)

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

let loadpath = (C.loadpath (get_main ())) @ List.rev !includes

let gconfig =
  let c = Gconfig.config () in
  c.env <- Env.create_env loadpath;
(*
  let provers = C.get_provers c.Gconfig.config in
  c.provers <-
    Util.Mstr.fold (Session.get_prover_data c.env) provers Util.Mstr.empty;
*)
  c

let () =
  C.load_plugins (get_main ())

let () =
  Debug.Opt.set_flags_selected ();
  if Debug.Opt.option_list () then exit 0


(***************)
(* Main window *)
(***************)

let w = GWindow.window
  ~allow_grow:true ~allow_shrink:true
  ~width:gconfig.window_width
  ~height:gconfig.window_height
  ~title:"Why3 Interactive Proof Session" ()

let () =
  w#set_icon (Some !Gconfig.why_icon)

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
  b1#misc#set_tooltip_markup
    "When selected, tools below are applied only to <b>unproved</b> goals";
  let (_ : GtkSignal.id) =
    b1#connect#clicked
      ~callback:(fun () -> context_unproved_goals_only := true)
  in
  let b2 = GButton.radio_button
    ~group:b1#group ~packing:context_box#add ~label:"All goals" ()
  in
  b2#misc#set_tooltip_markup
    "When selected, tools below are applied to all goals";
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

let monitor_frame =
  GBin.frame ~label:"Proof monitoring"
    ~packing:(tools_window_vbox#pack ~expand:false) ()

let monitor_box =
  GPack.vbox ~homogeneous:false ~packing:monitor_frame#add ()

let monitor_waiting =
  GMisc.label ~text:"  Waiting: 0" ~packing:monitor_box#add ()

let monitor_scheduled =
  GMisc.label ~text:"Scheduled: 0" ~packing:monitor_box#add ()

let monitor_running =
  GMisc.label ~text:"  Running: 0" ~packing:monitor_box#add ()



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
  view_name_column#set_max_width 800;
(*
  view_name_column#set_alignment 1.0;
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

let goals_model,goals_view =
  eprintf "[Info] Creating tree model...@?";
  let model = GTree.tree_store cols in
  let view = GTree.view ~model ~packing:scrollview#add () in
  let () = view#selection#set_mode (* `SINGLE *) `MULTIPLE in
  let () = view#set_rules_hint true in
  ignore (view#append_column view_name_column);
  ignore (view#append_column view_status_column);
  ignore (view#append_column view_time_column);
  eprintf " done@.";
  model,view

let clear model = model#clear ()

let image_of_result ~obsolete result =
  match result with
    | Session.Undone Session.Interrupted -> !image_undone
    | Session.Undone Session.Unedited -> !image_unknown
    | Session.Undone Session.Scheduled -> !image_scheduled
    | Session.Undone Session.Running -> !image_running
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

(* connecting to the Session model *)

let fan n =
  match n mod 4 with
    | 0 -> "|"
    | 1 | -3 -> "\\"
    | 2 | -2 -> "-"
    | 3 | -1 -> "/"
    | _ -> assert false

module S = Session

let set_row_status row b =
  if b then
    goals_model#set ~row:row#iter ~column:status_column !image_yes
  else
    goals_model#set ~row:row#iter ~column:status_column !image_unknown

let set_proof_state a =
  let obsolete = a.S.proof_obsolete in
  let row = a.S.proof_key in
  let res = a.S.proof_state in
  goals_model#set ~row:row#iter ~column:status_column
    (image_of_result ~obsolete res);
  let t = match res with
    | S.Done { Call_provers.pr_time = time } ->
        if gconfig.show_time_limit then
          Format.sprintf "%.2f [%d.0]" time a.S.proof_timelimit
        else
          Format.sprintf "%.2f" time
    | S.Undone S.Unedited -> "(not yet edited, edit with \"Edit\" button)"
    | S.InternalFailure _ -> "(internal failure)"
    | S.Undone S.Interrupted -> "(interrupted)"
    | S.Undone (S.Scheduled | S.Running) ->
        Format.sprintf "[limit=%d.0]" a.S.proof_timelimit
  in
  let t = if obsolete then t ^ " (obsolete)" else t in
  (* TODO find a better way to signal arhived row *)
  let t = if a.S.proof_archived then t ^ " (archived)" else t in
  goals_model#set ~row:row#iter ~column:time_column t

let model_index = Hashtbl.create 17


let get_any_from_iter row =
  try
    let idx = goals_model#get ~row ~column:index_column in
    Hashtbl.find model_index idx
  with Not_found -> invalid_arg "Gmain.get_any_from_iter"

(*
let get_any (row:Gtk.tree_path) : M.any =
  get_any_from_iter (goals_model#get_iter row)
*)

let get_any_from_row_reference r = get_any_from_iter r#iter

let get_selected_row_references () =
  List.map
    (fun path -> goals_model#get_row_reference path)
    goals_view#selection#get_selected_rows

let row_expanded b iter _path =
  match get_any_from_iter iter with
    | S.File f ->
        S.set_file_expanded f b
    | S.Theory t ->
        S.set_theory_expanded t b
    | S.Goal g ->
        S.set_goal_expanded g b
    | S.Transf tr ->
        S.set_transf_expanded tr b
    | S.Proof_attempt _ -> ()


let (_:GtkSignal.id) =
  goals_view#connect#row_collapsed ~callback:(row_expanded false)

let (_:GtkSignal.id) =
  goals_view#connect#row_expanded ~callback:(row_expanded true)

module M = Session_scheduler.Make
  (struct
     type key = GTree.row_reference

     let create ?parent () =
       let parent = match parent with
         | None -> None
         | Some r -> Some r#iter
       in
       let iter = goals_model#append ?parent () in
       goals_model#set ~row:iter ~column:index_column (-1);
       goals_model#get_row_reference (goals_model#get_path iter)


     let remove row =
       let (_:bool) = goals_model#remove row#iter in ()

     let reset () = goals_model#clear ()

     let idle f =
       let (_ : GMain.Idle.id) = GMain.Idle.add f in ()

     let timeout ~ms f =
       let (_ : GMain.Timeout.id) = GMain.Timeout.add ~ms ~callback:f in
       ()

     let notify_timer_state =
       let c = ref 0 in
       fun t s r ->
         incr c;
         monitor_waiting#set_text ("Waiting: " ^ (string_of_int t));
         monitor_scheduled#set_text ("Scheduled: " ^ (string_of_int s));
         monitor_running#set_text
           (if r=0 then "Running: 0" else
              "Running: " ^ (string_of_int r)^ " " ^ (fan (!c / 10)))

let notify any =
  let row,exp =
    match any with
      | S.Goal g ->
          g.S.goal_key, g.S.goal_expanded
      | S.Theory t -> t.S.theory_key, t.S.theory_expanded
      | S.File f -> f.S.file_key, f.S.file_expanded
      | S.Proof_attempt a -> a.S.proof_key,false
      | S.Transf tr -> tr.S.transf_key,tr.S.transf_expanded
  in
  if exp then goals_view#expand_to_path row#path else
    goals_view#collapse_row row#path;
  match any with
    | S.Goal g ->
        set_row_status row g.S.goal_verified
    | S.Theory th ->
        set_row_status row th.S.theory_verified
    | S.File file ->
        set_row_status row file.S.file_verified
    | S.Proof_attempt a ->
        set_proof_state a
    | S.Transf tr ->
        set_row_status row tr.S.transf_verified

let init =
  let cpt = ref (-1) in
  fun row any ->
    let ind = goals_model#get ~row:row#iter ~column:index_column in
    if ind < 0 then
      begin
        incr cpt;
        Hashtbl.add model_index !cpt any;
        goals_model#set ~row:row#iter ~column:index_column !cpt
      end
    else
      begin
        Hashtbl.replace model_index ind any;
      end;
    (* useless since it has no child: goals_view#expand_row row#path; *)
    goals_model#set ~row:row#iter ~column:icon_column
      (match any with
         | S.Goal _ -> !image_file
         | S.Theory _
         | S.File _ -> !image_directory
         | S.Proof_attempt _ -> !image_prover
         | S.Transf _ -> !image_transf);
    goals_model#set ~row:row#iter ~column:name_column
      (match any with
         | S.Goal g -> S.goal_expl g
         | S.Theory th -> th.S.theory_name.Ident.id_string
         | S.File f -> Filename.basename f.S.file_name
         | S.Proof_attempt a ->
           let p = a.S.proof_prover in
           Pp.string_of_wnl C.print_prover p
         | S.Transf tr -> tr.S.transf_name);
    notify any

let unknown_prover = Gconfig.unknown_prover gconfig

let replace_prover = Gconfig.replace_prover gconfig

   end)


(********************)
(* opening database *)
(********************)

(** TODO remove that should done only in session *)
let project_dir, file_to_read =
  if Sys.file_exists fname then
    begin
      if Sys.is_directory fname then
        begin
          eprintf "[Info] found directory '%s' for the project@." fname;
          fname, None
        end
      else
        begin
          eprintf "[Info] found regular file '%s'@." fname;
          let d =
            try Filename.chop_extension fname
            with Invalid_argument _ -> fname
          in
          eprintf "[Info] using '%s' as directory for the project@." d;
          d, Some (Filename.concat Filename.parent_dir_name
                     (Filename.basename fname))
        end
    end
  else
    fname, None

let () =
  if not (Sys.file_exists project_dir) then
    begin
      eprintf "[Info] '%s' does not exists. Creating directory of that name \
 for the project@." project_dir;
      Unix.mkdir project_dir 0o777
    end


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
    ~title:"Why3IDE"
    ~icon:(!Gconfig.why_icon)
    ~modal:true
    ~show:true ()
  in
  let (_ : GtkSignal.id) =
    d#connect#response
      ~callback:(function x ->
                   d#destroy ();
                   if mt <> `QUESTION || x = `OK then callback ())
  in ()

(* check if provers are present *)
let () =
  if C.Mprover.is_empty (C.get_provers gconfig.Gconfig.config) then
    begin
      info_window `ERROR
        "No prover configured.\nPlease run 'why3config --detect-provers' first"
        ~callback:GMain.quit;
      GMain.main ();
      exit 2;
    end

let env_session,sched =
  try
    eprintf "[Info] Opening session...@\n@[<v 2>  ";
    let session =
      if Sys.file_exists project_dir then S.read_session project_dir
      else S.create_session project_dir in
    let env_session,(_:bool) =
      M.update_session ~allow_obsolete:true session gconfig.env
        gconfig.Gconfig.config
    in
    let sched = M.init gconfig.max_running_processes in
    dprintf debug "@]@\n[Info] Opening session: done@.";
    ref env_session, sched
  with e ->
    eprintf "@[Error while opening session:@ %a@.@]"
      Exn_printer.exn_printer e;
    exit 1



(**********************************)
(* add new file from command line *)
(**********************************)

let () =
  match file_to_read with
    | None -> ()
    | Some fn ->
        if S.PHstr.mem !env_session.S.session.S.session_files fn then
          dprintf debug "[Info] file %s already in database@." fn
        else
          try
            ignore (M.add_file !env_session fn)
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
      try
       let a = get_any_from_row_reference row in
       M.run_prover
         !env_session sched
         ~context_unproved_goals_only:!context_unproved_goals_only
         ~timelimit:gconfig.time_limit
         pr a
      with e ->
        eprintf "@[Exception raised while running a prover:@ %a@.@]"
          Exn_printer.exn_printer e)
    (get_selected_row_references ())

(**********************************)
(* method: replay obsolete proofs *)
(**********************************)

let replay_obsolete_proofs () =
  List.iter
    (fun r ->
       let a = get_any_from_row_reference r in
       M.replay !env_session sched ~obsolete_only:true
         ~context_unproved_goals_only:!context_unproved_goals_only a)
    (get_selected_row_references ())

(***********************************)
(* method: mark proofs as obsolete *)
(***********************************)

let cancel_proofs () =
  List.iter
    (fun r ->
       let a = get_any_from_row_reference r in
       M.cancel a)
    (get_selected_row_references ())

(*****************************************)
(* method: Set or unset the archive flag *)
(*****************************************)

let set_archive_proofs b () =
  List.iter
    (fun r ->
       let a = get_any_from_row_reference r in
       S.iter_proof_attempt (fun a -> M.set_archive a b) a)
    (get_selected_row_references ())

(*****************************************************)
(* method: split selected goals *)
(*****************************************************)

let split_transformation = "split_goal"
let inline_transformation = "inline_goal"
let intro_transformation = "introduce_premises"


let apply_trans_on_selection tr =
  List.iter
    (fun r ->
       let a = get_any_from_row_reference r in
        M.transform !env_session sched
          ~context_unproved_goals_only:!context_unproved_goals_only
          tr
          a)
    (get_selected_row_references ())


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
                ignore (M.add_file !env_session f)
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
       M.set_maximum_running_proofs gconfig.max_running_processes sched)
    ()

let refresh_provers = ref (fun () -> ())

let add_refresh_provers f _msg =
(*
  eprintf "[Info] recording '%s' for refresh provers@." msg;
*)
  let rp = !refresh_provers in
  refresh_provers := (fun () -> rp (); f ())

(*
let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~label:"_Detect provers" ~callback:
    (fun () -> Gconfig.run_auto_detection gconfig; !refresh_provers () )
    ()
*)

let save_session () =
  eprintf "[Info] saving session@.";
  S.save_session !env_session.S.session

let exit_function ?(destroy=false) () =
  eprintf "[Info] saving IDE config file@.";
  save_config ();
  (*
  eprintf "saving session (testing only)@.";
  begin
    M.test_save ();
    try
      let l = M.test_load () in
      eprintf "reloaded successfully %d elements@." (List.length l);
      match l with
        | [] -> ()
        | f :: _ ->
            eprintf "first element is a '%s' with %d sub-elements@."
              f.Xml.name (List.length f.Xml.elements);

    with e -> eprintf "test reloading failed with exception %s@."
      (Printexc.to_string e)
  end;
  let ret = Sys.command
    "xmllint --noout --dtdvalid share/why3session.dtd essai.xml" in
  if ret = 0 then eprintf "DTD validation succeeded, good!@.";
  *)
  match (Gconfig.config ()).saving_policy with
    | 0 -> save_session (); GMain.quit ()
    | 1 -> GMain.quit ()
    | 2 ->
        let answer =
          GToolbox.question_box
            ~title:"Why3 saving session"
            ~buttons:(["Yes"; "No"] @ (if destroy then [] else ["Cancel"]))
            "Do you want to save the session?"
        in
        begin
          match answer with
            | 1 -> save_session (); GMain.quit ()
            | 2 -> GMain.quit ()
            | _ -> if destroy then GMain.quit () else ()
        end
    | _ ->
        eprintf "unexpected value for saving_policy@.";
        GMain.quit ()

(*************)
(* View menu *)
(*************)

let view_menu = factory#add_submenu "_View"
let view_factory = new GMenu.factory view_menu ~accel_group
let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._E
    ~label:"Expand all" ~callback:(fun () -> goals_view#expand_all ()) ()

let rec collapse_verified = function
  | S.Goal g when g.S.goal_verified ->
    let row = g.S.goal_key in
    goals_view#collapse_row row#path
  | S.Theory th when th.S.theory_verified ->
    let row = th.S.theory_key in
    goals_view#collapse_row row#path
  | S.File f when f.S.file_verified ->
    let row = f.S.file_key in
    goals_view#collapse_row row#path
  | any -> S.iter collapse_verified any

let collapse_all_verified_things () =
  S.session_iter collapse_verified !env_session.S.session

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
  "remove from provers box"

let tools_menu = factory#add_submenu "_Tools"
let tools_factory = new GMenu.factory tools_menu ~accel_group

let () = add_refresh_provers (fun () ->
  List.iter (fun item -> item#destroy ()) tools_menu#all_children)
  "remove from tools menu"

let () =
  let add_item_provers () =
    C.Mprover.iter
      (fun p _ ->
         let n = Pp.string_of_wnl C.print_prover p in
         let (_ : GMenu.image_menu_item) =
           tools_factory#add_image_item ~label:n
             ~callback:(fun () -> prover_on_selected_goals p)
             ()
         in
         let b = GButton.button ~packing:provers_box#add ~label:n () in
         b#misc#set_tooltip_markup
           (Pp.sprintf_wnl "Start <tt>%a</tt> on the <b>selected goals</b>"
              C.print_prover p);

(* prend de la place pour rien
         let i = GMisc.image ~pixbuf:(!image_prover) () in
         let () = b#set_image i#coerce in
*)
         let (_ : GtkSignal.id) =
           b#connect#pressed
             ~callback:(fun () -> prover_on_selected_goals p)
         in ())
      (C.get_provers gconfig.Gconfig.config)
  in
  add_refresh_provers add_item_provers "Add in tools menu and provers box";
  add_item_provers ()

let split_selected_goals () =
  apply_trans_on_selection split_transformation

let inline_selected_goals () =
  apply_trans_on_selection inline_transformation

let () =
  let add_separator () =
    ignore(tools_factory#add_separator
             () : GMenu.menu_item) in
  let add_item_split () =
    ignore(tools_factory#add_image_item
             ~label:"Split in selection"
             ~callback:split_selected_goals
             () : GMenu.image_menu_item) in
  let add_item_inline () =
    ignore(tools_factory#add_image_item
             ~label:"Inline in selection"
             ~callback:inline_selected_goals
             () : GMenu.image_menu_item) in
  add_refresh_provers add_separator "add separator in tools menu";
  add_refresh_provers add_item_split "add split in tools menu";
  add_refresh_provers add_item_inline  "add inline in tools menu";
  add_separator ();
  add_item_split ();
  add_item_inline ()


let () =
  let b = GButton.button ~packing:transf_box#add ~label:"Split" () in
  b#misc#set_tooltip_markup "Apply the transformation <tt>split_goal</tt> \
to the <b>selected goals</b>";

  let i = GMisc.image ~pixbuf:(!image_transf) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:split_selected_goals
  in
  ()

let () =
  let b = GButton.button ~packing:transf_box#add ~label:"Inline" () in
  b#misc#set_tooltip_markup "Apply the transformation <tt>inline_goal</tt> \
to the <b>selected goals</b>";
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

let () = task_view#source_buffer#set_language why_lang
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
    ~editable:false
    ~packing:scrolled_source_view#add
    ()



(*
  source_view#misc#modify_font_by_name font_name;
*)
let () = source_view#source_buffer#set_language None
let () = source_view#set_highlight_current_line true
(*
let () = source_view#source_buffer#set_text (source_text fname)
*)

let current_file = ref ""

let file_info = GMisc.label ~text:""
  ~packing:(right_hb#pack ~fill:true) ()

let set_current_file f =
  current_file := f;
  file_info#set_text ("file: " ^ !current_file)


let move_to_line ~yalign (v : GSourceView2.source_view) line =
  let line = max 0 line in
  let line = min line v#buffer#line_count in
  let it = v#buffer#get_iter (`LINE line) in
  let mark = `MARK (v#buffer#create_mark it) in
  v#scroll_to_mark ~use_align:true ~yalign mark


let premise_tag = source_view#buffer#create_tag
  ~name:"premise_tag" [`BACKGROUND gconfig.premise_color]

let goal_tag = source_view#buffer#create_tag
  ~name:"goal_tag" [`BACKGROUND gconfig.goal_color]

let error_tag = source_view#buffer#create_tag
  ~name:"error_tag" [`BACKGROUND gconfig.error_color]

let erase_color_loc (v:GSourceView2.source_view) =
  let buf = v#buffer in
  buf#remove_tag premise_tag ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag goal_tag ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag error_tag ~start:buf#start_iter ~stop:buf#end_iter

let color_loc (v:GSourceView2.source_view) ~color l b e =
  let buf = v#buffer in
  let top = buf#start_iter in
  let start = top#forward_lines (l-1) in
  let start = start#forward_chars b in
  let stop = start#forward_chars (e-b) in
  buf#apply_tag ~start ~stop color

let scroll_to_loc ?(yalign=0.0) ~color loc =
  let (f,l,b,e) = Loc.get loc in
  if f <> !current_file then
    begin
      source_view#source_buffer#set_language (any_lang f);
      source_view#source_buffer#set_text (source_text f);
      set_current_file f;
    end;
  move_to_line ~yalign source_view (l-1);
  erase_color_loc source_view;
  (* FIXME: use another color or none at all *)
  (* color_loc source_view ~color l b e *)
  ignore (color,l,b,e)

let scroll_to_id ~color id =
  match id.Ident.id_loc with
    | Some loc -> scroll_to_loc ~color loc
    | None ->
        source_view#source_buffer#set_text
          "Non-localized ident (no position available)\n";
        set_current_file ""

let color_loc ~color loc =
  let f, l, b, e = Loc.get loc in
  if f = !current_file then color_loc ~color source_view l b e

let rec color_locs ~color f =
  let b = ref false in
  Util.option_iter (fun loc -> color_loc ~color loc; b := true) f.Term.t_loc;
  Term.t_fold (fun b loc -> color_locs ~color loc || b) !b f

(* FIXME: we shouldn't open binders _every_time_ we redraw screen!!!
   No t_fold, no t_open_quant! *)
let rec color_t_locs f =
  match f.Term.t_node with
    | Term.Tbinop (Term.Timplies,f1,f2) ->
        let b = color_locs ~color:premise_tag f1 in
        color_t_locs f2 || b
    | Term.Tlet (t,fb) ->
        let _,f1 = Term.t_open_bound fb in
        let b = color_locs ~color:premise_tag t in
        color_t_locs f1 || b
    | Term.Tquant (Term.Tforall,fq) ->
        let _,_,f1 = Term.t_open_quant fq in
        color_t_locs f1
    | _ ->
        color_locs ~color:goal_tag f

let scroll_to_source_goal g =
  let t = S.goal_task g in
  let id = (Task.task_goal t).Decl.pr_name in
  scroll_to_id ~color:goal_tag id;
  match t with
    | Some
        { Task.task_decl =
            { Theory.td_node =
                Theory.Decl { Decl.d_node = Decl.Dprop (Decl.Pgoal, _, f)}}} ->
        if not (color_t_locs f) then
          Util.option_iter (color_loc ~color:goal_tag) id.Ident.id_loc
    | _ ->
        assert false

let scroll_to_theory th =
  let id = th.S.theory_name in
  scroll_to_id ~color:goal_tag id


let reload () =
  try
    erase_color_loc source_view;
    current_file := "";
    (** create a new environnement
        (in order to reload the files which are "use") *)
    gconfig.env <- Env.create_env loadpath;
    (** reload the session *)
    let old_session = (!env_session).S.session in
    let new_env_session,(_:bool) =
      M.update_session ~allow_obsolete:true old_session gconfig.env
        gconfig.Gconfig.config
    in
    env_session := new_env_session
  with
    | e ->
        let e = match e with
          | Loc.Located(loc,e) ->
              scroll_to_loc ~color:error_tag ~yalign:0.5 loc; e
          | e -> e
        in
        fprintf str_formatter
          "@[Error:@ %a@]" Exn_printer.exn_printer e;
        let msg = flush_str_formatter () in
        file_info#set_text msg
(*
        info_window `ERROR msg
*)

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~key:GdkKeysyms._R
    ~label:"_Reload" ~callback:reload
    ()


(* Saving the session *)

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item (* no shortcut ~key:GdkKeysyms._S *)
    ~label:"_Save session" ~callback:save_session
    ()


(*

Saving the source_view: deactivated for the moment

let save_file () =
  let f = !current_file in
  if f <> "" then
    begin
      save_session ();
      let s = source_view#source_buffer#get_text () in
      let c = open_out f in
      output_string c s;
      close_out c;
      reload ()
    end
  else
    info_window `ERROR "No file currently edited"

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~key:GdkKeysyms._S
    ~label:"_Save" ~callback:save_file
    ()
*)

let (_ : GtkSignal.id) = w#connect#destroy
  ~callback:(exit_function ~destroy:true)

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~key:GdkKeysyms._Q ~label:"_Quit"
    ~callback:exit_function ()


(*****************************)
(* method: edit current goal *)
(*****************************)

let edit_selected_row r =
  match get_any_from_row_reference r with
    | S.Goal _g ->
        ()
    | S.Theory _th ->
        ()
    | S.File _file ->
        ()
    | S.Proof_attempt a ->
        M.edit_proof
          !env_session sched ~default_editor:gconfig.default_editor a
    | S.Transf _ -> ()

let edit_current_proof () =
  match get_selected_row_references () with
    | [] -> ()
    | [r] -> edit_selected_row r
    | _ ->
        info_window `INFO "Please select exactly one proof to edit"

let () =
  let add_separator () =
    ignore(tools_factory#add_separator
             () : GMenu.menu_item) in
  let add_item_edit () =
    ignore (tools_factory#add_image_item
              ~label:"Edit current proof"
              ~callback:edit_current_proof
              () : GMenu.image_menu_item) in
  let add_item_replay () =
    ignore (tools_factory#add_image_item
              ~label:"Replay selection"
              ~callback:replay_obsolete_proofs
              () : GMenu.image_menu_item) in
  let add_item_cancel () =
    ignore (tools_factory#add_image_item
              ~label:"Mark as obsolete"
              ~callback:cancel_proofs
              () : GMenu.image_menu_item) in
  let add_item_archived () =
    ignore (tools_factory#add_image_item
              ~label:"Mark as archive"
              ~callback:(set_archive_proofs true)
              () : GMenu.image_menu_item) in
  let add_item_unarchived () =
    ignore (tools_factory#add_image_item
              ~label:"Remove from archive"
              ~callback:(set_archive_proofs false)
              () : GMenu.image_menu_item) in
  add_refresh_provers add_separator "add sep in tools menu";
  add_refresh_provers add_item_edit "add edit in tools menu";
  add_refresh_provers add_item_replay "add replay in tools menu";
  add_refresh_provers add_item_cancel "add cancel in tools menu";
  add_refresh_provers add_item_archived "add archive in tools menu";
  add_refresh_provers add_item_unarchived "add unarchive in tools menu";
  add_separator ();
  add_item_edit ();
  add_item_replay ();
  add_item_cancel ();
  add_item_archived ();
  add_item_unarchived ()



let () =
  let b = GButton.button ~packing:tools_box#add ~label:"Edit" () in
  b#misc#set_tooltip_markup
    "Edit the <b>selected proof</b> with the appropriate editor";

  let i = GMisc.image ~pixbuf:(!image_editor) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:edit_current_proof
  in ()

let () =
  let b = GButton.button ~packing:tools_box#add ~label:"Replay" () in
  b#misc#set_tooltip_markup
    "Replay <b>obsolete</b> proofs below the current selection";

  let i = GMisc.image ~pixbuf:(!image_replay) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:replay_obsolete_proofs
  in ()


(*************)
(* removing  *)
(*************)

let confirm_remove_row r =
  match get_any_from_row_reference r with
    | S.Goal _g ->
        info_window `ERROR "Cannot remove a goal"
    | S.Theory _th ->
        info_window `ERROR "Cannot remove a theory"
    | S.File _file ->
        info_window `ERROR "Cannot remove a file"
    | S.Proof_attempt a ->
        info_window
          ~callback:(fun () -> M.remove_proof_attempt a)
          `QUESTION
          "Do you really want to remove the selected proof attempt?"
    | S.Transf tr ->
        info_window
          ~callback:(fun () -> M.remove_transformation tr)
          `QUESTION
          "Do you really want to remove the selected transformation
and all its subgoals?"

let remove_proof r =
  match get_any_from_row_reference r with
    | S.Goal _g -> ()
    | S.Theory _th -> ()
    | S.File _file -> ()
    | S.Proof_attempt a -> M.remove_proof_attempt a
    | S.Transf _tr -> ()

let confirm_remove_selection () =
  match get_selected_row_references () with
    | [] -> ()
    | [r] -> confirm_remove_row r
    | l ->
        info_window
          ~callback:(fun () -> List.iter remove_proof l)
          `QUESTION
          "Do you really want to remove the selected proof attempts?"
(*
    | _ ->
        info_window `INFO "Please select exactly one item to remove"
*)

let clean_selection () =
  List.iter (fun r -> M.clean (get_any_from_row_reference r))
    (get_selected_row_references ())

let () =
  let add_separator () =
    ignore(tools_factory#add_separator
             () : GMenu.menu_item) in
  let add_item_remove () =
    ignore(tools_factory#add_image_item
             ~label:"Remove current proof"
             ~callback:confirm_remove_selection
             () : GMenu.image_menu_item) in
  let add_item_clean () =
    ignore(tools_factory#add_image_item
             ~label:"Clean selection"
             ~callback:clean_selection
             () : GMenu.image_menu_item) in
  add_refresh_provers add_separator "add sep in tools menu";
  add_refresh_provers add_item_remove "add remove in tools menu";
  add_refresh_provers add_item_clean "add clean in tools menu";
  add_separator ();
  add_item_remove ();
  add_item_clean ()

let () =
  let b = GButton.button ~packing:cleaning_box#add ~label:"Remove" () in
  b#misc#set_tooltip_markup "Remove selected <b>proof attempts</b> and \
<b>transformations</b>";
  let i = GMisc.image ~pixbuf:(!image_remove) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:confirm_remove_selection
  in ()

let () =
  let b = GButton.button ~packing:cleaning_box#add ~label:"Clean" () in
  b#misc#set_tooltip_markup "Remove unsuccessful <b>proof attempts</b> \
associated to proved goals";
  let i = GMisc.image ~pixbuf:(!image_cleaning) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:clean_selection
  in ()

let () =
  let b = GButton.button ~packing:monitor_box#add ~label:"Interrupt" () in
  b#misc#set_tooltip_markup "Cancels all scheduled proof attempts";
  let i = GMisc.image ~pixbuf:(!image_cancel) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#pressed ~callback:(fun () -> M.cancel_scheduled_proofs sched)
  in ()


(***************)
(* Bind events *)
(***************)

let display_task g t =
  let task_text = Pp.string_of Pretty.print_task t in
  task_view#source_buffer#set_text task_text;
  task_view#scroll_to_mark `INSERT;
  scroll_to_source_goal g

(* to be run when a row in the tree view is selected *)
let select_row r =
  let a = get_any_from_row_reference r in
  match a with
    | S.Goal g ->
        if (Gconfig.config ()).intro_premises then
          let trans =
            Trans.lookup_transform intro_transformation !env_session.S.env in
          display_task g (Trans.apply trans (S.goal_task g))
        else
          display_task g (S.goal_task g)
    | S.Theory th ->
        task_view#source_buffer#set_text "";
        scroll_to_theory th
    | S.File _file ->
        task_view#source_buffer#set_text "";
        (* scroll_to_file file *)
    | S.Proof_attempt a ->
        let o =
          match a.S.proof_state with
            | S.Undone S.Interrupted ->
              "proof not yet scheduled for running"
            | S.Undone S.Unedited -> "proof not yet edited"
            | S.Done r -> r.Call_provers.pr_output
            | S.Undone S.Scheduled-> "proof scheduled but not running yet"
            | S.Undone S.Running -> "prover currently running"
            | S.InternalFailure e ->
              let b = Buffer.create 37 in
              bprintf b "%a" Exn_printer.exn_printer e;
              Buffer.contents b
        in
        task_view#source_buffer#set_text o;
        scroll_to_source_goal a.S.proof_parent
    | S.Transf tr ->
        task_view#source_buffer#set_text "";
        scroll_to_source_goal tr.S.transf_parent

(* row selection on tree view on the left *)
let (_ : GtkSignal.id) =
  goals_view#selection#connect#after#changed ~callback:
    begin fun () ->
      match get_selected_row_references () with
        | [p] -> select_row p
        | [] -> ()
        | _ -> ()
    end

(*
let () = Debug.set_flag (Debug.lookup_flag "transform")
*)

let () = w#add_accel_group accel_group
let () = w#show ()
let () = GMain.main ()

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
