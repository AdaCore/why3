(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Format
open Gconfig
open Stdlib
open Ide_utils
open History
open Itp_communication
open Itp_server

external reset_gc : unit -> unit = "ml_reset_gc"

let debug = Debug.lookup_flag "ide_info"
let debug_stack_trace = Debug.lookup_flag "stack_trace"

(***************************)
(* Debugging Json protocol *)
(***************************)


(* TODO remove print_request_json and print_notification_json *)
exception Badparsing

let print_request_json fmt (r: ide_request) =
  (try (
    let s = Pp.string_of Json_util.print_request r in
    let x = Json_util.parse_request s in
    if r = x then () else raise Badparsing)
  with
    _ -> Format.eprintf "Bad parsing@.");
  Json_util.print_request fmt r

let print_notification_json fmt (n: notification) =
  (try (
    let x = Json_util.parse_notification (Pp.string_of Json_util.print_notification n) in
    if n = x then () else raise Badparsing)
  with
    _ -> Format.eprintf "Bad parsing@.");
  Json_util.print_notification fmt n

let debug_json = Debug.register_flag "json_proto"
    ~desc:"Print@ json@ requests@ and@ notifications@"

(*******************)
(* server protocol *)
(*******************)

module Protocol_why3ide = struct

  let debug_proto = Debug.register_flag "ide_proto"
      ~desc:"Print@ debugging@ messages@ about@ Why3Ide@ protocol@"

  let print_request_debug r =
    Debug.dprintf debug_proto "request %a@." print_request r;
    Debug.dprintf debug_json "%a@." print_request_json r

  let print_msg_debug m =
    Debug.dprintf debug_proto "message %a@." print_msg m

  let print_notify_debug n =
    Debug.dprintf debug_proto "handling notification %a@." print_notify n;
    Debug.dprintf debug_json "%a@." print_notification_json n

  let list_requests: ide_request list ref = ref []

  let get_requests () =
    let n = List.length !list_requests in
    if n > 0 then
      Debug.dprintf debug_proto "got %d new requests@." n;
    let l = List.rev !list_requests in
    list_requests := [];
    l

  let send_request r =
    print_request_debug r;
    list_requests := r :: !list_requests

  let notification_list: notification list ref = ref []

  let notify n =
(* too early, print when handling notifications
    print_notify_debug n;
 *)    notification_list := n :: !notification_list

  let get_notified () =
    let n = List.length !notification_list in
    if n > 0 then
      Debug.dprintf debug_proto "got %d new notifications@." n;
    let l = List.rev !notification_list in
    notification_list := [];
    l

end

(* True when session differs from the saved session *)
let session_needs_saving = ref false

let get_notified = Protocol_why3ide.get_notified

let send_request r =
  (* If request changes the session then session needs saving *)
  if modify_session r then
    session_needs_saving := true;
  Protocol_why3ide.send_request r

(****************************************)
(* server instance on the GTK scheduler *)
(****************************************)

(*
   The gtk scheduler is catching all exceptions avoiding the printing of the
   backtrace that is normally done by debug option stack_trace. To recover this
   behavior we catch exceptions ourselves. If "stack_trace" is on, we exit on
   first exception and print backtrace on standard output otherwise we raise
   the exception again (with information on error output).
*)
let backtrace_and_exit f () =
  try f () with
  | e ->
     if Debug.test_flag debug_stack_trace then
       begin
         Printexc.print_backtrace stderr;
         Format.eprintf "exception '%a' was raised in a LablGtk callback.@."
                        Exn_printer.exn_printer e;
         exit 1
       end
     else
       begin
         Format.eprintf "exception '%a' was raised in a LablGtk callback.@."
                        Exn_printer.exn_printer e;
         Format.eprintf "This should not happen. Please report. @.";
         raise e
       end

module Scheduler = struct

    let blocking = false

    let multiplier = 3

    let idle ~prio f =
      let (_ : GMain.Idle.id) = GMain.Idle.add ~prio (backtrace_and_exit f) in ()

    let timeout ~ms f =
      let (_ : GMain.Timeout.id) =
        GMain.Timeout.add ~ms ~callback:(backtrace_and_exit f) in ()
end

module Server = Itp_server.Make (Scheduler) (Protocol_why3ide)

(************************)
(* parsing command line *)
(************************)

let files : string Queue.t = Queue.create ()
let opt_parser = ref None

let spec = [
  "-F", Arg.String (fun s -> opt_parser := Some s),
      "<format> select input format (default: \"why\")";
  "--format", Arg.String (fun s -> opt_parser := Some s),
      " same as -F";
(*
  "-f",
   Arg.String (fun s -> input_files := s :: !input_files),
   "<file> add file to the project (ignored if it is already there)";
*)
  Termcode.arg_extra_expl_prefix
]

let usage_str = sprintf
  "Usage: %s [options] [<file.why>|<project directory>]..."
  (Filename.basename Sys.argv.(0))

let env, gconfig = try
  let config, base_config, env =
    Whyconf.Args.initialize spec (fun f -> Queue.add f files) usage_str in
    if Queue.is_empty files then
      Whyconf.Args.exit_with_usage spec usage_str;
    Gconfig.load_config config base_config;
    env, Gconfig.config ()

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

(* Initialization of config, provers, task_driver and controller in the server *)
let () =
  let dir =
    try
      Server_utils.get_session_dir ~allow_mkdir:true files
    with Invalid_argument s ->
      Format.eprintf "Error: %s@." s;
      Whyconf.Args.exit_with_usage spec usage_str
  in
  Server.init_server gconfig.config env dir;
  Queue.iter (fun f -> send_request (Add_file_req f)) files

let () =
  Debug.dprintf debug "Init the GTK interface...@?";
  ignore (GtkMain.Main.init ());
  Debug.dprintf debug " done.@.";
  Gconfig.init ()


(********************************)
(* Source language highlighting *)
(********************************)


let (why_lang, any_lang) =
  let main = Whyconf.get_main gconfig.config in
  let load_path = Filename.concat (Whyconf.datadir main) "lang" in
  let languages_manager =
    GSourceView2.source_language_manager ~default:true
  in
  languages_manager#set_search_path
    (load_path :: languages_manager#search_path);
  let why_lang =
    match languages_manager#language "why3" with
    | None ->
        eprintf "language file for 'why3' not found in directory %s@."
          load_path;
        exit 1
    | Some _ as l -> l in
  let any_lang filename =
    match languages_manager#guess_language ~filename () with
    | None -> why_lang
    | Some _ as l -> l in
  (why_lang, any_lang)

(* Borrowed from Frama-C src/gui/source_manager.ml:
Try to convert a source file either as UTF-8 or as locale. *)
let try_convert s =
  try
    if Glib.Utf8.validate s then s else Glib.Convert.locale_to_utf8 s
  with Glib.Convert.Error _ ->
    try
      Glib.Convert.convert_with_fallback
        ~fallback:"#neither UTF-8 nor locale nor ISO-8859-15#"
        ~to_codeset:"UTF-8"
        ~from_codeset:"ISO_8859-15"
        s
    with Glib.Convert.Error _ as e -> Printexc.to_string e


(****************************)
(* Color handling in source *)
(****************************)

(* For each view, we have to recreate the tags *)
let create_colors v =
  let premise_tag (v: GSourceView2.source_view) = v#buffer#create_tag
      ~name:"premise_tag" [`BACKGROUND gconfig.premise_color] in

  let neg_premise_tag (v: GSourceView2.source_view) = v#buffer#create_tag
      ~name:"neg_premise_tag" [`BACKGROUND gconfig.neg_premise_color] in

  let goal_tag (v: GSourceView2.source_view) = v#buffer#create_tag
      ~name:"goal_tag" [`BACKGROUND gconfig.goal_color] in

  let error_tag (v: GSourceView2.source_view) = v#buffer#create_tag
      ~name:"error_tag" [`BACKGROUND gconfig.error_color] in
  let _ : GText.tag = premise_tag v in
  let _ : GText.tag = neg_premise_tag v in
  let _ : GText.tag = goal_tag v in
  let _ : GText.tag = error_tag v in
  ()

(* Erase all the source location tags in a source file *)
let erase_color_loc (v:GSourceView2.source_view) =
  let buf = v#buffer in
  buf#remove_tag_by_name "premise_tag" ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag_by_name "neg_premise_tag" ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag_by_name "goal_tag" ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag_by_name "error_tag" ~start:buf#start_iter ~stop:buf#end_iter



(*******************)
(* Graphical tools *)
(*******************)

(* Elements needed for usage of graphical elements *)

(* [quit_on_saved] set to true by exit function to delay quiting after Saved
   notification is received *)
let quit_on_saved = ref false

(* Exit brutally without asking anything *)
let exit_function_unsafe () =
  send_request Exit_req;
  GMain.quit ()

(* Contains a quadruplets (tab page, source_view, file_has_been_modified, label_of_tab):
   - tab_page is a unique number for each pages of the notebook
   - source_view is the graphical element inside a tab
   - has_been_modified is a reference to a boolean stating if the current tab
     source has been modified
   - label_of_tab is the mutable title of the tab
*)
let source_view_table : (int * GSourceView2.source_view * bool ref * GMisc.label) Hstr.t =
  Hstr.create 14

(* The corresponding file does not have a source view *)
exception Nosourceview of string

let get_source_view_table (file:string) =
  match Hstr.find source_view_table file with
  | v -> v
  | exception Not_found -> raise (Nosourceview file)

(* This returns the source_view of a file *)
let get_source_view (file: string) : GSourceView2.source_view =
  match Hstr.find source_view_table file with
  | (_, v, _, _) -> v
  | exception Not_found -> raise (Nosourceview file)

(* Saving function for sources *)
let save_sources () =
  Hstr.iter
    (fun k (_n, (s: GSourceView2.source_view), b, _l) ->
      if !b then
        let text_to_save = s#source_buffer#get_text () in
        send_request (Save_file_req (k, text_to_save))
    )
    source_view_table

(* True if there exist a file which needs saving *)
let files_need_saving () =
  Hstr.fold (fun _k (_, _, b, _) acc -> !b || acc) source_view_table false

(* Ask if the user wants to save session before exit. Exit is then delayed until
   the [Saved] notification is received *)
let exit_function_safe () =
  if not !session_needs_saving && not (files_need_saving ()) then
    exit_function_unsafe ()
  else
    let answer =
      GToolbox.question_box
        ~title:"Why3 saving session and files"
        ~buttons:["Yes"; "No"; "Cancel"]
        "Do you want to save the session and unsaved files?"
    in
    begin
      match answer with
      | 1 -> save_sources(); send_request Save_req; quit_on_saved := true
      | 2 -> exit_function_unsafe ()
      | _ -> ()
    end

(* Update name of the tab when the label changes so that it has a * as prefix *)
let update_label_change (label: GMisc.label) =
  let s = label#text in
  if not (Strings.has_prefix "*" s) then
    label#set_text ("*" ^ s)

(* Update name of the tab when the label is saved. Removes * prefix *)
let update_label_saved (label: GMisc.label) =
  let s = label#text in
  if (Strings.has_prefix "*" s) then
    label#set_text (String.sub s 1 (String.length s - 1))


(**********************)
(* Graphical elements *)
(**********************)


let main_window : GWindow.window =
  let w = GWindow.window
            ~allow_grow:true ~allow_shrink:true
            ~width:gconfig.window_width
            ~height:gconfig.window_height
            ~title:"Why3 Interactive Proof Session" ()
  in
  (* callback to record the new size of the main window when changed, so
   that on restart the window size is the same as the last session *)
  let (_ : GtkSignal.id) =
    w#misc#connect#size_allocate
      ~callback:
      (fun {Gtk.width=w;Gtk.height=h} ->
       gconfig.window_height <- h;
       gconfig.window_width <- w)
  in w

(* the main window contains a vertical box, containing:
   1. the menu [menubar]
   2. an horizontal box [hb]
 *)

let vbox = GPack.vbox ~packing:main_window#add ()

let menubar = GMenu.menu_bar
  ~packing:(vbox#pack ?from:None ?expand:None ?fill:None ?padding:None)
  ()

let hb = GPack.hbox ~packing:vbox#add ()

(* 1. Menu *)

let factory = new GMenu.factory menubar

let accel_group = factory#accel_group

let create_menu_item (factory:GMenu.menu GMenu.factory)
                     ?key label tooltip =
  let i = factory#add_item ?key label in
  i#misc#set_tooltip_markup tooltip;
  i

let connect_menu_item i ~callback =
  let (_ : GtkSignal.id) = i#connect#activate ~callback in ()

(* 1.1 "File" menu items *)

let file_menu = factory#add_submenu "_File"
let file_factory = new GMenu.factory file_menu ~accel_group
let menu_add_file =
  create_menu_item file_factory "Add file to session"
                   "Insert another file in the current session"
let menu_preferences =
  create_menu_item file_factory "Preferences"
                   "Open Preferences Window"
let menu_save_session =
  create_menu_item file_factory "Save session"
                   "Save the current proof session on disk"
let menu_save_files =
  create_menu_item file_factory "Save files"
                   "Save the edited source files on disk"
let menu_save_session_and_files =
  create_menu_item file_factory ~key:GdkKeysyms._S "_Save session and files"
                   "Save the current proof session and the source files"
let menu_refresh =
  create_menu_item file_factory ~key:GdkKeysyms._R "Save all and _Refresh session"
                   "Save the current proof session and the source files, then refresh the proof session with updated source files."

let menu_quit =
  create_menu_item file_factory ~key:GdkKeysyms._Q "_Quit"
                   "Quit the interface. See the Preferences for setting the policy on automatic file saving at exit."

(* 1.2 "Tools" menu items *)

let tools_menu = factory#add_submenu "_Tools"
let tools_factory = new GMenu.factory tools_menu ~accel_group
let tools_accel_group = GtkData.AccelGroup.create ()

let strategies_factory =
  let tools_submenu_strategies = tools_factory#add_submenu "Strategies" in
  let ( _ : GMenu.menu_item) = tools_factory#add_separator () in
  new GMenu.factory tools_submenu_strategies

let provers_factory =
  let tools_submenu_provers = tools_factory#add_submenu "Provers" in
  let ( _ : GMenu.menu_item) = tools_factory#add_separator () in
  new GMenu.factory tools_submenu_provers



(* 1.3 "View" menu items *)



(****************************)
(* actions of the interface *)
(****************************)









(***********************************)
(* connection of actions to signals *)
(***********************************)

(* File menu signals *)

let send_session_config_to_server () =
  let nb = gconfig.session_nb_processes in
  send_request (Set_config_param("max_tasks",nb));
  let nb = gconfig.session_time_limit in
  send_request (Set_config_param("timelimit",nb));
  let nb = gconfig.session_mem_limit in
  send_request (Set_config_param("memlimit",nb))

let () =
  let callback () =
    Gconfig.preferences gconfig;
    (* TODO:
      begin
        match !current_env_session with
          | None -> ()
          | Some e ->
              Session.update_env_session_config e gconfig.config;
              Session.unload_provers e
      end;
      recreate_gui ();
(*
      Mprover.iter
        (fun p pi ->
          Debug.dprintf debug "editor for %a : %s@." Whyconf.print_prover p
            pi.editor)
        (Whyconf.get_provers gconfig.config);
     *)
     *)
    send_session_config_to_server ()
  in
  connect_menu_item menu_preferences ~callback

let () =
  connect_menu_item
    menu_save_session
    ~callback:(fun () -> send_request Save_req)

let () =
  connect_menu_item
    menu_save_session_and_files
    ~callback:(fun () -> save_sources(); send_request Save_req)

let () =
  connect_menu_item
    menu_save_files
    ~callback:(fun () -> save_sources())


let () =
  connect_menu_item
    menu_quit
    ~callback:exit_function_safe

let (_ : GtkSignal.id) =
  main_window#connect#destroy
    ~callback:exit_function_safe

let (_ : GtkSignal.id) =
  main_window#event#connect#delete
    ~callback:(fun _ -> exit_function_safe (); true)

(* 2. horizontal box contains:
   2.1 TODO: a tool box ?
   2.2 a horizontal paned [hp] containing:
     2.2.1 a scrolled window to hold the tree view of the session [scrolledview]
     2.2.2 a vertical paned containing [vpan222]
*)

let hp = GPack.paned `HORIZONTAL ~packing:hb#add ()

let scrollview =
  let sv =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~width:gconfig.tree_width ~shadow_type:`ETCHED_OUT
      ~packing:hp#add ()
  in
  let (_ : GtkSignal.id) =
    sv#misc#connect#size_allocate
      ~callback:
      (fun {Gtk.width=w;Gtk.height=_h} ->
       gconfig.tree_width <- w)
  in sv

(** {2 view for the session tree} *)
let scrolled_session_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:scrollview#add_with_viewport
    ()

(* Vertical pan *)
let vpan222 = GPack.paned `VERTICAL ~packing:hp#add ()

(*  the scrolled window 2.2.1 [scrolled_session_view] contains a GTK tree

*)

(** {3 the model for tree view} *)

let cols = new GTree.column_list
(* first column: unique id of the object *)
let node_id_column = cols#add Gobject.Data.int
(* second column: an icon identifying the object: file,theory, goal, transformation *)
let icon_column = cols#add Gobject.Data.gobject
(* third column: name of the object *)
let name_column = cols#add Gobject.Data.string
(* fourth column: icon status for the object: proved/unproved, unknown, timeout, etc. *)
let status_column = cols#add Gobject.Data.gobject
(* fifth column: extra status info: time, obsolete status, limits *)
let time_column = cols#add Gobject.Data.string

(* first view column: icon and name *)
let view_name_column =
  let v = GTree.view_column ~title:"Theories/Goals" () in
  (* icon attribute *)
  let icon_renderer = GTree.cell_renderer_pixbuf [ ] in
  v#pack icon_renderer ~expand:false;
  v#add_attribute icon_renderer "pixbuf" icon_column;
  let name_renderer = GTree.cell_renderer_text [`XALIGN 0.] in
  v#pack name_renderer;
  v#add_attribute name_renderer "text" name_column;
  (* v#set_sizing `AUTOSIZE; *)
  v#set_resizable true;
  (*  v#set_max_width 1000;*)
  v

(* second view column: status *)
let view_status_column =
  let status_renderer = GTree.cell_renderer_pixbuf [ ] in
  let v = GTree.view_column ~title:"Status"
                            ~renderer:(status_renderer, ["pixbuf", status_column])
                            ()
  in
  v#set_resizable false;
  v#set_visible true;
  v

let view_time_column =
  let renderer = GTree.cell_renderer_text [`XALIGN 0.] in
  let v = GTree.view_column ~title:"Time"
                            ~renderer:(renderer, ["text", time_column]) ()
  in
  v#set_resizable false;
  v#set_visible true;
  v

let goals_model,goals_view =
  Debug.dprintf debug "Creating tree model...@?";
  let model = GTree.tree_store cols in
  let view = GTree.view ~model ~packing:scrolled_session_view#add () in
  let () = view#selection#set_mode (* `SINGLE *) `MULTIPLE in
(*
  let () = view#set_rules_hint true in
*)
  let () = view#set_enable_search false in
  let _: int = view#append_column view_status_column in
  let _: int = view#append_column view_name_column in
  let _: int = view#append_column view_time_column in
  view#set_expander_column (Some view_name_column);
  Debug.dprintf debug "done@.";
  model,view


(***********************************)
(* Mapping session to the GTK tree *)
(***********************************)

type pa_status = Controller_itp.proof_attempt_status
      * bool   (* obsolete or not *) (* TODO *)
      * Call_provers.resource_limit

let node_id_type : node_type Hint.t = Hint.create 17
let node_id_proved : bool Hint.t = Hint.create 17
let node_id_pa : pa_status Hint.t = Hint.create 17
let node_id_detached : bool Hint.t = Hint.create 17

let get_node_type id = Hint.find node_id_type id

let get_node_proved id =
  try Hint.find node_id_proved id
  with Not_found -> false

let get_node_id_pa id = Hint.find node_id_pa id

let get_obs (pa_st: pa_status) = match pa_st with
| _, b, _ -> b

let get_proof_attempt (pa_st: pa_status) = match pa_st with
| pa, _, _ -> pa

let get_limit (pa_st: pa_status) = match pa_st with
| _, _, l -> l

let get_node_obs id = get_obs (get_node_id_pa id)
let get_node_proof_attempt id = get_proof_attempt (get_node_id_pa id)
let get_node_limit id = get_limit (get_node_id_pa id)

let get_node_id iter = goals_model#get ~row:iter ~column:node_id_column

(* To each node we have the corresponding row_reference *)
let node_id_to_gtree : GTree.row_reference Hint.t = Hint.create 42
(* TODO exception for those: *)
let get_node_row id = Hint.find node_id_to_gtree id

let get_node_detached id =
  Hint.find node_id_detached id

(******************************)
(* Initialization of the tree *)
(******************************)

let remove_tree goals_model =
  Hint.iter (fun _x i ->
    try ignore(goals_model#remove (i#iter)) with _ -> ())
    node_id_to_gtree

let clear_tree_and_table goals_model =
  remove_tree goals_model;
  Hint.clear node_id_to_gtree;
  Hint.clear node_id_type;
  Hint.clear node_id_proved;
  Hint.clear node_id_pa;
  Hint.clear node_id_detached


(**************)
(* Menu items *)
(**************)


let reload_unsafe () = send_request Reload_req

let save_and_reload () = save_sources (); reload_unsafe ()

(* Same as reload_safe but propose to save edited sources before reload *)
let reload_safe () =
  if files_need_saving () then
    let answer =
      GToolbox.question_box
        ~title:"Why3 saving source files"
        ~buttons:["Yes"; "No"; "Cancel"]
        "Do you want to save modified source files before refresh?\nBeware that unsaved modifications will be discarded."
    in
    match answer with
    | 1 -> save_and_reload ()
    | 2 -> reload_unsafe ()
    | _ -> ()
  else
    reload_unsafe ()

let () = connect_menu_item menu_refresh ~callback:save_and_reload


(* vpan222 contains:
   2.2.2.1 a notebook containing view of the current task, source code etc
   2.2.2.2 a vertical pan which contains [vbox2222]
     2.2.2.2.1 the input field to type commands
     2.2.2.2.2 a scrolled window to hold the output of the commands
 *)

(***********************************)
(*    notebook on the top 2.2.2.1  *)
(***********************************)

(* notebook is composed of a Task page and several source files pages *)
let notebook = GPack.notebook ~packing:vpan222#add ()

(********************************)
(* Task view (part of notebook) *)
(********************************)
let task_page,scrolled_task_view =
  let label = GMisc.label ~text:"Task" () in
  0, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()

let scrolled_task_view =
  GBin.scrolled_window
    ~height:gconfig.task_height
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:scrolled_task_view#add ()

let (_ : GtkSignal.id) =
  scrolled_task_view#misc#connect#size_allocate
    ~callback:
    (fun {Gtk.width=_w;Gtk.height=h} ->
       gconfig.task_height <- h)


let task_view =
  GSourceView2.source_view
    ~editable:false
    ~cursor_visible:false
    ~show_line_numbers:true
    ~packing:scrolled_task_view#add
    ()


(* Creating a page for source code view *)
let create_source_view =
  (* Counter for pages *)
  let n = ref 1 in
  (* Create a page with tabname [f] and buffer equal to [content] in the
     notebook. Also add a corresponding page in source_view_table. *)
  let create_source_view f content =
    if not (Hstr.mem source_view_table f) then
      begin
        let label = GMisc.label ~text:f () in
        let source_page, scrolled_source_view =
          !n, GPack.vbox ~homogeneous:false ~packing:
            (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()
        in
        let scrolled_source_view =
          GBin.scrolled_window
            ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
            ~shadow_type:`ETCHED_OUT
            ~packing:scrolled_source_view#add () in
        let source_view =
          GSourceView2.source_view
            ~auto_indent:true
            ~insert_spaces_instead_of_tabs:true ~tab_width:2
            ~show_line_numbers:true
            ~right_margin_position:80 ~show_right_margin:true
            (* ~smart_home_end:true *)
            ~editable:true
            ~packing:scrolled_source_view#add
            () in
        let has_changed = ref false in
        Hstr.add source_view_table f (source_page, source_view, has_changed, label);
        n := !n + 1;
        source_view#source_buffer#set_text content;
        (* At initialization, file has not changed. When it changes, changes the
           name of the tab and update has_changed boolean. *)
        let (_: GtkSignal.id) = source_view#source_buffer#connect#changed
          ~callback:(fun () ->
            try
              let _source_page, _source_view, has_changed, label =
                Hstr.find source_view_table f in
              update_label_change label;
              has_changed := true;
              ()
            with Not_found -> () ) in
        Gconfig.add_modifiable_mono_font_view source_view#misc;
        source_view#source_buffer#set_language why_lang;
        (* We have to create the tags for background colors for each view.
           They are not reusable from the other views.  *)
        create_colors source_view;
        Gconfig.set_fonts ()
      end in
  create_source_view



(* End of notebook *)

(*
  2.2.2.2 a vertical pan which contains [vbox2222]
    2.2.2.2.1 the input field to type commands [hbox22221]
    2.2.2.2.2 a scrolled window to hold the output of the commands [message_zone]
*)
let vbox2222 = GPack.vbox ~packing:vpan222#add  ()

(* 2.2.2.2.1 Horizontal box [hbox22221]
     [monitor] number of scheduled/running provers
     [command_entry] Commands to run on the session
*)
let hbox22221 =
  GPack.hbox
    ~packing:(vbox2222#pack ?from:None ?expand:None ?fill:None ?padding:None) ()

let monitor =
  GMisc.label
    ~text:"  0/0/0"
    ~width:100
    ~xalign:0.0
    ~packing:(hbox22221#pack ?from:None ?expand:None ?fill:None ?padding:None) ()

let command_entry = GEdit.entry ~packing:hbox22221#add ()

(* Part 2.2.2.2.2 contains messages returned by the IDE/server *)
let messages_notebook = GPack.notebook ~packing:vbox2222#add ()

let error_page,error_view =
  let label = GMisc.label ~text:"Messages" () in
  0, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(messages_notebook#append_page ~tab_label:label#coerce w)) ()

let log_page,log_view =
  let label = GMisc.label ~text:"Log" () in
  1, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(messages_notebook#append_page ~tab_label:label#coerce w)) ()

(* tab 3: edited proof *)
let edited_page,edited_tab =
  let label = GMisc.label ~text:"Edited proof" () in
  2, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(messages_notebook#append_page ~tab_label:label#coerce w)) ()

let scrolled_edited_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT ~packing:edited_tab#add ()

let edited_view =
  GSourceView2.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_edited_view#add
    ()

(* tab 4: prover output *)
let output_page,output_tab =
  let label = GMisc.label ~text:"Prover output" () in
  3, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(messages_notebook#append_page ~tab_label:label#coerce w)) ()

let scrolled_output_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT ~packing:output_tab#add ()

let output_view =
  GSourceView2.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_output_view#add
    ()


(* tab 5: counterexample *)
let counterexample_page,counterexample_tab =
  let label = GMisc.label ~text:"Counterexample" () in
  4, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(messages_notebook#append_page ~tab_label:label#coerce w)) ()

let scrolled_counterexample_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT ~packing:counterexample_tab#add ()

let counterexample_view =
  GSourceView2.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_counterexample_view#add
    ()





let message_zone =
  let sv = GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~shadow_type:`ETCHED_OUT ~packing:error_view#add ()
  in
  GText.view ~editable:false ~cursor_visible:false
    ~packing:sv#add ()

let log_zone =
  let sv = GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~shadow_type:`ETCHED_OUT ~packing:log_view#add ()
  in
  GText.view ~editable:false ~cursor_visible:false
    ~packing:sv#add ()

(* Create a tag for errors in the message zone. *)
let message_zone_error_tag = message_zone#buffer#create_tag
  ~name:"error" [`BACKGROUND gconfig.neg_premise_color]

(**** Message-zone printing functions *****)

let add_to_log mark s =
  log_zone#buffer#insert ("\n--------["^ mark ^"]--------\n");
  log_zone#buffer#insert s;
  log_zone#scroll_to_mark `INSERT

(* Function used to print stuff on the message_zone *)
let print_message ~kind ~mark fmt =
  Format.kfprintf
    (fun _ -> let s = flush_str_formatter () in
              add_to_log mark s;
              if kind>0 then message_zone#buffer#set_text s)
    str_formatter
    fmt


(**** Monitor *****)

let fan n =
  match n mod 4 with
    | 0 -> "|"
    | 1 | -3 -> "\\"
    | 2 | -2 -> "-"
    | 3 | -1 -> "/"
    | _ -> assert false

let update_monitor =
  let c = ref 0 in
  fun t s r ->
  reset_gc ();
  incr c;
  let f = if r=0 then "  " else fan (!c / 2) ^ " " in
  monitor#set_text
    (f ^ (string_of_int t) ^ "/" ^ (string_of_int s) ^ "/" ^ (string_of_int r))





(****************************)
(* command entry completion *)
(****************************)

let completion_cols = new GTree.column_list
let completion_col = completion_cols#add Gobject.Data.string
let completion_model = GTree.tree_store completion_cols

let command_entry_completion : GEdit.entry_completion =
  GEdit.entry_completion ~model:completion_model ~minimum_key_length:1 ~entry:command_entry ()

let add_completion_entry s =
  let row = completion_model#append () in
  completion_model#set ~row ~column:completion_col s

let match_function s iter =
  let candidate = completion_model#get ~row:iter ~column:completion_col in
  try
    ignore (Str.search_forward (Str.regexp_string_case_fold s) candidate 0);
    true
  with Not_found -> false

(* see also init_compeltion below *)

(*********************)
(* Terminal history  *)
(*********************)

let list_commands = create_history()

let _ =
  command_entry#event#connect#key_press
    ~callback:(fun (ev: 'a Gdk.event) ->
      match GdkEvent.Key.keyval ev with
      | k when k = GdkKeysyms._Up -> (* Arrow up *)
          let s = print_next_command list_commands in
          (match s with
          | None -> true
          | Some s ->
              (command_entry#set_text s; true))
      | k when k = GdkKeysyms._Down -> (* Arrow down *)
          let s = print_prev_command list_commands in
          (match s with
          | None -> true
          | Some s ->
              (command_entry#set_text s; true))
      | _ -> false
      )

let () = send_session_config_to_server ()

(********************)
(* Locations colors *)
(********************)

(* This apply a background [color] on a location given by its file view [v] line
   [l] beginning char [b] and end char [e]. *)
let color_loc (v:GSourceView2.source_view) ~color l b e =
  let buf = v#buffer in
  let top = buf#start_iter in
  let start = top#forward_lines (l-1) in
  let start = start#forward_chars b in
  let stop = start#forward_chars (e-b) in
  buf#apply_tag_by_name ~start ~stop color

let convert_color (color: color): string =
  match color with
  | Neg_premise_color -> "neg_premise_tag"
  | Premise_color -> "premise_tag"
  | Goal_color -> "goal_tag"

let move_to_line ~yalign (v : GSourceView2.source_view) line =
  let line = max 0 (line - 1) in
  let line = min line v#buffer#line_count in
  let it = v#buffer#get_iter (`LINE line) in
  v#buffer#place_cursor ~where:it;
  let mark = `MARK (v#buffer#create_mark it) in
  v#scroll_to_mark ~use_align:true ~yalign mark

(* Add a color tag on the right locations on the correct file.
   If the file was not open yet, nothing is done *)
let color_loc ~color loc =
  let f, l, b, e = Loc.get loc in
  try
    let (_, v, _, _) = get_source_view_table f in
    let color = convert_color color in
    color_loc ~color v l b e
  with
  | Nosourceview _ ->
      (* If the file is not present do nothing *)
      print_message ~kind:0 ~mark:"color_loc" "%s" "No source view yet"

(* Scroll to a specific locations *)
let scroll_to_loc ~force_tab_switch loc_of_goal =
  match loc_of_goal with
  | None -> ()
  | Some (loc, _) ->
    let f, l, _, _ = Loc.get loc in
    try
      let (n, v, _, _) = get_source_view_table f in
      if force_tab_switch then
        (Debug.dprintf debug "tab switch to page %d@." n;
                       notebook#goto_page n);
      move_to_line ~yalign:0.0 v l
    with Nosourceview _ -> ()

(* Erase the colors and apply the colors given by l (which come from the task)
   to appropriate source files *)
let apply_loc_on_source (l: (Loc.position * color) list) =
  Hstr.iter (fun _ (_, v, _, _) -> erase_color_loc v) source_view_table;
  List.iter (fun (loc, color) ->
    color_loc ~color loc) l;
  let loc_of_goal =
    (* TODO the last location sent seems more relevant thus the rev. This
       should be changed, the sent task should contain the information of where
       to scroll and the list of locations is far too long. *)
    try Some (List.find (fun (_, color) -> color = Goal_color) (List.rev l))
    with Not_found -> None
  in
  scroll_to_loc ~force_tab_switch:false loc_of_goal

(*******************)
(* The "View" menu *)
(*******************)

let view_menu = factory#add_submenu "_View"
let view_factory = new GMenu.factory view_menu ~accel_group

(* goals view is not yet multi-selectable
let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._A
    ~label:"Select all"
    ~callback:(fun () -> goals_view#selection#select_all ()) ()
 *)

let (_ : GMenu.menu_item) =
  view_factory#add_item ~key:GdkKeysyms._plus
    ~callback:enlarge_fonts "Enlarge font"

let (_ : GMenu.menu_item) =
    view_factory#add_item ~key:GdkKeysyms._minus
      ~callback:reduce_fonts "Reduce font"

let collapse_iter iter =
  let path = goals_model#get_path iter in
  goals_view#collapse_row path

let rec collapse_proven_goals_from_iter iter =
  let node_id = get_node_id iter in
  let is_proved = get_node_proved node_id in
  if is_proved then
    collapse_iter iter
  else
    let n = goals_model#iter_n_children (Some iter) in
    for i = 0 to (n - 1) do
      collapse_proven_goals_from_iter (goals_model#iter_children ?nth:(Some i) (Some iter))
    done

let collapse_proven_goals () =
  match goals_model#get_iter_first with
  | None -> ()
  | Some root_iter -> collapse_proven_goals_from_iter root_iter

let () =
  let i = view_factory#add_item
            "Collapse proven goals"
            ~callback:(fun () -> collapse_proven_goals ())
  in
  i#misc#set_tooltip_markup "Collapse all sub-nodes of proven nodes (shortcut: Ctrl-C)";
  i#add_accelerator ~group:tools_accel_group ~modi:[`CONTROL] GdkKeysyms._C;
  let i = view_factory#add_item
            "Expand all"
            ~callback:(fun () -> goals_view#expand_all ())
  in
  i#misc#set_tooltip_markup "Expand all nodes of the tree view (shortcut: Ctrl-E)";
  i#add_accelerator ~group:tools_accel_group ~modi:[`CONTROL] GdkKeysyms._E


let () =
  Gconfig.add_modifiable_sans_font_view goals_view#misc;
  Gconfig.add_modifiable_mono_font_view monitor#misc;
  Gconfig.add_modifiable_mono_font_view task_view#misc;
  Gconfig.add_modifiable_mono_font_view edited_view#misc;
  Gconfig.add_modifiable_mono_font_view output_view#misc;
  Gconfig.add_modifiable_mono_font_view counterexample_view#misc;
  Gconfig.add_modifiable_mono_font_view command_entry#misc;
  Gconfig.add_modifiable_mono_font_view message_zone#misc;
  task_view#source_buffer#set_language why_lang;
  Gconfig.set_fonts ()




(******************)
(*    actions     *)
(******************)

let get_selected_row_references () =
  List.map
    (fun path -> goals_model#get_row_reference path)
    goals_view#selection#get_selected_rows

(* unused
let rec update_status_column_from_iter cont iter =
  set_status_column iter;
  match goals_model#iter_parent iter with
  | Some p -> update_status_column_from_iter cont p
  | None -> ()
*)

(* TODO Unused functions. Map these to a key or remove it *)
let move_current_row_selection_up () =
  let current_view = List.hd (goals_view#selection#get_selected_rows) in
  ignore (GTree.Path.up current_view);
  let row_up = goals_model#get_row_reference current_view in
  goals_view#selection#select_iter row_up#iter

let move_current_row_selection_down () =
  let current_iter =
    try
      let current_view = List.hd (goals_view#selection#get_selected_rows) in
      let current_row = goals_model#get_row_reference current_view in
      Some current_row#iter
    with Not_found ->
      None
  in
  let child = goals_model#iter_children current_iter in
  goals_view#selection#select_iter child

let clear_command_entry () = command_entry#set_text ""

let interp cmd =
  (* TODO: do some preprocessing for queries, or leave everything to server ? *)
  let rows = get_selected_row_references () in
  let ids =
    match rows with
      | [] -> [root_node]
      | _ -> List.map (fun n -> get_node_id n#iter) rows
  in
  List.iter (fun id -> send_request (Command_req (id, cmd))) ids;
  clear_command_entry ()

let (_ : GtkSignal.id) =
  command_entry#connect#activate
    ~callback:(fun () -> add_command list_commands command_entry#text;
      interp command_entry#text)

let on_selected_row r =
  try
    let id = get_node_id r#iter in
    let typ = get_node_type id in
    match typ with
    | NGoal ->
      let detached = get_node_detached id in
      if detached then
        task_view#source_buffer#set_text ""
      else
        let b = gconfig.intro_premises in
        let c = gconfig.show_full_context in
        send_request (Get_task(id,b,c,true))
    | NProofAttempt ->
       let (pa, _obs, _l) = Hint.find node_id_pa id in
       let output_text =
         match pa with
         | Controller_itp.Done pr -> pr.Call_provers.pr_output
         | Controller_itp.Undone -> "no result known"
         | Controller_itp.Detached -> "detached proof attempt: parent goal has no task"
         | Controller_itp.Interrupted -> "prover run was interrupted"
         | Controller_itp.Scheduled -> "proof scheduled but not running yet"
         | Controller_itp.Running -> "prover currently running"
         | Controller_itp.InternalFailure e ->
            (Pp.sprintf "internal failure: %a" Exn_printer.exn_printer e)
         | Controller_itp.Uninstalled _p -> "uninstalled prover"
         | Controller_itp.UpgradeProver _p -> "upgraded prover"
       in
       let output_text =
         if output_text = "" then
           "(no output known, you may consider running the prover again)"
         else output_text
       in
       output_view#source_buffer#set_text output_text;
       edited_view#source_buffer#set_text "(not yet available)";
       edited_view#scroll_to_mark `INSERT;
       counterexample_view#source_buffer#set_text "(not yet available)";
       counterexample_view#scroll_to_mark `INSERT
    | _ ->
       let b = gconfig.intro_premises in
       let c = gconfig.show_full_context in
       send_request (Get_task(id,b,c,true))
  with
    | Not_found -> task_view#source_buffer#set_text ""


let (_ : GtkSignal.id) =
  goals_view#selection#connect#after#changed ~callback:
    (fun () ->
     Debug.dprintf debug "running callback of goals_view#selection#connect#after#changed@.";
     begin
       match get_selected_row_references () with
       | [r] -> on_selected_row r;
       | _ -> ()
     end (* ;
     command_entry#misc#grab_focus () *))

let (_ : GtkSignal.id) =
  let callback ev =
    Debug.dprintf debug "running callback of goals_view#event#connect#button_press@.";
    let n = GdkEvent.Button.button ev in
    begin
      Debug.dprintf debug "button number %d was clicked on the tree view@." n;
      match n with
      | 1 -> (* Left click *) false
      | 2 -> (* Middle click *) false
      | 3 -> (* Right click *)
         Debug.dprintf debug "before tools_menu#popup@.";
         tools_menu#popup ~button:3 ~time:(GdkEvent.Button.time ev);
         Debug.dprintf debug "after tools_menu#popup@.";
         true
      | _ -> (* Error case TODO *) assert false
    end
  in
  goals_view#event#connect#button_press ~callback


(*************************************)
(* Commands of the Experimental menu *)
(*************************************)

let exp_menu = factory#add_submenu "_Experimental"
let exp_factory = new GMenu.factory exp_menu ~accel_group


(* Current copied node *)
let saved_copy = ref None

let copy () =
  match get_selected_row_references () with
  | [r] -> let n = get_node_id r#iter in
    saved_copy := Some n
  | _ -> ()

let paste () =
  match get_selected_row_references () with
  | [r] ->
      let m = get_node_id r#iter in
    (match !saved_copy with
    | Some n -> send_request (Copy_paste (n, m))
    | None -> ())
  | _ -> ()

let detached_copy () =
  match get_selected_row_references () with
  | [r] -> let n = get_node_id r#iter in
    send_request (Copy_detached n)
  | _ -> ()

let (_ : GMenu.menu_item) = exp_factory#add_item ~callback:copy "Copy"

let (_ : GMenu.menu_item) = exp_factory#add_item ~callback:paste "Paste"

let (_ : GMenu.menu_item) = exp_factory#add_item ~callback:detached_copy "Detached copy"

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

let select_file ~request =
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
          | Some f -> request f
      end
  | `DELETE_EVENT | `CANCEL -> ()
  end ;
  d#destroy ()

let (_ : GtkSignal.id) =
  menu_add_file#connect#activate ~callback:(fun () ->
      select_file ~request:(fun f -> send_request (Add_file_req f)))

(*************************)
(* Notification Handling *)
(*************************)

let treat_message_notification msg = match msg with
  (* TODO: do something ! *)
  | Proof_error (_id, s)                        ->
     print_message ~kind:1 ~mark:"[Proof_error]" "%s" s
  | Transf_error (_id, tr_name, arg, loc, msg, doc) ->
      if arg = "" then
        print_message ~kind:1 ~mark:"Transformation Error"
                      "%s\nTransformation failed: \n%s\n\n%s" msg tr_name doc
      else
        begin
          let buf = message_zone#buffer in
          (* remove all coloration in message_zone *)
          buf#remove_tag_by_name "error" ~start:buf#start_iter ~stop:buf#end_iter;
          print_message ~kind:1 ~mark:"Transformation Error"
                        "%s\nTransformation failed. \nOn argument: \n%s \n%s\n\n%s"
            tr_name arg msg doc;
          let color = "error" in
          let _, _, beg_char, end_char = Loc.get loc in
          let start = buf#start_iter#forward_lines 3 in
          buf#apply_tag_by_name
            ~start:(start#forward_chars beg_char)
            ~stop:(start#forward_chars end_char)
            color
        end
  | Strat_error (_id, s) ->
     print_message ~kind:1 ~mark:"Strat_error" "%s" s
  | Replay_Info s ->
     print_message ~kind:0 ~mark:"Replay_info" "%s" s
  | Query_Info (_id, s) ->
     print_message ~kind:1 ~mark:"Query_info" "%s" s
  | Query_Error (_id, s) ->
     print_message ~kind:1 ~mark:"Query_error" "%s" s
  | Help s ->
     print_message ~kind:1 ~mark:"Help" "%s" s
  | Information s ->
     print_message ~kind:1 ~mark:"Information" "%s" s
  | Task_Monitor (t, s, r) -> update_monitor t s r
  | Open_File_Error s ->
     print_message ~kind:0 ~mark:"Open_File_Error" "%s" s
  | Parse_Or_Type_Error (loc, s) ->
    begin
      (* TODO find a new color *)
      scroll_to_loc ~force_tab_switch:true (Some (loc,0));
      color_loc ~color:Goal_color loc;
      print_message ~kind:1 ~mark:"Parse_Or_Type_Error]" "%s" s
    end
  | File_Saved f                 ->
    begin
      try
        let (_source_page, _source_view, b, l) = Hstr.find source_view_table f in
        b := false;
        update_label_saved l;
        print_message ~kind:1 ~mark:"File_Saved" "%s was saved" f
      with
      | Not_found                ->
          print_message ~kind:1 ~mark:"File_Saved"
                        "Please report: %s was not found in IDE but was saved in session" f
    end
  | Error s                      ->
     print_message ~kind:1 ~mark:"General request failure" "%s" s


(***********************)
(* First Unproven goal *)
(***********************)

let is_goal node =
  get_node_type node = NGoal

let proved node =
  get_node_proved node

let children node =
  let iter = (get_node_row node)#iter in
  let n = goals_model#iter_n_children (Some iter) in
  let acc = ref [] in
  for i = 0 to (n-1) do
    let new_iter = goals_model#iter_children ?nth:(Some i) (Some iter) in
    let child_node = get_node_id new_iter in
    if (get_node_type child_node != NProofAttempt) then
      acc := child_node :: !acc
  done;
  !acc

let get_parent node =
  let iter = (get_node_row node)#iter in
  let parent_iter = goals_model#iter_parent iter in
  match parent_iter with
  | None -> None
  | Some parent -> Some (get_node_id parent)

let if_selected_alone id f =
  match get_selected_row_references () with
  | [r] ->
     let i = get_node_id r#iter in
     if i = id || Some i = get_parent id then f id
  | _ -> ()


(**************************)
(* Graphical proof status *)
(**************************)

let image_of_pa_status ~obsolete pa =
  match pa with
  | Controller_itp.Undone
  | Controller_itp.Interrupted -> !image_undone
  | Controller_itp.Scheduled -> !image_scheduled
  | Controller_itp.Running -> !image_running
  | Controller_itp.InternalFailure _e -> !image_failure
  | Controller_itp.Detached -> !image_undone (* TODO !image_detached *)
  | Controller_itp.Uninstalled _p -> !image_undone (* TODO !image_uninstalled *)
  | Controller_itp.UpgradeProver _p -> !image_undone
  | Controller_itp.Done r ->
    let pr_answer = r.Call_provers.pr_answer in
    begin
      match pr_answer with
      | Call_provers.Valid ->
        if obsolete then !image_valid_obs else !image_valid
      | Call_provers.Invalid ->
        if obsolete then !image_invalid_obs else !image_invalid
      | Call_provers.Timeout ->
        if obsolete then !image_timeout_obs else !image_timeout
      | Call_provers.OutOfMemory ->
        if obsolete then !image_outofmemory_obs else !image_outofmemory
      | Call_provers.StepLimitExceeded ->
        if obsolete then !image_steplimitexceeded_obs
        else !image_steplimitexceeded
      | Call_provers.Unknown _ ->
        if obsolete then !image_unknown_obs else !image_unknown
      | Call_provers.Failure _ ->
        if obsolete then !image_failure_obs else !image_failure
      | Call_provers.HighFailure ->
        if obsolete then !image_failure_obs else !image_failure
    end


module S = Session_itp
module C = Controller_itp


(* Returns true if the current row is an ancestor of the selected row *)
let selected_ancestor row =
  match get_selected_row_references () with
  | [selected_row] ->
      not (goals_model#is_ancestor ~iter:row#iter ~descendant:selected_row#iter)
  | _ -> false

let set_status_and_time_column ?limit row =
  let id = get_node_id row#iter in
  let proved = get_node_proved id in
  let detached = get_node_detached id in
  let image = match get_node_type id with
    | NRoot -> assert false
    | NFile
    | NTheory
    | NTransformation
    | NGoal ->
       if detached then
         begin
           goals_model#set ~row:row#iter ~column:time_column "(detached)";
           !image_valid_obs
         end
      else
        if proved
        then begin
          Debug.dprintf debug "Collapsing row for proved node %d@." id;
          (* We should only collapse if it does not collapse the selected row
             because collapsing unselects the focused row in this case. *)
          if selected_ancestor row then
             goals_view#collapse_row (goals_model#get_path row#iter);
          !image_valid
          end
        else begin
            (* goals_view#expand_row (goals_model#get_path row#iter); *)
            !image_unknown
          end
    | NProofAttempt ->
      let pa = get_node_proof_attempt id in
      let obs = get_node_obs id in
      let t = match pa with
        | C.Done r ->
           let time = r.Call_provers.pr_time in
           let steps = r.Call_provers.pr_steps in
           let s =
             if gconfig.show_time_limit then
               match limit with
                 | Some l ->
                    Format.sprintf "%.2f [%d.0]" time
                                   (l.Call_provers.limit_time)
                 | None ->
                    Format.sprintf "%.2f" time
             else
               Format.sprintf "%.2f" time
           in
           if steps >= 0 then
	     Format.sprintf "%s (steps: %d)" s steps
           else
	     s
        | C.InternalFailure _ -> "(internal failure)"
        | C.Interrupted -> "(interrupted)"
        | C.Undone -> "(undone)"
        | C.Uninstalled _ -> "(uninstalled prover)"
        | C.UpgradeProver _ -> "(upgraded prover)"
        | C.Scheduled -> "(scheduled)"
        | C.Running -> "(running)"
        | C.Detached -> "(detached)"
      in
      let t = match pa with
        | C.Scheduled | C.Running ->
           begin
             match limit with
             | Some l -> t ^
                Format.sprintf " [limit=%d sec., %d M]"
                               (l.Call_provers.limit_time)
                               (l.Call_provers.limit_mem)
             | None -> t ^ " [no limit known]"
           end
        | _ -> t
      in
      let t = if obs then t ^ " (obsolete)" else t in
      let t = if detached then t ^ " (detached)" else t in
      goals_model#set ~row:row#iter ~column:time_column t;
      image_of_pa_status ~obsolete:obs pa
  in
  goals_model#set ~row:row#iter ~column:status_column image


let new_node ?parent id name typ detached =
  if not (Hint.mem node_id_to_gtree id) then begin
    Hint.add node_id_type id typ;
    Hint.add node_id_detached id detached;
    (* The tree does not have a root by default so the task is a forest with
       several root files *)
    let iter =
      match parent with
      | None -> goals_model#append ()
      | Some p -> goals_model#append ~parent:p#iter ()
    in
    goals_model#set ~row:iter ~column:name_column name;
    goals_model#set ~row:iter ~column:node_id_column id;
    goals_model#set ~row:iter ~column:icon_column
      (match typ with
         | NGoal -> !image_goal
         | NRoot | NFile -> !image_file
         | NTheory -> !image_theory
         | NTransformation -> !image_transf
         | NProofAttempt -> !image_prover);
    let path = goals_model#get_path iter in
    let new_ref = goals_model#get_row_reference path in
    Hint.add node_id_to_gtree id new_ref;
    set_status_and_time_column new_ref;
    new_ref
  end
  else
    Hint.find node_id_to_gtree id


(**************************************************)
(* tools submenus for strategies, provers and transformations *)
(**************************************************)

let sanitize_markup x =
  let remove = function
    | '_' -> "__"
    | c -> String.make 1 c in
  Ident.sanitizer remove remove (Glib.Markup.escape_text x)

let string_of_desc desc =
  let print_trans_desc fmt (x,r) =
    fprintf fmt "@[<hov 2>%s@\n%a@]" x Pp.formatted r
  in Glib.Markup.escape_text (Pp.string_of print_trans_desc desc)


let pr_shortcut s = if s = "" then "" else " (shortcut: " ^ s ^ ")"

let parse_shortcut_as_key s =
  match GtkData.AccelGroup.parse s with
  | (0,[]) ->
     Debug.dprintf debug "Shortcut '%s' cannot be parsed as a key@." s;
     None
  | (key, modi) ->
     let name = GtkData.AccelGroup.name ~key ~modi in
     Debug.dprintf debug "Shortcut '%s' parsed as key '%s'@." s name;
     Some (name, key, modi)

let add_submenu_strategy (shortcut,strategy) =
  let  i = create_menu_item
             strategies_factory
             strategy
             ("run strategy " ^ strategy ^ " on selected goal" ^ pr_shortcut shortcut)
  in
  Opt.iter (fun (_,key,modi) -> i#add_accelerator ~group:tools_accel_group ~modi key)
          (parse_shortcut_as_key shortcut);
  let callback () =
    Debug.dprintf debug "interp command '%s'@." shortcut;
    interp shortcut
  in
  connect_menu_item i ~callback

let add_submenu_prover (shortcut,prover_name,prover_parseable_name) =
  let  i = create_menu_item
             provers_factory
             prover_name
             ("run prover " ^ prover_name ^ " on selected goal" ^ pr_shortcut shortcut)
  in
  Opt.iter (fun (_,key,modi) -> i#add_accelerator ~group:tools_accel_group ~modi key)
          (parse_shortcut_as_key shortcut);
  let callback () =
    Debug.dprintf debug "interp command '%s'@." prover_parseable_name;
    interp prover_parseable_name
  in
  connect_menu_item i ~callback



let init_completion provers transformations strategies commands =
  (* add the names of all the the transformations *)
  List.iter add_completion_entry transformations;
  (* add the name of the commands *)
  List.iter add_completion_entry commands;
  (* todo: add queries *)

  (* add provers *)

  let all_strings =
    List.fold_left (fun acc (s,_,p) ->
                    Debug.dprintf debug "string for completion: '%s' '%s'@." s p;
                    if s = "" then p :: acc else s :: p :: acc) [] provers
  in
  List.iter add_completion_entry all_strings;
  let provers_sorted =
    List.sort (fun (_,h1,_) (_,h2,_) ->
               String.compare (Strings.lowercase h1) (Strings.lowercase h2))
              provers
  in
  List.iter add_submenu_prover provers_sorted;

  List.iter add_submenu_strategy strategies;

  command_entry_completion#set_text_column completion_col;
  command_entry_completion#set_match_func match_function;

  command_entry#set_completion command_entry_completion


let () =
  let transformations = Server_utils.list_transforms () in
  let add_submenu_transform name filter =
    let submenu = tools_factory#add_submenu name in
    let submenu = new GMenu.factory submenu ~accel_group in
    let iter ((name,_) as desc) =
      let callback () = interp name in
      let i = create_menu_item submenu (sanitize_markup name) (string_of_desc desc) in
      connect_menu_item i ~callback
    in
    let trans = List.filter filter transformations in
    List.iter iter trans
  in
  add_submenu_transform
    "transformations (a-e)"
    (fun (x,_) -> x < "eliminate");
  add_submenu_transform
    "transformations (eliminate)"
    (fun (x,_) -> x >= "eliminate" && x < "eliminatf");
  add_submenu_transform
    "transformations (e-r)"
    (fun (x,_) -> x >= "eliminatf" && x < "s");
  add_submenu_transform "transformations (s-z)"
                        (fun (x,_) -> x >= "s");
  let ( _ : GMenu.menu_item) = tools_factory#add_separator () in
  ()

(* complete the tools menu *)

let edit_menu_item =
  create_menu_item tools_factory "Edit"
                   "View or edit proof script (shortcut: e)"
let () =
  edit_menu_item#add_accelerator ~group:tools_accel_group ~modi:[] GdkKeysyms._e

let replay_menu_item =
  create_menu_item tools_factory "Replay obsolete"
                   "Replay all obsolete proofs (shortcut: r)"
let () =
  replay_menu_item#add_accelerator ~group:tools_accel_group ~modi:[] GdkKeysyms._r

let clean_menu_item =
  create_menu_item tools_factory  "Clean"
                   "Remove unsuccessful proofs or transformations that are below a proved goal (shortcut: c)"
let () =
  clean_menu_item#add_accelerator ~group:tools_accel_group ~modi:[] GdkKeysyms._c


let remove_item =
  create_menu_item tools_factory "Remove"
                   "Remove the selected proof attempts or transformations (shortcut: x)"
let () =
  remove_item#add_accelerator ~group:tools_accel_group ~modi:[] GdkKeysyms._x


let mark_obsolete_item =
  create_menu_item tools_factory "Mark obsolete"
                   "Mark all proof nodes below the current selected nodes as obsolete (shortcut: o)"
let () =
  mark_obsolete_item#add_accelerator ~group:tools_accel_group ~modi:[] GdkKeysyms._o


let focus_item =
  create_menu_item tools_factory "Focus"
    "Focus on proof node"

let unfocus_item =
  create_menu_item tools_factory "Unfocus"
    "Unfocus"

let () =
  connect_menu_item
    replay_menu_item
    ~callback:(fun () -> send_request Replay_req);
  connect_menu_item
    clean_menu_item
    ~callback:(fun _ -> send_request Clean_req);
  connect_menu_item
    remove_item
    ~callback:(fun () ->
               match get_selected_row_references () with
               | [r] ->
                   let id = get_node_id r#iter in
                   send_request (Remove_subtree id)
               | _ -> print_message ~kind:1 ~mark:"Remove_subtree error"
                        "Select only one node to perform the remove node action");
  connect_menu_item
    edit_menu_item
    ~callback:(fun () ->
               match get_selected_row_references () with
               | [r] ->
                   let id = get_node_id r#iter in
                   send_request (Command_req (id,"edit"))
               | _ -> print_message ~kind:1 ~mark:"Edit error"
                        "Select only one node to perform the edit action");
  connect_menu_item
    mark_obsolete_item
    ~callback:(fun () ->
               match get_selected_row_references () with
               | [r] ->
                   let id = get_node_id r#iter in
                   send_request (Mark_obsolete_req id)
               | _ -> print_message ~kind:1 ~mark:"Mark_obsolete error"
                        "Select only one node to perform the mark obsolete action");
  connect_menu_item
    focus_item
    ~callback:(fun () ->
      match get_selected_row_references () with
      | [r] ->
          let id = get_node_id r#iter in
          send_request (Focus_req id)
      | _ -> print_message ~kind:1 ~mark:"Focus_req error"
                        "Select only one node to perform the focus action");
  connect_menu_item
    unfocus_item
    ~callback:(fun () -> send_request Unfocus_req)


(* the command-line *)

let check_uninstalled_prover =
  let uninstalled_prover_seen = Whyconf.Hprover.create 3 in
  fun p ->
  if not (Whyconf.Hprover.mem uninstalled_prover_seen p)
  then begin
      Whyconf.Hprover.add uninstalled_prover_seen p ();
      uninstalled_prover_dialog gconfig p
    end


let treat_notification n =
  Protocol_why3ide.print_notify_debug n;
  begin match n with
  | Reset_whole_tree -> clear_tree_and_table goals_model
  | Node_change (id, uinfo)        ->
     begin
       match uinfo with
       | Proved b ->
          let old =
            try
              let o = Hint.find node_id_proved id in
              Hint.replace node_id_proved id b;
              o
            with Not_found ->
              Hint.add node_id_proved id b;
              (* new node, then expand it if not proved *)
              not b
          in
          if old <> b then begin
              set_status_and_time_column (get_node_row id);
              if b then
                (* Trying to move cursor on first unproven goal around
             on all cases but not when proofAttempt is updated because
             ad hoc debugging. *)
                if_selected_alone id (fun _ -> send_request (Get_first_unproven_node id))
              else
                begin
                  try
                    let row = Hint.find node_id_to_gtree id in
                    let path = row#path in
                    Debug.dprintf debug "Expanding row for unproved node %d@." id;
                    goals_view#expand_to_path path
                  with Not_found ->
                    Debug.dprintf debug "Warning: no gtk row registered for node %d@." id
                end
            end
       | Name_change n ->
          let row = get_node_row id in
          goals_model#set ~row:row#iter ~column:name_column n
       | Proof_status_change (pa, obs, l) ->
          let r = get_node_row id in
          Hint.replace node_id_pa id (pa, obs, l);
          set_status_and_time_column ~limit:l r;
          match pa with
          | Controller_itp.Uninstalled p -> check_uninstalled_prover p
          | _ -> ()
     end
  | Next_Unproven_Node_Id (asked_id, next_unproved_id) ->
      if_selected_alone asked_id
          (fun _ ->
            (* Unselect the potentially selected goal to avoid having two tasks
               selected at once when a prover successfully end. To continue the
               proof, it is better to only have the new goal selected *)
            goals_view#selection#unselect_all ();
            let iter = (get_node_row next_unproved_id)#iter in
            goals_view#selection#select_iter iter)
  | New_node (id, parent_id, typ, name, detached) ->
     begin
       let name =
         if typ = NGoal then
           List.hd (Strings.rev_split '.' name)
         else name
       in
       try
         let parent = get_node_row parent_id in
         ignore (new_node ~parent id name typ detached)
       with Not_found ->
         ignore (new_node id name typ detached)
     end
  | Remove id                     ->
     let n = get_node_row id in
     ignore (goals_model#remove(n#iter));
     Hint.remove node_id_to_gtree id;
     Hint.remove node_id_type id;
     Hint.remove node_id_proved id;
     Hint.remove node_id_pa id
  | Initialized g_info            ->
     (* TODO: treat other *)
     init_completion g_info.provers g_info.transformations g_info.strategies g_info.commands;
  | Saved                         ->
      session_needs_saving := false;
      print_message ~kind:1 ~mark:"Saved action info"
                        "Session saved.";
      if !quit_on_saved = true then
        exit_function_safe ()
  | Message (msg)                 -> treat_message_notification msg
  | Task (id, s, list_loc)        ->
     if_selected_alone
       id
       (fun _ -> task_view#source_buffer#set_text s;
                 apply_loc_on_source list_loc;
                 (* scroll to end of text *)
                 task_view#scroll_to_mark `INSERT)
  | File_contents (file_name, content) ->
    begin
      try
        let (_, sc_view, b, l) = Hstr.find source_view_table file_name in
        sc_view#source_buffer#set_text content;
        update_label_saved l;
        b := false;
      with
      | Not_found -> create_source_view file_name content
    end
  | Dead _ ->
     print_message ~kind:1 ~mark:"Server Dead ?"
                        "Server sent the notification '%a'. Please report."
        print_notify n
  end;
  ()



(*************)
(* Help menu *)
(*************)


let help_menu = factory#add_submenu "_Help"
let help_factory = new GMenu.factory help_menu ~accel_group

let (_ : GMenu.menu_item) =
  help_factory#add_item
    "Legend"
    ~callback:show_legend_window

let (_ : GMenu.menu_item) =
  help_factory#add_item
    "About"
    ~callback:show_about_window


(***********************************)
(* accel group switching           *)
(* when entering/leaving tree view *)
(***********************************)

let () =
  let (_:GtkSignal.id) =
    goals_view#event#connect#focus_in
      ~callback:(fun _ -> main_window#add_accel_group tools_accel_group; true)
  in
  let (_:GtkSignal.id) =
    goals_view#event#connect#focus_out
      ~callback:(fun _ ->
                 GtkWindow.Window.remove_accel_group main_window#as_window tools_accel_group; true)
  in
  ()



(***********************)
(* start the interface *)
(***********************)

let () =
  Scheduler.timeout ~ms:Controller_itp.default_delay_ms
    (fun () -> List.iter treat_notification (get_notified ()); true);
  main_window#add_accel_group accel_group;
  main_window#set_icon (Some !Gconfig.why_icon);
  message_zone#buffer#set_text "Welcome to Why3 IDE\ntype 'help' for help";
  main_window#show ();
  GMain.main ()
