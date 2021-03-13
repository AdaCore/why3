(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2021 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Format
open Gconfig
open Wstdlib
open Ide_utils
open History
open Itp_communication
open Gtkcompat

let debug = Debug.lookup_flag "ide_info"
let debug_stack_trace = Debug.lookup_flag "stack_trace"

let () =
  (* Allow global locations to be saved for Find_ident_req *)
  Debug.set_flag Glob.flag

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

  (* print_ext_any just use the pretty function here *)
  let print_ext_any print_any fmt t =
    print_any fmt t

end

let get_notified = Protocol_why3ide.get_notified

let send_request r = Protocol_why3ide.send_request r

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

let when_idle (f:unit->unit) =
  let (_:GMain.Idle.id) =
    GMain.Idle.add (fun () -> f (); false)
  in ()


(************************)
(* parsing command line *)
(************************)

let files : string Queue.t = Queue.create ()
let opt_parser = ref None
let opt_batch = ref None

let spec =
  let open Getopt in
  [ Key ('F', "format"), Hnd1 (AString, fun s -> opt_parser := Some s),
    "<format> select input format (default: \"why\")";
    Termcode.opt_extra_expl_prefix;
    KLong "batch", Hnd1 (AString, fun s -> opt_batch := Some s), "";
  ]

let usage_str =
  "[<file.why>|<project directory>]...\n\
   Open a graphical interface for Why3."

let env, gconfig =
  try
    let config, env =
      Whyconf.Args.initialize spec (fun f -> Queue.add f files) usage_str
    in
    if Queue.is_empty files then
      Whyconf.Args.exit_with_usage spec usage_str;
    Gconfig.load_config config;
    env, Gconfig.config ()
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "Anomaly while loading configuration: %a@." Exn_printer.exn_printer e;
    exit 1



(********************************)
(* Source language highlighting *)
(********************************)


let (why_lang, any_lang, why3py_lang, why3c_lang) =
  let main = Whyconf.get_main gconfig.config in
  let load_path = Filename.concat (Whyconf.datadir main) "lang" in
  let languages_manager =
    GSourceView.source_language_manager ~default:true
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
  let why3py_lang =
    match languages_manager#language "why3py" with
    | None ->
        eprintf "language file for 'Why3python' not found in directory %s@."
          load_path;
        exit 1
    | Some _ as l -> l in
  let why3c_lang =
    match languages_manager#language "why3c" with
    | None ->
        eprintf "language file for 'Why3c' not found in directory %s@."
          load_path;
        exit 1
    | Some _ as l -> l in
  (why_lang, any_lang, why3py_lang, why3c_lang)

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

(* Generates the tag list (using the current config) *)
let color_tags_list config =
  (* The order of this list influences the priorities of tags *)
  [("error_line_tag", [`BACKGROUND config.error_line_color]); (* less priority *)
   ("premise_tag", [`BACKGROUND config.premise_color]);
   ("neg_premise_tag", [`BACKGROUND config.neg_premise_color]);
   ("goal_tag", [`BACKGROUND config.goal_color]);
   ("error_tag", [`BACKGROUND config.error_color_bg]);
   ("error_tag_msg_zone", [`BACKGROUND gconfig.error_color_msg_zone_bg;
                           `FOREGROUND gconfig.error_color_msg_zone_fg]);
   ("error_font_tag", [`FOREGROUND config.error_color_fg]);
   ("search_tag", [`BACKGROUND config.search_color]);
  ]

(* For each view, we have to recreate the tags.
   TODO The type annotatin is necessary for the type inference to know that <name> is optional. *)
let create_colors config
    (v: <buffer: < create_tag: ?name:string -> GText.tag_property list -> GText.tag;..>; ..>) =
  let list_tags = color_tags_list config in
  List.iter (fun (name, props) ->
      let (_: GText.tag) = v#buffer#create_tag ~name props in ()) list_tags

let remove_tag v tag_name =
  let tag = GtkText.TagTable.lookup v#buffer#tag_table tag_name in
  match tag with
  | None -> ()
  | Some tag -> GtkText.TagTable.remove v#buffer#tag_table tag

let remove_all_tags config v =
  List.iter (fun (s, _) -> remove_tag v s) (color_tags_list config)

(* When colors are changed in the preferences, the tag need to change so we
   remove and regenerate the tags.
   This works only on sourceview (not on message_zone where tags are not added
   by name *)
let update_tags config v =
  remove_all_tags config  v;
  create_colors config v

(* Erase all the source location tags in a source file *)
let erase_color_loc (v:GSourceView.source_view) =
  let buf = v#buffer in
  buf#remove_tag_by_name "premise_tag" ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag_by_name "neg_premise_tag" ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag_by_name "goal_tag" ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag_by_name "error_tag" ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag_by_name "error_line_tag" ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag_by_name "error_font_tag" ~start:buf#start_iter ~stop:buf#end_iter



(*******************)
(* Graphical tools *)
(*******************)

(* Elements needed for usage of graphical elements *)

(* Hold the node_id on which "next" was called to allow differentiating on
   automatic jump from a user jump *)
let manual_next = ref None


(* [quit_on_saved] set to true by exit function to delay quiting after Saved
   notification is received *)
let quit_on_saved = ref false

(* Exit brutally without asking anything *)
let exit_function_unsafe () =
  send_request Exit_req;
  GMain.quit ()

(* Contains triples (tab page, source_view, label_of_tab):
   - tab_page is a unique number for each pages of the notebook
   - source_view is the graphical element inside a tab
   - label_of_tab is the mutable title of the tab
*)
let source_view_table : (int * GSourceView.source_view * GMisc.label) Hstr.t =
  Hstr.create 14

(* The corresponding file does not have a source view *)
exception Nosourceview of string

let get_source_view_table (file:string) =
  match Hstr.find source_view_table file with
  | v -> v
  | exception Not_found -> raise (Nosourceview file)

(* Saving function for sources *)
let save_sources () =
  Hstr.iter
    (fun k (_n, (s: GSourceView.source_view), _l) ->
      if s#source_buffer#modified then
        let text_to_save = s#source_buffer#get_text () in
        send_request (Save_file_req (k, text_to_save))
    )
    source_view_table

(* True if there exist a file which needs saving *)
let files_need_saving () =
  Hstr.fold (fun _k (_, s, _) acc -> acc || s#source_buffer#modified) source_view_table false

(* Ask if the user wants to save session before exit. Exit is then delayed until
   the [Saved] notification is received *)
let exit_function_safe () =
  send_request Check_need_saving_req

let exit_function_handler b =
  if not b && not (files_need_saving ()) then
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

(* Erase colors in all source views *)
let erase_loc_all_view () =
  Hstr.iter (fun _ (_, v, _) -> erase_color_loc v) source_view_table

(* Update name of the tab when the label changes so that it has a * as prefix *)
let update_label_change (label: GMisc.label) =
  let s = label#text in
  erase_loc_all_view ();
  if not (Strings.has_prefix "*" s) then
    label#set_text ("*" ^ s)

(* Update name of the tab when the label is saved. Removes * prefix *)
let update_label_saved (label: GMisc.label) =
  let s = label#text in
  if (Strings.has_prefix "*" s) then
    label#set_text (String.sub s 1 (String.length s - 1))

let make_sources_editable b =
  Hstr.iter
    (fun _ (_,source_view,_) ->
      source_view#set_editable b;
      source_view#set_auto_indent b)
    source_view_table

(**********************)
(* Graphical elements *)
(**********************)

let initialization_complete = ref false
let warnings = Queue.create ()

let record_warning ?loc msg =
  Format.eprintf "%awarning: %s@."
    (Pp.print_option Loc.report_position) loc msg;
  Queue.push (loc,msg) warnings

let () =
  Warning.set_hook record_warning;
  let dir =
    try
      Server_utils.get_session_dir ~allow_mkdir:true files
    with Invalid_argument s ->
      Format.eprintf "Error: %s@." s;
      Whyconf.Args.exit_with_usage spec usage_str
  in
  Server.init_server gconfig.config env dir;
  Queue.iter (fun f ->
      (* Sanitize the command line arguments so that they are always absolute *)
      let f = Sysutil.concat (Sys.getcwd()) f in
      send_request (Add_file_req f)) files;
  send_request Get_global_infos;
  Debug.dprintf debug "Init the GTK interface...@?";
  ignore (GtkMain.Main.init ());
  Debug.dprintf debug " done.@.";
  Gconfig.init ()

let window_title =
  match !opt_batch with
  | Some _ -> "Why3 Batch Mode"
  | None -> "Why3 Interactive Proof Session"

let main_window : GWindow.window =
  let w = GWindow.window ~title:window_title () in
  w#resize ~width:gconfig.window_width ~height:gconfig.window_height;
  (* callback to record the new size of the main window when changed, so
   that on restart the window size is the same as the last session *)
  let (_ : GtkSignal.id) =
    w#misc#connect#size_allocate
      ~callback:
      (fun {Gtk.width=w;Gtk.height=h} ->
       gconfig.window_height <- h;
       gconfig.window_width <- w)
  in
  w

(* the main window contains a vertical box, containing:
   1. the menu [menubar]
   2. an horizontal box [hb]
 *)

let vbox = GPack.vbox ~packing:main_window#add ()

let menubar = GMenu.menu_bar
  ~packing:(vbox#pack ?from:None ?expand:None ?fill:None ?padding:None)
  ()

let hb = GPack.hbox ~packing:vbox#add ()

let accel_group = GtkData.AccelGroup.create ()

(* context_tools : simplified tools menu for mouse-3 *)

let context_tools_menu = GMenu.menu ()

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

(** {2 view for the session tree} *)
let scrolled_session_view =
  let sv =
    GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~shadow_type:`ETCHED_OUT
      ~packing:hp#add ()
  in
  hp#set_position gconfig.tree_width;
  let (_ : GtkSignal.id) =
    sv#misc#connect#size_allocate
      ~callback:
      (fun {Gtk.width=w;Gtk.height=_h} ->
       gconfig.tree_width <- w)
  in sv

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

let column_status_title = "Status"
let column_time_title = "Time"
let column_goals_title = "Theories/Goals"

(* first view column: icon and name *)
let view_name_column =
  let v = GTree.view_column ~title:column_goals_title () in
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
  let v = GTree.view_column ~title:column_status_title
                            ~renderer:(status_renderer, ["pixbuf", status_column])
                            ()
  in
  v#set_resizable false;
  v#set_visible true;
  v

let view_time_column =
  let renderer = GTree.cell_renderer_text [`XALIGN 0.] in
  let v = GTree.view_column ~title:column_time_title
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

let get_node_obs id = get_obs (get_node_id_pa id)
let get_node_proof_attempt id = get_proof_attempt (get_node_id_pa id)

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

(* vpan222 contains:
   2.2.2.1 a notebook containing view of the current task, source code etc
   2.2.2.2 a vertical pan which contains [vbox2222]
     2.2.2.2.1 the input field to type commands
     2.2.2.2.2 a scrolled window to hold the output of the commands
 *)

(*
  2.2.2.2 a vertical pan which contains [vbox2222]
    2.2.2.2.1 the input field to type commands [hbox22221]
    2.2.2.2.2 a scrolled window to hold the output of the commands [message_zone]
*)
let vbox2222 = GPack.vbox  ()

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

let command_entry =
  GEdit.entry
    ~text:"type commands here"
    ~packing:hbox22221#add ()

(* Part 2.2.2.2.2 contains messages returned by the IDE/server *)
let messages_notebook = GPack.notebook ~packing:vbox2222#add ()

let error_page,error_view =
  let label = GMisc.label ~text:"Messages" () in
  0, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(messages_notebook#append_page ~tab_label:label#coerce w)) ()

let log_view =
  let label = GMisc.label ~text:"Log" () in
  GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(messages_notebook#append_page ~tab_label:label#coerce w)) ()

(* tab 3: edited proof *)
let edited_tab =
  let label = GMisc.label ~text:"Edited proof" () in
  GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(messages_notebook#append_page ~tab_label:label#coerce w)) ()

let scrolled_edited_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT ~packing:edited_tab#add ()

let edited_view =
  GSourceView.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_edited_view#add
    ()

(* tab 4: prover output *)
let output_tab =
  let label = GMisc.label ~text:"Prover output" () in
  GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(messages_notebook#append_page ~tab_label:label#coerce w)) ()

let scrolled_output_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT ~packing:output_tab#add ()

let output_view =
  GSourceView.source_view
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
  GSourceView.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_counterexample_view#add
    ()

(* Allow colors locations on counterexample view *)
let () = create_colors gconfig counterexample_view

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
let create_msg_zone_error_tag () =
  message_zone#buffer#create_tag
    ~name:"error_tag_msg_zone" [`BACKGROUND gconfig.error_color_msg_zone_bg;
                                `FOREGROUND gconfig.error_color_msg_zone_fg]
let message_zone_error_tag = ref (create_msg_zone_error_tag ())

(**** Message-zone printing functions *****)

let add_to_log =
  let old = ref None in
  fun notif_kind s ->
  let (_,_,_,n) as x =
    match !old with
    | Some(line,oldnotif_kind,olds,oldn)
         when notif_kind = oldnotif_kind && s = olds ->
       let start = log_zone#buffer#get_iter (`LINE line) in
       let stop = log_zone#buffer#end_iter in
       log_zone#buffer#delete ~start ~stop;
       (line,oldnotif_kind,olds,oldn+1)
    | _ ->
       let line = log_zone#buffer#line_count in
       (line,notif_kind,s,1)
  in
  old := Some x;
  log_zone#buffer#insert ("["^ notif_kind);
  if n>1 then
    log_zone#buffer#insert (" (repeated " ^ (string_of_int n) ^ " times)");
  log_zone#buffer#insert ("] " ^ s ^ "\n");
  (* scroll to end of text. Since Gtk3 we must do it in idle() because
     of the "smooth scrolling". *)
  when_idle (fun () -> log_zone#scroll_to_mark `INSERT)

let clear_message_zone () =
  let buf = message_zone#buffer in
  buf#remove_tag_by_name "error_tag_msg_zone" ~start:buf#start_iter ~stop:buf#end_iter;
  buf#delete ~start:buf#start_iter ~stop:buf#end_iter

(* Function used to print stuff on the message_zone *)
let print_message ~kind ~notif_kind fmt =
  Format.kasprintf (fun s ->
              let s = try_convert s in
              add_to_log notif_kind s;
              let buf = message_zone#buffer in
              if kind>0 then
                begin
                  if Strings.ends_with notif_kind "error" ||
                     Strings.ends_with notif_kind "Error"
                  then
                    buf#insert ~tags:[!message_zone_error_tag] (s ^ "\n")
                  else
                    buf#insert (s ^ "\n");
                  messages_notebook#goto_page error_page;
                end)
    fmt

let display_warnings fmt warnings =
  let nwarn = ref 0 in
  try
    Queue.iter (fun (loc,msg) ->
      if !nwarn = 4 then begin
        Format.fprintf fmt "[%d more warnings. See stderr for details]@\n" (Queue.length warnings - !nwarn);
        raise Exit
      end;
      incr nwarn;
      match loc with
      | None ->
        Format.fprintf fmt "%s@\n@\n" msg
      | Some l ->
        (* scroll_to_loc ~color:error_tag ~yalign:0.5 loc; *)
        Format.fprintf fmt "%a: %s@\n@\n" Loc.gen_report_position l msg
    ) warnings;
  with Exit -> ()

let display_warnings () =
  if Queue.is_empty warnings then ()
  else begin
    print_message ~kind:1 ~notif_kind:"warning" "%a" display_warnings warnings;
    Queue.clear warnings;
  end

let print_message ~kind ~notif_kind fmt =
  display_warnings (); print_message ~kind ~notif_kind fmt

(***********************************)
(*    notebook on the top 2.2.2.1  *)
(***********************************)

(* notebook is composed of a Task page and several source files pages *)
let notebook = GPack.notebook ~packing:(vpan222#pack1 ~resize:true ~shrink:true) ()

(* Pack vbox2222 after packing the notebook (for vertical order) *)
let () = vpan222#pack2 ~resize:false ~shrink:true vbox2222#coerce

let (_ : GtkSignal.id) =
  vpan222#set_position gconfig.task_height;
  notebook#misc#connect#size_allocate
    ~callback:
    (fun {Gtk.width=_w;Gtk.height=h} ->
       gconfig.task_height <- h)

(********************************)
(* Task view (part of notebook) *)
(********************************)

let scrolled_task_view =
  let label = GMisc.label ~text:"Task" () in
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:(fun w -> ignore(notebook#append_page ~tab_label:label#coerce w))
    ()

let task_view =
  GSourceView.source_view
    ~editable:false
    ~cursor_visible:true
    ~show_line_numbers:true
    ~packing:scrolled_task_view#add
    ()

let () = create_colors gconfig task_view

let change_lang view lang =
  let lang =
    match lang with
    | "python" -> why3py_lang
    | "micro-C" -> why3c_lang
    | _ -> why_lang in
  view#source_buffer#set_language lang

(* Create an eventbox for the title label of the notebook tab *)
let create_eventbox ~read_only file =
  let eventbox = GBin.event_box () in
  let right_click_label_menu = GMenu.menu () in
  (* Create a menu for this eventbox *)
  let () =
    let close_item = GMenu.menu_item ~label:"close" () in
    if read_only then
      let (_: GtkSignal.id) = close_item#connect#activate
          ~callback:(fun () ->
              match Hstr.find source_view_table file with
              | exception Not_found ->
                  print_message ~kind:1 ~notif_kind:"ide_error"
                    "Error of the graphic interface: cannot find %s" file
              | (page_number, _, _)  ->
                  notebook#remove_page page_number;
                  Hstr.remove source_view_table file) in
      right_click_label_menu#append close_item in
  (* Connect the menu in the eventbox *)
  let (_: GtkSignal.id) =
    eventbox#event#connect#button_press ~callback:(fun v ->
        let n = GdkEvent.Button.button v in
        if n = 3 then
          right_click_label_menu#popup ~button:3 ~time:(GdkEvent.Button.time v);
        false (* Allow other handlers *)
      ) in
  eventbox

(* Create a page with tabname [f] and buffer equal to [content] in the
   notebook. Also add a corresponding page in source_view_table. *)
let create_source_view ~read_only f content f_format =
  let markup_read_only txt =
    "<span font-style=\"italic\">" ^ txt ^
    "</span> <span font-weight=\"bold\">(read-only)</span>" in

  if not (Hstr.mem source_view_table f) then
    begin
      let fl = Filename.basename f in
      let markup_fl = if read_only then markup_read_only fl else fl in
      let eventbox = create_eventbox ~read_only f in
      let label = GMisc.label ~packing:(fun w -> eventbox#add w)
          ~markup:markup_fl () in
      label#misc#set_tooltip_markup f;
      (* let source_page = !n in*)
      let scrolled_source_view =
        GBin.scrolled_window
          ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
          ~shadow_type:`ETCHED_OUT
          (*    ~packing:scrolled_source_view#add*)
          () in
      let source_page = notebook#append_page ~tab_label:eventbox#coerce
          scrolled_source_view#coerce in
      let editable = gconfig.allow_source_editing && (not read_only) in
      let source_view =
        GSourceView.source_view
          ~auto_indent:editable
          ~insert_spaces_instead_of_tabs:true ~tab_width:2
          ~show_line_numbers:true
          (* ~right_margin_position:80 ~show_right_margin:true *)
          (* ~smart_home_end:true *)
          ~editable:editable
          ~packing:scrolled_source_view#add
          () in
      Hstr.add source_view_table f (source_page, source_view, label);
      source_view#source_buffer#begin_not_undoable_action ();
      source_view#source_buffer#set_text content;
      source_view#source_buffer#end_not_undoable_action ();
      source_view#source_buffer#set_modified false;
      (* At initialization, file has not changed. When it changes, changes the
         name of the tab and update has_changed boolean. *)
      let (_: GtkSignal.id) = source_view#source_buffer#connect#modified_changed
          ~callback:(fun () ->
              try
                let _source_page, source_view, label =
                  Hstr.find source_view_table f in
                if not read_only then
                  if source_view#source_buffer#modified then
                    update_label_change label
                  else
                    update_label_saved label
              with Not_found -> () ) in
      Gconfig.add_modifiable_mono_font_view source_view#misc;
      change_lang source_view f_format;
      (* We have to create the tags for background colors for each view.
         They are not reusable from the other views.  *)
      create_colors gconfig source_view;
      Gconfig.set_fonts ();
      (* Focusing on the tabs that was just added *)
      notebook#goto_page source_page
    end

(* This returns the source_view of a file *)
let get_source_view (file: string) : GSourceView.source_view =
  if file = "Task" then task_view else
  match Hstr.find source_view_table file with
  | (_, v, _) -> v
  | exception Not_found -> raise (Nosourceview file)


(* End of notebook *)

(**** Monitor *****)

let fan =
  let s = Bytes.of_string "\226\150\129" in
  let c = Char.code (Bytes.get s 2) in
  let a = Array.init 8 (fun i ->
    Bytes.set s 2 (Char.chr (c + i));
    Bytes.to_string s) in
  fun n ->
  let n = n mod 14 in
  let n = if n < 0 then n + 14 else n in
  let n = if n >= 8 then 14 - n else n in
  a.(n)

let update_monitor =
  let c = ref 0 in
  fun t s r ->
  incr c;
  let f = if r = 0 then " " else fan !c in
  let text = Printf.sprintf "%s %d/%d/%d" f t s r in
  monitor#set_text text

(**********************)
(* Cursor positioning *)
(**********************)

(* Current position in the source files *)
let current_cursor_loc = ref None

let move_to_line ?(character=0) ~yalign (v : GSourceView.source_view) line =
  let line = max 0 (line - 1) in
  let line = min line v#buffer#line_count in
  (* Warning : Do not use LINECHAR here as it fails when there is not enough
     char on the line. *)
  let it = v#buffer#get_iter (`LINE line) in
  let it = it#forward_chars character in
  v#buffer#place_cursor ~where:it;
  let mark = `MARK (v#buffer#create_mark it) in
  (* Make the left side of the code always visible *)
  let xalign = 1.0 in
  v#scroll_to_mark ~use_align:true ~yalign ~xalign mark

(* Scroll to a specific locations *)
let scroll_to_loc ~force_tab_switch loc_of_goal =
  match loc_of_goal with
  | None -> ()
  | Some loc ->
    let f, l, e, _ = Loc.get loc in
    try
      let (n, v) = if f = "Task" then (0, task_view) else
          let (n, v, _) = get_source_view_table f in
          (n, v) in
      if force_tab_switch then
        begin
          Debug.dprintf debug "tab switch to page %d@." n;
          notebook#goto_page n;
        end;
      when_idle (fun () ->
          (* 0.5 to focus on the middle of the screen *)
          move_to_line ~character:e ~yalign:0.5 v l)
    with Nosourceview f ->
      Debug.dprintf debug "scroll_to_loc: no source know for file %s@." f

let scroll_to_loc_ce loc_of_goal =
  match loc_of_goal with
  | None -> ()
  | Some loc ->
      let _, l, _, _= Loc.get loc in
      (* 0.5 to focus on the middle of the screen *)
      when_idle (fun () -> move_to_line ~yalign:0.5 counterexample_view l)

(* Reposition the cursor to the place it was saved *)
let reposition_ide_cursor () =
  scroll_to_loc ~force_tab_switch:false !current_cursor_loc

let find_current_file_view () =
  let n = notebook#current_page in
  if n = 0 then Some ("Task", task_view) else
    let acc = ref None in
    Hstr.iter (fun k (x, v, _) -> if x = n then acc := Some (k, v)) source_view_table;
    !acc

(* Save the current location of the cursor to be reused after reload *)
let save_cursor_loc cursor_ref =
  let cur_fv = find_current_file_view () in
  match cur_fv with
  | None -> ()
  | Some (cur_file, view) ->
    (* Get current line *)
    let line = (view#buffer#get_iter_at_mark `INSERT)#line + 1 in
    cursor_ref := Some (Loc.user_position cur_file line 0 0)

(******************)
(* Reload actions *)
(******************)

let reload_unsafe () =
  save_cursor_loc current_cursor_loc; clear_message_zone ();
  send_request Reload_req

let save_and_reload () = save_sources (); reload_unsafe ()

(****************************)
(* command entry completion *)
(****************************)

let completion_cols = new GTree.column_list
let completion_col = completion_cols#add Gobject.Data.string
let completion_desc = completion_cols#add Gobject.Data.string
let completion_model = GTree.tree_store completion_cols

let command_entry_completion : GEdit.entry_completion =
  GEdit.entry_completion ~model:completion_model ~minimum_key_length:2 ~entry:command_entry ()

let add_completion_entry (s,desc) =
  let row = completion_model#append () in
  completion_model#set ~row ~column:completion_col s;
  completion_model#set ~row ~column:completion_desc desc

let match_function s iter =
  let candidate = completion_model#get ~row:iter ~column:completion_col in
  try
    ignore (Re.Str.search_forward (Re.Str.regexp_string_case_fold s) candidate 0);
    true
  with Not_found -> false

(* see also init_completion below *)

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
      | k when k = GdkKeysyms._Escape ->
        goals_view#misc#grab_focus ();
        true
      | _ -> false
      )

let () = send_session_config_to_server ()

(********************)
(* Locations colors *)
(********************)

let convert_color (color: color): string =
  match color with
  | Neg_premise_color -> "neg_premise_tag"
  | Premise_color     -> "premise_tag"
  | Goal_color        -> "goal_tag"
  | Error_color       -> "error_tag"
  | Error_line_color  -> "error_line_tag"
  | Error_font_color  -> "error_font_tag"
  | Search_color      -> "search_tag"

let color_line ~color loc =
  let color_line (v:GSourceView.source_view) ~color l =
    let buf = v#buffer in
    let top = buf#start_iter in
    let start = top#forward_lines (l-1) in
    let stop = start#forward_lines 1 in
    buf#apply_tag_by_name ~start ~stop color
  in

  let f, l, _, _ = Loc.get loc in
  try
    let v = get_source_view f in
    let color = convert_color color in
    color_line ~color v l
  with
  | Nosourceview f ->
    (* If the file is not present do nothing *)
    print_message ~kind:0 ~notif_kind:"color_loc" "No source view for file %s" f;
    Debug.dprintf debug "color_loc: no source view for file %s@." f

(* Add a color tag on the right locations on the correct file.
   If the file was not open yet, nothing is done *)
let color_loc ?(ce=false) ~color loc =

  (* This apply a background [color] on a location given by its file view [v] line
     [l] beginning char [b] and end char [e]. *)
  let color_loc (v:GSourceView.source_view) ~color l b e =
    let buf = v#buffer in
    let top = buf#start_iter in
    let start = top#forward_lines (l-1) in
    let start = start#forward_chars b in
    let stop = start#forward_chars (e-b) in
    buf#apply_tag_by_name ~start ~stop color
  in

  let f, l, b, e = Loc.get loc in
  try
    let v = if ce then counterexample_view else get_source_view f in
    let color = convert_color color in
    color_loc ~color v l b e
  with
  | Nosourceview f ->
      (* If the file is not present do nothing *)
     print_message ~kind:0 ~notif_kind:"color_loc" "No source view for file %s" f;
     Debug.dprintf debug "color_loc: no source view for file %s@." f

(* Erase the colors and apply the colors given by l (which come from the task)
   to appropriate source files *)
let apply_loc_on_source (l: (Loc.position * color) list) loc_goal =
  erase_loc_all_view ();
  List.iter (fun (loc, color) -> color_loc ~color loc) l;
  scroll_to_loc ~force_tab_switch:false loc_goal

(* Erase the colors and apply the colors given by l (which come from the task)
   to the counterexample tab *)
let apply_loc_on_ce (l: (Loc.position * color) list) =
  erase_color_loc counterexample_view;
  List.iter (fun (loc, color) -> color_loc ~ce:true ~color loc) l

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
  Gconfig.add_modifiable_sans_font_view goals_view#misc;
  Gconfig.add_modifiable_mono_font_view monitor#misc;
  Gconfig.add_modifiable_mono_font_view task_view#misc;
  Gconfig.add_modifiable_mono_font_view edited_view#misc;
  Gconfig.add_modifiable_mono_font_view output_view#misc;
  Gconfig.add_modifiable_mono_font_view counterexample_view#misc;
  Gconfig.add_modifiable_mono_font_view command_entry#misc;
  Gconfig.add_modifiable_mono_font_view message_zone#misc;
  task_view#source_buffer#set_language why_lang;
  counterexample_view#source_buffer#set_language why_lang;
  Gconfig.set_fonts ()




(******************)
(*    actions     *)
(******************)

let get_selected_row_references () =
  List.map
    (fun path -> goals_model#get_row_reference path)
    goals_view#selection#get_selected_rows

(**********************)
(* Contextual actions *)
(**********************)

(* goals_view#selection#select_iter only changes the selection for the selection
   tree, it should also change the cursor of the goal_view. The reason is that
   the cursor is used for arrow keys moves (not the selected row). *)
let select_iter iter =
  goals_view#selection#select_iter iter;
  let path = goals_model#get_path iter in
  goals_view#set_cursor path view_name_column


let expand_row () =
  let rows = get_selected_row_references () in
  match rows with
  | [row] ->
      let path = goals_model#get_path row#iter in
      goals_view#expand_row path ~all:(goals_view#row_expanded path)
  | _ -> ()

let collapse_row () =
  let rows = get_selected_row_references () in
  match rows with
  | [row] ->
      let path = goals_model#get_path row#iter in
      goals_view#collapse_row path
  | _ -> ()

let move_current_row_selection_to_parent () =
  let rows = get_selected_row_references () in
  match rows with
  | [row] ->
      begin
        goals_view#selection#unselect_all ();
        match goals_model#iter_parent row#iter with
        | None -> ()
        | Some iter ->
            select_iter iter
      end
  | _ -> ()

let move_current_row_selection_to_first_child () =
  let rows = get_selected_row_references () in
  match rows with
  | [row] ->
      let n = goals_model#iter_n_children (Some row#iter) in
      if n = 0 then
        ()
      else
        begin
          goals_view#selection#unselect_all ();
          let iter = goals_model#iter_children ?nth:(Some 0) (Some row#iter) in
          select_iter iter
        end
  | _ -> ()

let move_current_row_selection_to_down () =
  let rows = get_selected_row_references () in
  match rows with
  | [row] ->
      let path = goals_model#get_path row#iter in
      GtkTree.TreePath.down path;
      goals_view#selection#unselect_all ();
      goals_view#selection#select_path path;
      goals_view#set_cursor path view_name_column
  | _ -> ()

let move_current_row_selection_to_next () =
  let rows = get_selected_row_references () in
  match rows with
  | [row] ->
      let path = goals_model#get_path row#iter in
      GtkTree.TreePath.next path;
      goals_view#selection#unselect_all ();
      goals_view#selection#select_path path;
      goals_view#set_cursor path view_name_column
  | _ -> ()

let move_to_next_unproven_node_id strat =
  let rows = get_selected_row_references () in
  match rows with
  | [row] ->
      let row_id = get_node_id row#iter in
      manual_next := Some row_id;
      send_request (Get_first_unproven_node (strat, row_id))
  | _ -> ()

(* unused
let rec update_status_column_from_iter cont iter =
  set_status_column iter;
  match goals_model#iter_parent iter with
  | Some p -> update_status_column_from_iter cont p
  | None -> ()
*)

let clear_command_entry () = command_entry#set_text ""

let ide_command_list =
  ["up", "Select the parent of the current node";
   "down", "Select the first child of the current node";
   "next", "Select the \"next\" unproved node";
   "expand", "Expand the node";
   "ex_all", "Expand the node recursively";
   "collapse", "Collapse the node";
   "list_ide_command", "show this help text"]

let ide_command cmd =
  List.exists (fun x -> fst x = cmd) ide_command_list

let interp_ide cmd =
  match cmd with
  | "up" ->
      move_current_row_selection_to_parent ()
  | "down" ->
      move_current_row_selection_to_first_child ()
  | "next" ->
      move_to_next_unproven_node_id Clever
  | "expand" ->
      expand_row ()
  | "collapse" ->
      collapse_row ()
  | "list_ide_command" ->
      let s = List.fold_left (fun acc x -> (fst x) ^ ": " ^
                              (snd x) ^ "\n" ^ acc) "" ide_command_list in
      clear_command_entry ();
      print_message ~kind:1 ~notif_kind:"Info" "%s" s
  | _ ->
      clear_command_entry ();
      print_message ~kind:1 ~notif_kind:"error" "Error: %s\nPlease report." cmd

let interp cmd =
  (* TODO: do some preprocessing for queries, or leave everything to server ? *)
  message_zone#buffer#set_text "";
  clear_command_entry ();
  if ide_command cmd then
    interp_ide cmd
  else
    begin
      let rows = get_selected_row_references () in
      let ids =
        match rows with
        | [] -> [root_node]
        | _ -> List.map (fun n -> get_node_id n#iter) rows
      in
      List.iter (fun id -> send_request (Command_req (id, cmd))) ids;
      (* clear previous error message if any *)
    end

let (_ : GtkSignal.id) =
  let callback () =
    let cmd = command_entry#text in
    match cmd with
    | ""     -> goals_view#misc#grab_focus ()
    | _ ->
      begin
        add_command list_commands cmd;
        interp cmd
      end in
  command_entry#connect#activate ~callback

(* remove the helper text from the command entry the first time it gets the focus *)
let () =
  let id = ref None in
  let callback _ =
    clear_command_entry ();
    GtkSignal.disconnect command_entry#as_entry (Opt.get !id);
    false in
  id := Some (command_entry#event#connect#focus_in ~callback)

let on_selected_row r =
  try
    let id = get_node_id r#iter in
    let typ = get_node_type id in
    match typ with
    | NGoal ->
        let c = gconfig.show_full_context in
        send_request (Get_task(id,c,true))
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
         | Controller_itp.Removed _p -> "removed proof attempt"
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
       counterexample_view#scroll_to_mark `INSERT;
       let c = gconfig.show_full_context in
       send_request (Get_task(id,c,true))
    | _ ->
       let c = gconfig.show_full_context in
       send_request (Get_task(id,c,true))
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
      | 3 -> (* Right click *)
        let sel = goals_view#selection in
        let x = int_of_float (GdkEvent.Button.x ev) in
        let y = int_of_float (GdkEvent.Button.y ev) in
        begin match goals_view#get_path_at_pos ~x ~y with
        | Some (path,_,_,_) when not (sel#path_is_selected path) ->
          sel#unselect_all ();
          sel#select_path path
        | _ -> ()
        end;
        context_tools_menu#popup ~button:3 ~time:(GdkEvent.Button.time ev);
        true
      | 1 -> (* Left click *)
          (* Call get-ce only when clicked on the Status of a proofattempt
             (which is unproved) *)
          let x = int_of_float (GdkEvent.Button.x ev) in
          let y = int_of_float (GdkEvent.Button.y ev) in
          begin match goals_view#get_path_at_pos ~x ~y with
            | Some (path,col,_,_) ->
                if col#title = column_status_title then
                  let node_id =
                    get_node_id (goals_model#get_row_reference path)#iter in
                  let type_id = get_node_type node_id in
                  let proved_id = get_node_proved node_id in
                  if type_id = NProofAttempt && not proved_id then
                    send_request (Command_req (node_id, "get-ce"))
            | _ -> ()
          end;
          false
      | _ -> (* Other buttons *) false
    end
  in
  goals_view#event#connect#button_press ~callback

let (_ : GtkSignal.id) =
  let callback ev =
    match GdkEvent.Key.keyval ev with
    | k when k = GdkKeysyms._Return ->
      command_entry#misc#grab_focus ();
      true
    | _ -> false
  in
  goals_view#event#connect#key_press ~callback

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

(*************************)
(* Notification Handling *)
(*************************)

let treat_message_notification msg = match msg with
  (* TODO: do something ! *)
  | Proof_error (_id, s)                        ->
     print_message ~kind:1 ~notif_kind:"Proof_error" "%s" s
  | Transf_error (true, _id, tr_name, _arg, _loc, msg, _doc) ->
      (* When the error reported by the transformation is fatal, we notify the
         user with a popup. *)
      let msg = Format.sprintf "Please report:\nTransformation %s failed: \n%s\n" tr_name msg in
      GToolbox.message_box ~title:"Why3 fatal error" msg
  | Transf_error (false, _id, tr_name, arg, loc, msg, doc) ->
      if arg = "" then
        print_message ~kind:1 ~notif_kind:"Transformation Error"
                      "%s\nTransformation failed: \n%s\n\n%s" msg tr_name doc
      else
        begin
          let buf = message_zone#buffer in
          print_message ~kind:1 ~notif_kind:"Transformation Error"
                        "%s\nTransformation failed. \nOn argument: \n%s \n%s\n\n%s"
            tr_name arg msg doc;
          (* remove all coloration in message_zone before coloring *)
          buf#remove_tag_by_name "error_tag" ~start:buf#start_iter ~stop:buf#end_iter;
          let color = "error_tag" in
          let _, _, beg_char, end_char = Loc.get loc in
          let start = buf#start_iter#forward_lines 3 in
          buf#apply_tag_by_name
            ~start:(start#forward_chars beg_char)
            ~stop:(start#forward_chars end_char)
            color
        end
  | Strat_error (_id, s) ->
     print_message ~kind:1 ~notif_kind:"Strat_error" "%s" s
  | Replay_Info s ->
     print_message ~kind:0 ~notif_kind:"Replay_info" "%s" s
  | Query_Info (_id, s) ->
     print_message ~kind:1 ~notif_kind:"Query_info" "%s" s
  | Query_Error (_id, s) ->
     print_message ~kind:1 ~notif_kind:"Query_error" "%s" s
  | Information s ->
     print_message ~kind:1 ~notif_kind:"Information" "%s" s
  | Task_Monitor (t, s, r) -> update_monitor t s r
  | Open_File_Error s ->
     print_message ~kind:0 ~notif_kind:"Open_File_Error" "%s" s
  | Parse_Or_Type_Error (loc, _rel_loc, s) ->
     if gconfig.allow_source_editing || !initialization_complete then
       begin
         scroll_to_loc ~force_tab_switch:true (Some loc);
         color_line ~color:Error_line_color loc;
         color_loc ~color:Error_color loc;
         color_loc ~color:Error_font_color loc;
         print_message ~kind:1 ~notif_kind:"Parse_Or_Type_Error" "%s" s
       end
     else
       begin
         Format.eprintf "%a: %s@." Loc.gen_report_position loc s;
         exit 1
       end

  | File_Saved f                 ->
    begin
      try
        let (_source_page, source_view, _) = Hstr.find source_view_table f in
        source_view#source_buffer#set_modified false;
        print_message ~kind:1 ~notif_kind:"File_Saved" "%s was saved" f
      with
      | Not_found                ->
          print_message ~kind:1 ~notif_kind:"File_Saved"
                        "Please report: %s was not found in IDE but was saved in session" f
    end
  | Error s                      ->
     print_message ~kind:1 ~notif_kind:"General request failure" "%s" s


let is_selected_alone id =
  match get_selected_row_references () with
  | [r] -> let i = get_node_id r#iter in i = id
  | _ -> false



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
  | Controller_itp.Removed _p -> !image_undone (* TODO !image_removed *)
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
        | C.Removed _ -> "(removed prover)"
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

let on_selected_rows ~multiple ~notif_kind ~action f () =
  match get_selected_row_references () with
  | [] ->
    print_message ~kind:1 ~notif_kind
      "Select at least one node to perform the '%s' action" action
  | _ :: _ :: _ when not multiple ->
    print_message ~kind:1 ~notif_kind
      "Select at most one node to perform the '%s' action" action
  | l ->
    List.iter (fun r -> send_request (f (get_node_id r#iter))) l

(**************************)
(* Helpers for menu items *)
(**************************)

let remove_mnemonic s =
  try
    let j = ref (String.index s '_') in
    let i = ref 0 in
    let n = String.length s in
    let b = Buffer.create n in
    try
      while true do
        Buffer.add_substring b s !i (!j - !i);
        i := !j + 1;
        if !i = n then raise Not_found;
        Buffer.add_char b s.[!i];
        incr i;
        j := String.index_from s !i '_';
      done;
      assert false
    with Not_found ->
      Buffer.add_substring b s !i (n - !i);
      Buffer.contents b
  with Not_found -> s

class menu_factory ~accel_path:menu_path ~accel_group:menu_group menu =
object (self)
  method add_item ?accel_path ?(accel_group=menu_group) ?modi ?key
    ?(use_mnemonic=true) ?(add_accel=true) ?tooltip ?callback label =
    let item = GtkMenu.MenuItem.create ~use_mnemonic ~label () in
    let item = new GMenu.menu_item item in
    item#misc#show ();
    menu#append item;
    if add_accel || accel_path <> None then begin
      let accel_path = match accel_path with
        | None -> menu_path ^ (if use_mnemonic then remove_mnemonic label else label)
        | Some ap -> ap in
      if add_accel then GtkData.AccelMap.add_entry accel_path ?key ?modi;
      GtkBase.Widget.set_accel_path item#as_widget accel_path accel_group
    end;
    Opt.iter (fun callback -> let _ = item#connect#activate ~callback in ()) callback;
    Opt.iter item#misc#set_tooltip_markup tooltip;
    item
  method add_separator () =
    let item = GtkMenu.MenuItem.separator_create () in
    let item = new GMenu.menu_item item in
    item#misc#show ();
    menu#append item;
    ()
  method add_submenu ?use_mnemonic label =
    let m = GtkMenu.Menu.create [] in
    let m = new GMenu.menu m in
    m#misc#show ();
    let item = self#add_item ?use_mnemonic ~add_accel:false label in
    item#set_submenu m;
    m
end

(*****************************************************************)
(* "Tools" submenus for strategies, provers, and transformations *)
(*****************************************************************)

let string_of_desc desc =
  let print_trans_desc fmt (x,r) =
    fprintf fmt "@[<hov 2>%s@\n%a@]" x Pp.formatted r
  in Glib.Markup.escape_text (Pp.string_of print_trans_desc desc)

let parse_shortcut_as_key s =
  let (key,modi) as r = GtkData.AccelGroup.parse s in
  begin if key = 0 then
    Debug.dprintf debug "Shortcut '%s' cannot be parsed as a key@." s
  else
    let name = GtkData.AccelGroup.name ~key ~modi in
    Debug.dprintf debug "Shortcut '%s' parsed as key '%s'@." s name
  end;
  r

let add_submenu_strategy (str_fac: menu_factory) (con_fac: menu_factory) (shortcut,strategy) =
  let callback () =
    Debug.dprintf debug "interp command '%s'@." strategy;
    interp strategy
  in
  let name = String.map (function '_' -> ' ' | c -> c) strategy in
  let tooltip = "run strategy " ^ strategy ^ " on selected goal" in
  let accel_path = "<Why3-Main>/Tools/Strategies/" ^ name in
  let (key, modi) = parse_shortcut_as_key shortcut in
  let (_ : GMenu.menu_item) = str_fac#add_item name
    ~use_mnemonic:false ~accel_path ~key ~modi ~tooltip ~callback in
  let (_ : GMenu.menu_item) = con_fac#add_item name
    ~use_mnemonic:false ~accel_path ~add_accel:false ~tooltip ~callback in
  ()

let hide_context_provers, add_submenu_prover =
  (* Set of context provers menu items *)
  let context_provers = Hstr.create 16 in
  (* After preferences for hidden provers are set, actualize provers allowed in
   the context_factory *)
  let hide_context_provers () =
    Hstr.iter (fun k i ->
      if List.mem k gconfig.hidden_provers then
        i#misc#hide ()
      else
        i#misc#show ()) context_provers in
  let add_submenu_prover (pro_fac: menu_factory) (con_fac: menu_factory)
    (shortcut,prover_name,prover_parseable_name) =
    let callback () =
      Debug.dprintf debug "interp command '%s'@." prover_parseable_name;
      interp prover_parseable_name
    in
    let tooltip = "run prover " ^ prover_name ^ " on selected goal" in
    let accel_path = "<Why3-Main>/Tools/Provers/" ^ prover_name in
    let (key,modi) = parse_shortcut_as_key shortcut in
    let (_ : GMenu.menu_item) = pro_fac#add_item prover_name
        ~use_mnemonic:false ~accel_path ~key ~modi ~tooltip ~callback in
    let (i : GMenu.menu_item) = con_fac#add_item prover_name
        ~use_mnemonic:false ~accel_path ~add_accel:false ~tooltip ~callback in
    Hstr.add context_provers prover_parseable_name i;
    if List.mem prover_parseable_name gconfig.hidden_provers then
      i#misc#hide() in
  hide_context_provers, add_submenu_prover

(*************)
(* Main menu *)
(*************)

(* Use the command key (⌘) for shortcuts when on mac *)
let primary_modifiers = snd (GtkData.AccelGroup.parse "<Primary>A")

let tools_accel_group = GtkData.AccelGroup.create ()
let factory = new menu_factory ~accel_path:"<Why3-Main>/" ~accel_group menubar
let context_factory = new menu_factory context_tools_menu
  ~accel_path:"" ~accel_group:tools_accel_group

let connect_menu_item i ~callback =
  let (_ : GtkSignal.id) = i#connect#activate ~callback in ()

(* "File" menu items *)

let file_menu = factory#add_submenu "_File"
let file_factory = new menu_factory file_menu ~accel_path:"<Why3-Main>/File/" ~accel_group

let (_: GMenu.menu_item) =
  file_factory#add_item "Add file to session"
    ~tooltip:"Insert another file in the current session"
    ~callback:(fun () ->
      select_file ~request:(fun f -> send_request (Add_file_req f)))

let (_: GMenu.menu_item) =
  let callback () =
    Gconfig.preferences ~parent:main_window gconfig;
    (* hide/show provers in contextual menu *)
    hide_context_provers ();
    (* Source view tags *)
    Opt.iter (fun (_, v) -> update_tags gconfig v) (find_current_file_view ());
    (* Update message zone tags *)
    remove_all_tags gconfig message_zone;
    message_zone_error_tag := create_msg_zone_error_tag ();
    make_sources_editable gconfig.allow_source_editing;
    send_session_config_to_server ()
  in
  file_factory#add_item "Preferences"
    ~tooltip:"Open Preferences Window"
    ~callback

let (_: GMenu.menu_item) =
  file_factory#add_item "Save session"
    ~tooltip:"Save the current proof session on disk"
    ~callback:(fun () -> send_request Save_req)

let (_: GMenu.menu_item) =
  file_factory#add_item "Save files"
    ~tooltip:"Save the edited source files on disk"
    ~callback:save_sources

let (_: GMenu.menu_item) =
  file_factory#add_item "_Save session and files"
    ~modi:primary_modifiers ~key:GdkKeysyms._S
    ~tooltip:"Save the current proof session and the source files"
    ~callback:(fun () -> save_sources(); send_request Save_req)

let (_: GMenu.menu_item) =
  file_factory#add_item "Save all and _Refresh session"
    ~modi:primary_modifiers ~key:GdkKeysyms._R
    ~tooltip:"Save the current proof session and the source files, then refresh the proof session with updated source files."
    ~callback:save_and_reload

let (_: GMenu.menu_item) =
  file_factory#add_item "_Quit"
    ~modi:primary_modifiers ~key:GdkKeysyms._Q
    ~tooltip:"See the Preferences for setting the policy on automatic file saving at exit."
    ~callback:exit_function_safe

(* Remove a specific color at a specific location *)
let uncolor ~color loc =
  match loc with
  | None -> ()
  | Some loc ->
      let f, l, b, e = Loc.get loc in
      try
        let v = get_source_view f in
        let color = convert_color color in
        let buf = v#buffer in
        let top = buf#start_iter in
        let start = top#forward_lines (l-1) in
        let start = start#forward_chars b in
        let stop = start#forward_chars (e-b) in
        buf#remove_tag_by_name ~start ~stop color;
      with
      | Nosourceview _ -> ()

let search_forward =
  let last_search = ref "" in
  let last_colored = ref None in
  let search_forward ~forward () =
    let cur_fv = find_current_file_view () in
    match cur_fv with
    | None -> print_message ~kind:0 ~notif_kind:"Search"
                "Cannot search. No current file view exist"
    | Some (cur_file, view) ->
        (* Get current line *)
        let iter = view#buffer#get_iter_at_mark `SEL_BOUND in
        let search_string =
          let find = if forward then "Forward search" else "Backward search" in
          GToolbox.input_string ~title:find ~ok:"Search"
            ~cancel:"Cancel" ~text:!last_search
            "Type a string to find in the current document"
        in
        match search_string with
        | None -> uncolor ~color:Search_color !last_colored
        | Some search ->
            last_search := search;
            let searched =
              if forward then
                GtkText.Iter.forward_search iter#as_iter search None
              else
                GtkText.Iter.backward_search iter#as_iter search None
            in
            match searched with
            | None ->
                uncolor ~color:Search_color !last_colored;
                print_message ~kind:1 ~notif_kind:"Search"
                        "Searched string not found in the rest of the document"
            | Some (iter_begin, iter_end) ->
                let n1 = GtkText.Iter.get_line iter_begin in
                let l1 = GtkText.Iter.get_line_index iter_begin in
                let l2 = GtkText.Iter.get_line_index iter_end in
                let loc1 = Loc.user_position cur_file (n1 + 1) l1 l2 in
                color_loc ~color:Search_color loc1;
                if not (Opt.equal Loc.equal !last_colored (Some loc1)) then
                  uncolor ~color:Search_color !last_colored;
                last_colored := Some loc1;
                (* Get to the line after to be able to call Ctrl+F on the same
                   string right away *)
                let loc2 = if forward then
                    Loc.user_position cur_file (n1 + 1) l2 l2
                  else
                    Loc.user_position cur_file (n1 + 1) l1 l1
                in
                scroll_to_loc ~force_tab_switch:false (Some loc2);
  in
  search_forward

let edit_menu = factory#add_submenu "_Edit"
let edit_factory = new menu_factory edit_menu ~accel_path:"<Why3-Main>/Edit/" ~accel_group

let (_: GMenu.menu_item) =
  edit_factory#add_item "Search forward"
    ~modi:primary_modifiers ~key:GdkKeysyms._F
    ~tooltip:"Search in the source file."
    ~callback:(search_forward ~forward:true)

let (_: GMenu.menu_item) =
  edit_factory#add_item "Search backward"
    ~modi:primary_modifiers ~key:GdkKeysyms._B
    ~tooltip:"Search backward in the source file."
    ~callback:(search_forward ~forward:false)

exception SearchLimit

(* Use a specific function to read words under cursor (for Ctrl+L) because GTK
   functions for forward_word_end/backward_word_start does not skip "_" in
   particular. *)
let get_word_around_iter iter =

  let is_letter c =
    match c with
    | '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' | '_' | '\'' -> true
    | _ -> false in

  let get_right_words (iter: GText.iter) =
    let rec get_words n start_iter =
      if n = 0 then raise SearchLimit; (* Forbid too long search *)
      let incr_iter = start_iter#forward_char in
      let s = start_iter#get_text ~stop:incr_iter in
      if not (is_letter s.[0]) then
        start_iter
      else
        get_words (n-1) incr_iter
    in
    get_words 80 iter in

  let get_left_words (iter: GText.iter) =
    let rec get_words n (end_iter: GText.iter) =
      if n = 0 then raise SearchLimit; (* Forbid too long search *)
      let incr_iter = end_iter#backward_char in
      let s = incr_iter#get_text ~stop:incr_iter#forward_char in
      if not (is_letter s.[0]) then
        incr_iter#forward_char
      else
        get_words (n-1) incr_iter
    in
    get_words 80 iter in

  let start_iter = get_left_words iter in
  let end_iter = get_right_words iter in
  let text = start_iter#get_text ~stop:end_iter in
  (start_iter, text, end_iter)

(* This function check for immediate quantification (not for scope yet) *)
let rec get_qualif acc start_iter =
  if start_iter#get_text ~stop:start_iter#forward_char = "." then
    let (start_iter, text, _) = get_word_around_iter start_iter#backward_char in
    if Strings.char_is_uppercase
        (start_iter#get_text ~stop:start_iter#forward_char).[0] then
      get_qualif (text :: acc) start_iter#backward_char
    else
      acc
  else
    acc

let get_module (iter: GText.iter) =
  match iter#backward_search "module" with
  | None -> print_message ~kind:1 ~notif_kind:"Error"
              "cannot find encapsulating module"; None
  | Some (_, end_iter) ->
      let (_, text, _) = get_word_around_iter end_iter#forward_char in
      Some text

(* find_cursor_ident: finds the ident under cursor and scroll to its definition
   get_back_loc: returns to the last position of a searched ident. *)
let find_cursor_ident, get_back_loc =
  let last_loc = ref None in
  (fun () ->
    save_cursor_loc last_loc;
    match find_current_file_view () with
    | None -> print_message ~notif_kind:"Ide_error" ~kind:1
                "Cannot determine current source file"
    | Some (file, view) ->
        try
          if file = "Task" then
            let iter = view#buffer#get_iter `SEL_BOUND in
            let (_, text, _) = get_word_around_iter iter in
            interp ("locate " ^ text)
          else
            let iter = view#buffer#get_iter `SEL_BOUND in
            let (start_iter, text, end_iter) = get_word_around_iter iter in
            if text = "" then
              ()
            else
              let l = start_iter#line + 1 in
              let b = start_iter#line_offset in
              let e = end_iter#line_offset in
              let f = file in
              let loc = Loc.user_position f l b e in
              send_request (Find_ident_req loc)
        with SearchLimit ->
          print_message ~notif_kind:"Ide_error" ~kind:1
            "Search limit overflow: the word is too long"
  ),
  (fun () -> scroll_to_loc ~force_tab_switch:true !last_loc)

let (_: GMenu.menu_item) =
  edit_factory#add_item "Find cursor ident"
    ~modi:primary_modifiers ~key:GdkKeysyms._L
    ~tooltip:"This finds the definition of the ident under user cursor"
    ~callback:find_cursor_ident

let (_: GMenu.menu_item) =
  edit_factory#add_item "Back"
    ~modi:primary_modifiers ~key:GdkKeysyms._ampersand (* & *)
    ~tooltip:"After find cursor ident, return back to cursor"
    ~callback:get_back_loc

(* "Tools" menu items *)

let tools_menu = factory#add_submenu "_Tools"
let tools_factory = new menu_factory tools_menu
  ~accel_path:"<Why3-Main>/Tools/" ~accel_group:tools_accel_group

let strategies_factory =
  let tools_submenu_strategies = tools_factory#add_submenu "Strategies" in
  tools_factory#add_separator ();
  new menu_factory tools_submenu_strategies
    ~accel_path:"<Why3-Main>/Tools/Strategies/" ~accel_group:tools_accel_group

let provers_factory =
  let tools_submenu_provers = tools_factory#add_submenu "Provers" in
  tools_factory#add_separator ();
  new menu_factory tools_submenu_provers
    ~accel_path:"<Why3-Main>/Tools/Provers/" ~accel_group:tools_accel_group

(* "View" menu items *)

let view_menu = factory#add_submenu "_View"
let view_factory = new menu_factory ~accel_path:"<Why3-Main>/View/" ~accel_group view_menu

let (_ : GMenu.menu_item) =
  view_factory#add_item "Enlarge font"
    ~modi:primary_modifiers ~key:GdkKeysyms._plus
    ~callback:enlarge_fonts

let (_ : GMenu.menu_item) =
  view_factory#add_item "Reduce font"
    ~modi:primary_modifiers ~key:GdkKeysyms._minus
    ~callback:reduce_fonts

let (_: GMenu.menu_item) =
  view_factory#add_item "Collapse proved goals"
    ~accel_group:tools_accel_group ~key:GdkKeysyms._exclam
    ~tooltip:"Collapse all the proven nodes under the current node"
    ~callback:collapse_proven_goals

let (_: GMenu.menu_item) =
  view_factory#add_item "Expand all"
    ~tooltip:"Expand all nodes of the tree view"
    ~callback:goals_view#expand_all

let (_: GMenu.menu_item) =
  view_factory#add_item "Collapse current node"
    ~accel_group:tools_accel_group ~key:GdkKeysyms._minus
    ~callback:collapse_row

let (_: GMenu.menu_item) =
  view_factory#add_item "Expand current node"
    ~accel_group:tools_accel_group ~key:GdkKeysyms._plus
    ~tooltip:"Expand current node, or its children when already expanded"
    ~callback:expand_row

let (_: GMenu.menu_item) =
  view_factory#add_item "Go to parent node"
    ~modi:primary_modifiers ~key:GdkKeysyms._Left
    ~callback:move_current_row_selection_to_parent

let (_: GMenu.menu_item) =
  view_factory#add_item "Go to first child"
    ~callback:move_current_row_selection_to_first_child

let (_: GMenu.menu_item) =
  view_factory#add_item "Select next unproven goal"
    ~modi:primary_modifiers ~key:GdkKeysyms._Right
    ~callback:(fun () -> move_to_next_unproven_node_id Clever)

let (_: GMenu.menu_item) =
  view_factory#add_item "Go down (skipping proved goals)"
    ~modi:primary_modifiers ~key:GdkKeysyms._Down
    ~callback:(fun () -> move_to_next_unproven_node_id Next)

let (_: GMenu.menu_item) =
  view_factory#add_item "Go up (skipping proved goals)"
    ~modi:primary_modifiers ~key:GdkKeysyms._Up
    ~callback:(fun () -> move_to_next_unproven_node_id Prev)

(* "Help" menu items *)

let help_menu = factory#add_submenu "_Help"
let help_factory = new menu_factory help_menu ~accel_path:"<Why3-Main>/Help/" ~accel_group

let (_ : GMenu.menu_item) =
  help_factory#add_item
    "Legend"
    ~callback:(show_legend_window ~parent:main_window)

let (_ : GMenu.menu_item) =
  help_factory#add_item
    "About"
    ~callback:(show_about_window ~parent:main_window)

let init_completion provers transformations strategies commands =
  (* add the names of all the the transformations *)
  List.iter add_completion_entry transformations;
  (* add the name of the commands *)
  List.iter (fun s -> add_completion_entry (s,"command")) commands;
  (* todo: add queries *)

  (* add provers *)

  let all_strings =
    List.fold_left (fun acc (s,_,p) ->
                    Debug.dprintf debug "string for completion: '%s' '%s'@." s p;
                    let acc = (p,"prover") :: acc in
                    if s = "" then acc else (s,"shortcut for prover "^p) :: acc) [] provers
  in
  List.iter add_completion_entry all_strings;
  let provers_sorted =
    List.sort (fun (_,h1,_) (_,h2,_) ->
               String.compare (Strings.lowercase h1) (Strings.lowercase h2))
              provers
  in
  (* Remove counterexample provers from the menu *)
  let menu_provers =
    List.filter (fun (_, _, s) -> not (Strings.ends_with s "counterexamples"))
      provers_sorted in
  List.iter (add_submenu_prover provers_factory context_factory) menu_provers;
  context_factory#add_separator ();
  let all_strings =
    List.fold_left (fun acc (shortcut,strategy) ->
                    Debug.dprintf debug "string for completion: '%s' '%s'@." shortcut strategy;
                    let acc = (strategy, "strategy") :: acc in
                    if shortcut = "" then acc else
                      (shortcut, "shortcut for strategy "^strategy) :: acc)
                   [] strategies
  in
  List.iter add_completion_entry all_strings;
  List.iter (add_submenu_strategy strategies_factory context_factory) strategies;

  command_entry_completion#set_text_column completion_col;
  (* Adding a column which contains the description of the
     prover/transformation/strategy. *)
  let name_renderer = GTree.cell_renderer_text [ ] in
  name_renderer#set_properties [`BACKGROUND "lightgrey"];
  command_entry_completion#pack name_renderer;
  command_entry_completion#add_attribute name_renderer "text" completion_desc;

  command_entry_completion#set_match_func match_function;

  command_entry#set_completion command_entry_completion


let () =
  let transformations = Server_utils.list_transforms () in
  let add_submenu_transform name filter =
    let submenu = tools_factory#add_submenu name in
    let submenu = new menu_factory submenu
      ~accel_path:("<Why3-Main>/Tools/" ^ name ^ "/")
      ~accel_group:tools_accel_group in
    let iter ((name,_) as desc) =
      let (_ : GMenu.menu_item) = submenu#add_item (Glib.Markup.escape_text name)
        ~use_mnemonic:false
        ~tooltip:(string_of_desc desc)
        ~callback:(fun () -> interp name) in
      ()
    in
    let trans = List.filter filter transformations in
    List.iter iter trans
  in
  add_submenu_transform
    "Transformations (a-e)"
    (fun (x,_) -> x < "eliminate");
  add_submenu_transform
    "Transformations (eliminate)"
    (fun (x,_) -> x >= "eliminate" && x < "eliminatf");
  add_submenu_transform
    "Transformations (e-r)"
    (fun (x,_) -> x >= "eliminatf" && x < "s");
  add_submenu_transform "Transformations (s-z)"
                        (fun (x,_) -> x >= "s");
  tools_factory#add_separator ()

(* complete the tools menu *)

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Edit error" ~action:"edit"
      (fun id -> Command_req (id, "edit")) in
  tools_factory#add_item "_Edit"
    ~key:GdkKeysyms._E
    ~tooltip:"View or edit proof script"
    ~callback

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"get-ce error"
      ~action:"Get Counterexamples"
      (fun id -> Command_req (id, "get-ce")) in
  tools_factory#add_item "_Get Counterexamples"
    ~key:GdkKeysyms._G
    ~tooltip:"Launch the prover with counterexamples"
    ~callback

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Replay error" ~action:"replay"
      (fun id -> Command_req (id, "replay")) in
  tools_factory#add_item "_Replay valid obsolete proofs"
    ~key:GdkKeysyms._R
    ~tooltip:"Replay valid obsolete proofs under the current node"
    ~callback

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Replay error" ~action:"replay all"
      (fun id -> Command_req (id, "replay all")) in
  tools_factory#add_item "Replay all obsolete proofs"
    ~tooltip:"Replay all obsolete proofs under the current node"
    ~callback

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Clean error" ~action:"clean"
      (fun id -> Command_req (id, "clean")) in
  tools_factory#add_item "_Clean node"
    ~key:GdkKeysyms._C
    ~tooltip:"Remove unsuccessful proofs or transformations that are under a proved goal"
    ~callback

let (_ : GMenu.menu_item) =
  (* This is considered risky command so it is intentionally not added to the
     context menu. It also trigger the apparition of a popup. *)
  let callback () =
    let answer =
      GToolbox.question_box
        ~default:2
        ~title:"Launching unsafe command"
        ~buttons:["Yes"; "No"]
        "Do you really want to remove all proofs from this session ?"
    in
      match answer with
      | 1 -> send_request Reset_proofs_req
      | _ -> ()
  in
  tools_factory#add_item "Reset proofs"
    ~tooltip:"Remove all proofs attempts or transformations"
    ~callback

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:true ~notif_kind:"Remove_subtree error" ~action:"remove"
      (fun id -> Remove_subtree id) in
  tools_factory#add_item "Remove node"
    ~key:GdkKeysyms._Delete
    ~tooltip:"Remove the selected proof attempts or transformations"
    ~callback

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:true ~notif_kind:"Mark_obsolete error" ~action:"mark obsolete"
      (fun id -> Command_req (id, "mark")) in
  tools_factory#add_item "Mark _obsolete"
    ~key:GdkKeysyms._O
    ~tooltip:"Mark all proof attempts under the current node as obsolete"
    ~callback

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:true ~notif_kind:"Interrupt error" ~action:"interrupt"
      (fun id -> Command_req (id, "interrupt")) in
  tools_factory#add_item "_Interrupt"
    ~tooltip:"Stop all running proof attempts"
    ~callback

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Bisect error" ~action:"bisect"
      (fun id -> Command_req (id, "bisect")) in
  tools_factory#add_item "_Bisect hypotheses"
    ~tooltip:"Remove useless hypotheses from a proved goal by bisection"
    ~callback

let () = tools_factory#add_separator ()

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Focus_req error" ~action:"focus"
      (fun id -> Command_req (id, "Focus")) in
  tools_factory#add_item "_Focus"
    ~tooltip:"Focus view on the current node"
    ~callback

let (_ : GMenu.menu_item) =
  let callback = fun () -> send_request (Unfocus_req) in
  tools_factory#add_item "_Unfocus"
    ~callback

let () = tools_factory#add_separator ()

let copy_item =
  tools_factory#add_item "Copy node"
    ~modi:primary_modifiers ~key:GdkKeysyms._C
    ~tooltip:"Copy the current node"

let paste_item =
  tools_factory#add_item "Paste node"
    ~modi:primary_modifiers ~key:GdkKeysyms._V
    ~tooltip:"Paste the copied node below the current node"

(* complete the contextual menu (but only after provers and strategies, hence the function) *)

let complete_context_menu () =
  context_factory#add_separator ();

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Edit error" ~action:"edit"
      (fun id -> Command_req (id, "edit")) in
  context_factory#add_item "_Edit"
    ~accel_path:"<Why3-Main>/Tools/Edit" ~add_accel:false
    ~tooltip:"View or edit proof script"
    ~callback
in ();

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"get-ce error"
      ~action:"Get Counterexamples"
      (fun id -> Command_req (id, "get-ce")) in
  context_factory#add_item "_Get Counterexamples"
    ~accel_path:"<Why3-Main>/Tools/Get Counterexamples" ~add_accel:false
    ~tooltip:"Launch the prover with counterexamples"
    ~callback
in ();

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Replay error" ~action:"replay"
      (fun id -> Command_req (id, "replay")) in
  context_factory#add_item "_Replay valid obsolete proofs"
    ~accel_path:"<Why3-Main>/Tools/Replay valid obsolete proofs" ~add_accel:false
    ~tooltip:"Replay valid obsolete proofs under the current node"
    ~callback
in ();

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Replay error" ~action:"replay all"
      (fun id -> Command_req (id, "replay all")) in
  context_factory#add_item "Replay all obsolete proofs"
    ~accel_path:"<Why3-Main>/Tools/Replay all obsolete proofs" ~add_accel:false
    ~tooltip:"Replay all obsolete proofs under the current node"
    ~callback
in ();

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:false ~notif_kind:"Clean error" ~action:"clean"
      (fun id -> Command_req (id, "clean")) in
  context_factory#add_item "_Clean node"
    ~accel_path:"<Why3-Main>/Tools/Clean node" ~add_accel:false
    ~tooltip:"Remove unsuccessful proofs or transformations that are under a proved goal"
    ~callback
in ();

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:true ~notif_kind:"Remove_subtree error" ~action:"remove"
      (fun id -> Remove_subtree id) in
  context_factory#add_item "Remove node"
    ~accel_path:"<Why3-Main>/Tools/Remove node" ~add_accel:false
    ~tooltip:"Remove the selected proof attempts or transformations"
    ~callback
in ();

let (_ : GMenu.menu_item) =
  let callback =
    on_selected_rows ~multiple:true ~notif_kind:"Interrupt error" ~action:"interrupt"
      (fun id -> Command_req (id, "interrupt")) in
  context_factory#add_item "_Interrupt"
    ~accel_path:"<Why3-Main>/Tools/Interrupt" ~add_accel:false
    ~tooltip:"Stop all running proof attempts"
    ~callback
in ()

(*************************************)
(* Copy paste                        *)
(*************************************)

(* Current copied node *)
let saved_copy = ref None

let copy () =
  match get_selected_row_references () with
  | [r] -> let n = get_node_id r#iter in
           saved_copy := Some n;
           paste_item#misc#set_sensitive true
  | _ ->
     saved_copy := None;
     paste_item#misc#set_sensitive false

let paste () =
  match get_selected_row_references () with
  | [r] ->
      let m = get_node_id r#iter in
    (match !saved_copy with
    | Some n -> send_request (Copy_paste (n, m))
    | None -> ())
  | _ -> ()

let () =
  paste_item#misc#set_sensitive false;
  connect_menu_item copy_item ~callback:copy;
  connect_menu_item paste_item ~callback:paste

(**********************************)
(* Notification handling (part 2) *)
(**********************************)

let check_uninstalled_prover =
  let uninstalled_prover_seen = Whyconf.Hprover.create 3 in
  fun p ->
  if not (Whyconf.Hprover.mem uninstalled_prover_seen p)
  then
    begin
      Whyconf.Hprover.add uninstalled_prover_seen p ();
      let callback p u =
        send_request (Set_prover_policy(p,u))
      in
      uninstalled_prover_dialog ~parent:main_window ~callback gconfig p
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
              Debug.dprintf debug "proved status changed to %b for %d@." b id;
              if b then
                begin
                  (* if the node newly proved is selected, then force
                   moving the selection the next unproved goal *)
                  if is_selected_alone id then
                    send_request (Get_first_unproven_node (Clever, id))
                end
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
      if is_selected_alone asked_id &&
         (* The user manually asked for next node from this one *)
         (!manual_next = Some asked_id ||
          (* or auto next is on *)
          gconfig.auto_next) then
        begin
          manual_next := None;
          (* Unselect the potentially selected goal to avoid having two tasks
             selected at once when a prover successfully end. To continue the
             proof, it is better to only have the new goal selected *)
          goals_view#selection#unselect_all ();
          let row = get_node_row next_unproved_id in
          goals_view#expand_to_path row#path;
          select_iter row#iter
        end
  | New_node (id, parent_id, typ, name, detached) ->
     begin
       try
         let parent = get_node_row parent_id in
         ignore (new_node ~parent id name typ detached);
         match typ with
         | NTransformation ->
            (* if this new node is a transformation, and its parent
               goal is selected, then ask for the next goal to prove. *)
            if is_selected_alone parent_id then
              send_request (Get_first_unproven_node (Clever, parent_id))
         | _ -> ()
       with Not_found ->
         ignore (new_node id name typ detached)
     end
  | Remove id                     ->
     let n = get_node_row id in
     if get_node_detached id then begin
         let path = goals_model#get_path n#iter in
         ignore(GtkTree.TreePath.prev path);
         goals_view#set_cursor path view_name_column
       end
     else begin
         (* In the case where id is an ancestor of a selected node, this node will
        be erased. So we try to select the parent. *)
         let is_ancestor =
           List.exists
             (fun row -> let row_id = get_node_id row#iter in
                         row_id = id || goals_model#is_ancestor ~iter:n#iter ~descendant:row#iter)
             (get_selected_row_references ())
         in
         if is_ancestor then
           (match goals_model#iter_parent n#iter with
            | None -> goals_view#selection#unselect_all ()
            | Some parent ->
               goals_view#selection#unselect_all ();
               select_iter parent
           (* TODO Go to the next unproved goal ?
            let parent_id = get_node_id parent in
          send_request (Get_first_unproven_node parent_id)*));
       end;
     ignore (goals_model#remove(n#iter));
     Hint.remove node_id_to_gtree id;
     Hint.remove node_id_type id;
     Hint.remove node_id_proved id;
     Hint.remove node_id_pa id
  | Initialized g_info            ->
     initialization_complete := true;
     main_window#show ();
     display_warnings ();
     init_completion g_info.provers g_info.transformations g_info.strategies g_info.commands;
     complete_context_menu ();
     Opt.iter select_iter goals_model#get_iter_first
  | Saved                         ->
      print_message ~kind:1 ~notif_kind:"Saved action info"
                        "Session saved.";
      if !quit_on_saved = true then
        exit_function_safe ()
  | Saving_needed b -> exit_function_handler b
  | Message (msg)                 -> treat_message_notification msg
  | Task (id, s, list_loc, goal_loc, lang)        ->
     if is_selected_alone id then
       begin
         change_lang task_view lang;
         task_view#source_buffer#set_text s;
         (* Avoid erasing colors at startup when selecting the first node. In
            all other cases, it should change nothing. *)
         if list_loc != [] then
           apply_loc_on_source list_loc goal_loc
         else
           begin
             erase_loc_all_view ();
             (* Still scroll to the ident (for example for modules) *)
             scroll_to_loc ~force_tab_switch:true goal_loc
           end;
         (* Scroll to the end of task text without any animation.
            We cannot use the scroll_to methods, as they eventually call
            gtk_adjustment_animate_to_value in GTK3. So, we manually call
            gtk_adjustment_set_value (through get_adjustment_clamp_page,
            because of GTK2). We cannot do that immediately though, as the
            vertical adjustment does not yet reflect the new content. *)
         when_idle (fun () ->
             let a = scrolled_task_view#vadjustment in
             a#clamp_page ~lower:a#upper ~upper:a#upper)
       end
  | File_contents (file_name, content, f_format, read_only) ->
     let content = try_convert content in
     begin
       try
         let (_, sc_view, _) = Hstr.find source_view_table file_name in
         (* read_only means it was sent by ctrl+l not by reload. So, if the file
            already exists, we dont want to erase users changes. *)
         if not read_only then
           begin
             sc_view#source_buffer#begin_not_undoable_action ();
             sc_view#source_buffer#set_text content;
             sc_view#source_buffer#end_not_undoable_action ();
             sc_view#source_buffer#set_modified false;
             reposition_ide_cursor ()
           end
       with
       | Not_found ->
           create_source_view ~read_only file_name content f_format
     end
  | Source_and_ce (content, list_loc, goal_loc, f_format) ->
    begin
      messages_notebook#goto_page counterexample_page;
      counterexample_view#source_buffer#set_text content;
      change_lang counterexample_view f_format;
      apply_loc_on_ce list_loc;
      scroll_to_loc_ce goal_loc
    end
  | Dead _ ->
     print_message ~kind:1 ~notif_kind:"Server Dead ?"
                        "Server sent the notification '%a'. Please report."
        print_notify n
  | Ident_notif_loc loc ->
      scroll_to_loc ~force_tab_switch:true (Some loc)
  end;
  ()

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

(***************************************************)
(* simulate some user actions and take screenshots *)
(***************************************************)

let pos_cursor_and_color (v:GSourceView.source_view) =
  let buf = v#source_buffer in
  let iter = buf#get_iter_at_mark `INSERT in
  let line, column = iter#line + 1, iter#line_index in
  (* This is the line that corresponds to the goal *)
  Format.printf "Cursor is placed at position: (%d, %d)@."
    line column;
  let iter = ref buf#start_iter in
  Format.printf "Recorded colors on the source code are:@.";
  while not (!iter#is_end) do
    let l = !iter#get_toggled_tags true in
    if l = [] then
      ()
    else
      List.iter (fun (tag: GText.tag) ->
          let tag_name = tag#get_property GtkText.Tag.P.name in
          if tag_name <> "" then
            let iter2 = !iter#forward_to_tag_toggle (Some tag) in
            Format.printf "Color \"%s\" from (%d, %d) to (%d, %d)@."
              tag_name !iter#line !iter#line_index iter2#line iter2#line_index)
        l;
    iter := !iter#forward_char;
  done;
  Format.printf "End color@."

let batch s =
  let cmd = ref (Strings.split ';' s) in
  let last = ref (Sys.time ()) in
  fun () ->
  let t = Sys.time () in
  if not !initialization_complete || t -. !last < 0.2 then true else
  match !cmd with
  | c :: tl ->
    cmd := tl;
    last := t;
    begin match Strings.split ' ' c with
    | [""] -> ()
    | ["down"] ->
        move_current_row_selection_to_down ()
    | ["next"] -> move_current_row_selection_to_next ()
    | ["view"; "task"] -> notebook#goto_page 0
    | ["view"; "source"] -> notebook#goto_page 1
    | ["wait"; w] ->
      let w = int_of_string w in
      if w > 0 then cmd := Printf.sprintf "wait %d" (w - 1) :: !cmd
    | "faketype" :: cmd ->
      let cmd = Strings.join " " cmd in
      command_entry#misc#grab_focus ();
      command_entry#set_text cmd
    | "type" :: cmd ->
      let cmd = Strings.join " " cmd in
      command_entry#misc#grab_focus ();
      add_command list_commands cmd;
      interp cmd
    | "snap" :: cmd ->
      let cmd = Strings.join " " cmd in
      let cmd = Printf.sprintf "import -window \"%s\" -define png:include-chunk=none %s" window_title cmd in
      if Sys.command cmd <> 0 then Printf.eprintf "Batch command failed: %s\n%!" cmd
    | "color" :: cmd ->
        begin
          let cmd = Strings.join " " cmd in
          let v = Hstr.fold (fun _ x acc ->
              match acc, x with
              | None, (sp, sv, _) when sp = 1 ->
                  Some sv
              | _ -> acc) source_view_table None
          in
          Opt.iter pos_cursor_and_color v;
          interp cmd
        end
    | ["save"] -> send_request Save_req
    | _ -> Printf.eprintf "Unrecognized batch command: %s\n%!" c
    end;
    true
  | _ ->
    exit_function_unsafe ();
    false

(***********************)
(* start the interface *)
(***********************)

let () =
  Scheduler.timeout ~ms:Controller_itp.default_delay_ms
    (fun () -> List.iter treat_notification (get_notified ()); true);
  main_window#add_accel_group accel_group;
  main_window#set_icon (Some !Gconfig.why_icon);
  print_message ~kind:1 ~notif_kind:"Info" "Welcome to Why3 IDE\ntype 'help' for help\n";
  begin match !opt_batch with
  | Some s ->
    let (_ : GMain.Idle.id) = GMain.Idle.add ~prio:300 (backtrace_and_exit (batch s)) in ()
  | None -> ()
  end;
  GMain.main ()
