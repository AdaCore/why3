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


open Format

open Why3
open Whyconf
open Gconfig
open Stdlib
open Debug

module C = Whyconf

external reset_gc : unit -> unit = "ml_reset_gc"

(* Setting a Gc.alarm is pointless; the function has to be called manually
   before each lablgtk operation. Indeed, each major slice resets
   caml_extra_heap_resources to zero, but alarms are executed only at
   finalization time, that is, after a full collection completes. Note that
   manual calls can fail to prevent extraneous collections too, if a major
   slice happens right in the middle of a sequence of lablgtk operations due
   to memory starvation. Hopefully, it seldom happens. *)
let () = reset_gc ()

let debug = Debug.lookup_flag "ide_info"

let debug_show_text_cntexmp = Debug.register_info_flag "show_text_cntexmp"
  ~desc:"Print@ textual@ counterexample@ before@ printing@ counterexample@ interleaved@ with@ cource@ code."

(************************)
(* parsing command line *)
(************************)

let files = Queue.create ()
let opt_parser = ref None

let spec = Arg.align [
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

let gconfig = try
  let config, base_config, env =
    Whyconf.Args.initialize spec (fun f -> Queue.add f files) usage_str in
  if Queue.is_empty files then Whyconf.Args.exit_with_usage spec usage_str;
  Gconfig.load_config config base_config env;
  Gconfig.config ()

  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "%a@." Exn_printer.exn_printer e;
    exit 1

let () =
  Debug.dprintf debug "[GUI] Init the GTK interface...@?";
  ignore (GtkMain.Main.init ());
  Debug.dprintf debug " done.@.";
  Gconfig.init ()

let (why_lang, any_lang) =
  let main = Gconfig.get_main () in
  let load_path = Filename.concat (datadir main) "lang" in
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

let menubar = GMenu.menu_bar
  ~packing:(vbox#pack ?from:None ?expand:None ?fill:None ?padding:None)
  ()

let factory = new GMenu.factory menubar

let accel_group = factory#accel_group

let hb = GPack.hbox ~packing:vbox#add ()

let left_scrollview =
  try
    GBin.scrolled_window ~hpolicy:`NEVER ~vpolicy:`AUTOMATIC
      ~packing:(hb#pack ~expand:false ?from:None ?fill:None ?padding:None) ()
  with Gtk.Error _ -> assert false

let () = left_scrollview#set_shadow_type `OUT

let tools_window_vbox =
  try
    GPack.vbox ~packing:left_scrollview#add_with_viewport ()
  with Gtk.Error _ -> assert false

let tools_window_vbox_pack =
  tools_window_vbox#pack ~expand:false ?from:None ?fill:None ?padding:None

let context_frame =
  GBin.frame ~label:"Context" ~shadow_type:`ETCHED_OUT
    ~packing:tools_window_vbox_pack ()

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


let strategies_frame =
  GBin.frame ~label:"Strategies" ~shadow_type:`ETCHED_OUT
    ~packing:tools_window_vbox_pack ()

let strategies_box =
  GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
  ~packing:strategies_frame#add ()

let provers_frame =
  GBin.frame ~label:"Provers" ~shadow_type:`ETCHED_OUT
    ~packing:tools_window_vbox_pack ()


let provers_box =
  GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
  ~packing:provers_frame#add ()

let () = provers_frame#set_resize_mode `PARENT

let tools_frame =
  GBin.frame ~label:"Tools" ~shadow_type:`ETCHED_OUT
    ~packing:tools_window_vbox_pack ()

let tools_box =
  GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
  ~packing:tools_frame#add ()

let monitor_frame =
  GBin.frame ~label:"Proof monitoring" ~shadow_type:`ETCHED_OUT
    ~packing:tools_window_vbox_pack ()

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
      ~width:gconfig.tree_width ~shadow_type:`ETCHED_OUT
      ~packing:hp#add ()
  with Gtk.Error _ -> assert false

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
  Debug.dprintf debug "[GUI] Creating tree model...@?";
  let model = GTree.tree_store cols in
  let view = GTree.view ~model ~packing:scrollview#add () in
  let () = view#selection#set_mode (* `SINGLE *) `MULTIPLE in
  let () = view#set_rules_hint true in
  ignore (view#append_column view_name_column);
  ignore (view#append_column view_status_column);
  ignore (view#append_column view_time_column);
  Debug.dprintf debug " done@.";
  model,view


(******************************)
(*    notebook on the right   *)
(******************************)

let notebook = GPack.notebook ~packing:hp#add ()

let source_page,source_tab =
  let label = GMisc.label ~text:"Source code" () in
  0, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()

let task_page,task_tab =
  let label = GMisc.label ~text:"Task" () in
  1, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()

let edited_page,edited_tab =
  let label = GMisc.label ~text:"Edited proof" () in
  2, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()

let output_page,output_tab =
  let label = GMisc.label ~text:"Prover Output" () in
  3, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()

let counterexample_page,counterexample_tab =
  let label = GMisc.label ~text:"Counter-example" () in
  4, GPack.vbox ~homogeneous:false ~packing:
    (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()

let (_ : GPack.box) =
  GPack.hbox ~packing:(source_tab#pack ~expand:false ?from:None ?fill:None
                         ?padding:None) ()

let () =
  notebook#goto_page gconfig.current_tab;
  let page_selected n = gconfig.current_tab <- n in
  let (_ : GtkSignal.id) =
    notebook#connect#switch_page ~callback:page_selected
  in ()



(******************)
(* views          *)
(******************)

let current_file = ref ""

let scrolled_task_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT ~packing:task_tab#add ()

let task_view =
  GSourceView2.source_view
    ~editable:false
    ~show_line_numbers:true
    ~packing:scrolled_task_view#add
    ()

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

let modifiable_sans_font_views = ref [goals_view#misc]
let modifiable_mono_font_views =
  ref [task_view#misc;edited_view#misc;output_view#misc;
       counterexample_view#misc
]
let () = task_view#source_buffer#set_language why_lang
let () = task_view#set_highlight_current_line true


let clear model = model#clear ()

let image_of_result ~obsolete result =
  match result with
    | Session.Interrupted -> !image_undone
    | Session.Unedited -> !image_editor
    | Session.JustEdited -> !image_unknown
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

(* connecting to the Session model *)

let fan n =
  match n mod 4 with
    | 0 -> "|"
    | 1 | -3 -> "\\"
    | 2 | -2 -> "-"
    | 3 | -1 -> "/"
    | _ -> assert false

module S = Session

let session_needs_saving = ref false

let set_row_status row b =
  match b with
  | Some t ->
    goals_model#set ~row:row#iter ~column:status_column !image_yes;
    let t = Format.sprintf "%.2f" t in
    goals_model#set ~row:row#iter ~column:time_column t
  | None ->
    goals_model#set ~row:row#iter ~column:status_column !image_unknown;
    goals_model#set ~row:row#iter ~column:time_column ""

let set_proof_state a =
  let obsolete = a.S.proof_obsolete in
  let row = a.S.proof_key in
  let res = a.S.proof_state in
  goals_model#set ~row:row#iter ~column:status_column
    (image_of_result ~obsolete res);
  let t = match res with
    | S.Done { Call_provers.pr_time = time; Call_provers.pr_steps = steps } ->
       let s =
        if gconfig.show_time_limit then
          Format.sprintf "%.2f [%d.0]" time
          (a.S.proof_limit.Call_provers.limit_time)
        else
          Format.sprintf "%.2f" time
       in
       if steps >= 0 then
	 Format.sprintf "%s (steps: %d)" s steps
       else
	 s
    | S.Unedited -> "(not yet edited)"
    | S.JustEdited -> "(edited)"
    | S.InternalFailure _ -> "(internal failure)"
    | S.Interrupted -> "(interrupted)"
    | S.Scheduled | S.Running ->
        Format.sprintf "[limit=%d sec., %d M]"
          (a.S.proof_limit.Call_provers.limit_time)
          (a.S.proof_limit.Call_provers.limit_mem)
  in
  let t = if obsolete then t ^ " (obsolete)" else t in
  (* TODO find a better way to signal archived row *)
  let t = if a.S.proof_archived then t ^ " (archived)" else t in
  goals_model#set ~row:row#iter ~column:time_column t

let model_index = Hint.create 17

let get_any_from_iter row =
  try
    let idx = goals_model#get ~row ~column:index_column in
    Hint.find model_index idx
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
  session_needs_saving := true;
  let expand_g g = goals_view#expand_row (S.goal_key g)#path in
  let expand_tr _ tr = goals_view#expand_row tr.S.transf_key#path in
  let expand_m _ m = goals_view#expand_row m.S.metas_key#path in
  match get_any_from_iter iter with
    | S.File f ->
        S.set_file_expanded f b
    | S.Theory t ->
        S.set_theory_expanded t b
    | S.Goal g ->
        S.set_goal_expanded g b;
        if b then begin
          Session.PHstr.iter expand_tr (S.goal_transformations g);
          Session.Mmetas_args.iter expand_m (S.goal_metas g)
        end
    | S.Transf tr ->
        S.set_transf_expanded tr b;
        if b then begin match tr.S.transf_goals with
          | [g] -> expand_g g
          | _ -> ()
        end
    | S.Proof_attempt _ -> ()
    | S.Metas m ->
        S.set_metas_expanded m b;
        if b then expand_g m.S.metas_goal

let current_selected_row = ref None
let current_env_session = ref None
let env_session () =
  match !current_env_session with
    | None -> assert false
    | Some e -> e

let task_text t =
  let max_boxes = (Gconfig.config ()).max_boxes in
  Pp.string_of ~max_boxes Pretty.print_task t

let split_transformation = "split_goal_wp"
let inline_transformation = "inline_goal"
let intro_transformation = "introduce_premises"

let goal_task_text g =
  if (Gconfig.config ()).intro_premises then
    let trans =
      Trans.lookup_transform intro_transformation (env_session()).S.env
    in
    task_text (try Trans.apply trans (S.goal_task g) with
      e -> eprintf "@.%a@." Exn_printer.exn_printer e; raise e)
  else
    task_text (S.goal_task g)

let file_contents f =
  let s = try Sysutil.file_contents f
          with Invalid_argument s -> s
  in try_convert s


let update_tabs a =
  let task_text =
    match a with
    | S.Goal g -> goal_task_text g
    | S.Proof_attempt a -> goal_task_text a.S.proof_parent
    | S.Theory th -> "Theory " ^ th.S.theory_name.Ident.id_string
    | S.File file -> "File " ^ file.S.file_name
    | S.Transf tr -> "transformation \"" ^ tr.S.transf_name ^ "\""
    | S.Metas _ -> "metas"
  in
  let edited_text =
    match a with
    | S.Proof_attempt a ->
      begin
        let env = env_session () in
        match S.get_edited_as_abs env.S.session a with
        | None -> ""
        | Some f -> file_contents f
      end
    | _ -> ""
  in
  let output_text =
    match a with
    | S.Proof_attempt a ->
        begin
          match a.S.proof_state with
            | S.Interrupted -> "proof not yet scheduled for running"
            | S.Unedited ->
              "Interactive proof, not yet edited. Edit with \"Edit\" button"
            | S.JustEdited ->
              "Edited interactive proof. Run it with \"Replay\" button"
            | S.Done
                ({Call_provers.pr_answer = Call_provers.HighFailure} as r) ->
              Call_provers.print_prover_result str_formatter r;
                  flush_str_formatter ()
            | S.Done r ->
              let out = r.Call_provers.pr_output in
              if out = "" then
                "Output not available. Rerun it with \"Replay\" button"
              else out
            | S.Scheduled-> "proof scheduled but not running yet"
            | S.Running -> "prover currently running"
            | S.InternalFailure e ->
              fprintf str_formatter "%a" Exn_printer.exn_printer e;
              flush_str_formatter ()
        end
    | S.Metas m ->
      let print_meta_args =
        Pp.hov 2 (Pp.print_list Pp.space Pretty.print_meta_arg) in
      let print =
        Pp.print_iter2 Mstr.iter Pp.newline2 Pp.newline Pp.string
          (Pp.indent 2
             (Pp.print_iter1 S.Smeta_args.iter Pp.newline print_meta_args))
      in
      (Pp.string_of (Pp.hov 2 print) m.S.metas_added)
    | _ -> ""
 in

  let counterexample_text =
    match a with
    | S.Proof_attempt a ->
      begin
        match a.S.proof_state with
	  | S.Done r ->
	    if not (Model_parser.is_model_empty r.Call_provers.pr_model) then begin
	      let cntexample_text =
		if Debug.test_flag debug_show_text_cntexmp then
		  "Counterexample:\n" ^
		    (Model_parser.model_to_string r.Call_provers.pr_model) ^
		    "\n\nSource code interleaved with counterexample:"
		else
		  "" in
	      let cntexample_text = cntexample_text ^
		(Model_parser.interleave_with_source
		   r.Call_provers.pr_model
		   ~filename:!current_file
		   ~source_code:(file_contents !current_file)) in
	      cntexample_text
	    end else
	      ""
	  | _ -> ""
      end
    | _ -> ""
  in

  let lang =
    if Filename.check_suffix !current_file ".why" ||
      Filename.check_suffix !current_file ".mlw"
    then why_lang else any_lang !current_file
  in
  counterexample_view#source_buffer#set_language lang;

  task_view#source_buffer#set_text task_text;
  task_view#scroll_to_mark `INSERT;
  edited_view#source_buffer#set_text edited_text;
  edited_view#scroll_to_mark `INSERT;
  output_view#source_buffer#set_text output_text;
  counterexample_view#source_buffer#set_text counterexample_text;
  counterexample_view#scroll_to_mark `INSERT;



module MA = struct
     type key = GTree.row_reference

     let create ?parent () =
       reset_gc ();
       session_needs_saving := true;
       let parent = match parent with
         | None -> None
         | Some r -> Some r#iter
       in
       let iter = goals_model#append ?parent () in
       goals_model#set ~row:iter ~column:index_column (-1);
       goals_model#get_row_reference (goals_model#get_path iter)

     let keygen = create

     let remove row =
       session_needs_saving := true;
       let (_:bool) = goals_model#remove row#iter in ()

     let reset () =
       session_needs_saving := true;
       goals_model#clear ()

     let idle f =
       let (_ : GMain.Idle.id) = GMain.Idle.add f in ()

     let timeout ~ms f =
       let (_ : GMain.Timeout.id) = GMain.Timeout.add ~ms ~callback:f in
       ()

     let notify_timer_state =
       let c = ref 0 in
       fun t s r ->
         reset_gc ();
         incr c;
         monitor_waiting#set_text ("Waiting: " ^ (string_of_int t));
         monitor_scheduled#set_text ("Scheduled: " ^ (string_of_int s));
         monitor_running#set_text
           (if r=0 then "Running: 0" else
              "Running: " ^ (string_of_int r)^ " " ^ (fan (!c / 10)))

let notify any =
  reset_gc ();
  session_needs_saving := true;
  let row,expanded =
    match any with
      | S.Goal g -> (S.goal_key g), (S.goal_expanded g)
      | S.Theory t -> t.S.theory_key, t.S.theory_expanded
      | S.File f -> f.S.file_key, f.S.file_expanded
      | S.Proof_attempt a -> a.S.proof_key,false
      | S.Transf tr ->
        tr.S.transf_key,tr.S.transf_expanded
      | S.Metas m -> m.S.metas_key,m.S.metas_expanded
  in
  (* name is set by notify since upgrade policy may update the prover name *)
  goals_model#set ~row:row#iter ~column:name_column
    (match any with
      | S.Goal g -> S.goal_user_name g
      | S.Theory th -> th.S.theory_name.Ident.id_string
      | S.File f -> Filename.basename f.S.file_name
      | S.Proof_attempt a ->
        let p = a.S.proof_prover in
        Pp.string_of_wnl C.print_prover p
      | S.Transf tr -> tr.S.transf_name
      | S.Metas _m -> "Metas..."
   );
  let ind = goals_model#get ~row:row#iter ~column:index_column in
  begin
    match !current_selected_row with
      | Some r when r == ind ->
        update_tabs any
      | _ -> ()
  end;
  if expanded then goals_view#expand_to_path row#path else
    goals_view#collapse_row row#path;
  match any with
    | S.Goal g ->
        set_row_status row (S.goal_verified g)
    | S.Theory th ->
        set_row_status row th.S.theory_verified
    | S.File file ->
        set_row_status row file.S.file_verified
    | S.Proof_attempt a ->
        set_proof_state a
    | S.Transf tr ->
        set_row_status row tr.S.transf_verified
    | S.Metas m ->
        set_row_status row m.S.metas_verified

let init =
  let cpt = ref (-1) in
  fun row any ->
    reset_gc ();
    let ind = goals_model#get ~row:row#iter ~column:index_column in
    if ind < 0 then
      begin
        incr cpt;
        Hint.add model_index !cpt any;
        goals_model#set ~row:row#iter ~column:index_column !cpt
      end
    else
      begin
        Hint.replace model_index ind any;
      end;
    (* useless since it has no child: goals_view#expand_row row#path; *)
    goals_model#set ~row:row#iter ~column:icon_column
      (match any with
         | S.Goal _ -> !image_goal
         | S.Theory _ -> !image_theory
         | S.File _ -> !image_file
         | S.Proof_attempt _ -> !image_prover
         | S.Transf _ -> !image_transf
         | S.Metas _ -> !image_metas);
    notify any

let rec init_any any =
  init (S.key_any any) any;
  S.iter init_any any

let uninstalled_prover = Gconfig.uninstalled_prover gconfig

end

module M = Session_scheduler.Make(MA)


let () = w#add_accel_group accel_group
let () = w#show ()

(********************)
(* opening database *)
(********************)

(** TODO remove that should done only in session *)
let project_dir =
  let fname = Queue.pop files in
  (* The remaining files in [files] are going to be open *)
  if Sys.file_exists fname then
    begin
      if Sys.is_directory fname then
        begin
          Debug.dprintf debug
            "[GUI] found directory '%s' for the project@." fname;
          fname
        end
      else
        if Queue.is_empty files then (* that was the only file *) begin
          Debug.dprintf debug "[GUI] found regular file '%s'@." fname;
          let d =
            try Filename.chop_extension fname
            with Invalid_argument _ -> fname
          in
          Debug.dprintf debug
            "[GUI] using '%s' as directory for the project@." d;
          Queue.push fname files; (* we need to open [fname] *)
          d
        end
        else begin
          (* The first argument is not a directory and it's not the
              only file *)
          Format.eprintf
            "[Error] @[When@ more@ than@ one@ file@ is@ given@ on@ the@ \
             command@ line@ the@ first@ one@ must@ be@ the@ directory@ \
             of@ the@ session.@]@.";
          Arg.usage spec usage_str; exit 1
        end
    end
  else
    fname

let () =
  if not (Sys.file_exists project_dir) then
    begin
      Debug.dprintf debug "[GUI] '%s' does not exist. \
        Creating directory of that name for the project@." project_dir;
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
    ~message_type:(mt :> Gtk.Tags.message_type)
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

let file_info = GMisc.label ~text:""
  ~packing:(source_tab#pack ~fill:true ?from:None ?expand:None ?padding:None) ()

let warnings = Queue.create ()

let record_warning ?loc msg =
  Format.eprintf "%awarning: %s@."
    (Pp.print_option Loc.report_position) loc msg;
  Queue.push (loc,msg) warnings

let () = Warning.set_hook record_warning

let display_warnings () =
  if Queue.is_empty warnings then () else
    begin
      let nwarn = ref 0 in
      begin try
      Queue.iter
        (fun (loc,msg) ->
         if !nwarn = 4 then
           begin
             Format.fprintf Format.str_formatter "[%d more warnings. See stderr for details]@\n" (Queue.length warnings - !nwarn);
             raise Exit
           end
         else
           begin
             incr nwarn;
             match loc with
             | None ->
                Format.fprintf Format.str_formatter "%s@\n@\n" msg
             | Some l ->
                (* scroll_to_loc ~color:error_tag ~yalign:0.5 loc; *)
                Format.fprintf Format.str_formatter "%a: %s@\n@\n"
                               Loc.gen_report_position l msg
           end) warnings;
        with Exit -> ();
      end;
      Queue.clear warnings;
      let msg =
        Format.flush_str_formatter ()
      in
  (* file_info#set_text msg; *)
      info_window `WARNING msg
    end

(* check if provers are present *)
let () =
  if C.Mprover.is_empty (C.get_provers gconfig.Gconfig.config) then
    begin
      info_window `ERROR
        "No prover configured.\nPlease run 'why3 config --detect-provers' first"
        ~callback:GMain.quit;
      GMain.main ();
      exit 2;
    end

let sched =
  try
    Debug.dprintf debug "@[<hov 2>[GUI session] Opening session...@\n";
    let session,use_shapes =
      if Sys.file_exists project_dir then
        S.read_session project_dir
      else
        S.create_session project_dir, false
    in
    let env,(_:bool),(_:bool) =
      M.update_session ~allow_obsolete:true ~release:false ~use_shapes
        session gconfig.env gconfig.Gconfig.config
    in
    Debug.dprintf debug "@]@\n[GUI session] Opening session: update done@.  @[<hov 2>";
    let sched = M.init (gconfig.session_nb_processes)
    in
    Debug.dprintf debug "@]@\n[GUI session] Opening session: done@.";
    session_needs_saving := false;
    current_env_session := Some env;
    sched
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "@[Error while opening session:@ %a@.@]"
      Exn_printer.exn_printer e;
    exit 1


(**********************************)
(* add new file from command line *)
(**********************************)

let open_file ?(start=false) f =
  let f = Sysutil.relativize_filename project_dir f in
  Debug.dprintf debug "[GUI session] Adding file '%s'@." f;
  if S.PHstr.mem (env_session()).S.session.S.session_files f then
    Debug.dprintf debug "[GUI] file %s already in database@." f
  else
    try
      Debug.dprintf debug "[GUI] adding file %s in database@." f;
      ignore (M.add_file (env_session()) ?format:!opt_parser f);
    with e ->
      if start
      then begin
        eprintf "@[Error while reading file@ '%s':@ %a@]@." f
          Exn_printer.exn_printer e;
        exit 1
      end
      else
        let msg =
          Pp.sprintf_wnl "@[Error while reading file@ '%s':@ %a@]" f
            Exn_printer.exn_printer e in
        info_window `ERROR msg

let () = Queue.iter (open_file ~start:true) files

(*****************************************************)
(* method: run a given prover on each unproved goals *)
(*****************************************************)

let prover_on_selected_goals pr =
  let timelimit = gconfig.session_time_limit in
  let memlimit = gconfig.session_mem_limit in
  let cntexample = Whyconf.cntexample (Whyconf.get_main gconfig.config) in
  List.iter
    (fun row ->
      try
       let a = get_any_from_row_reference row in
       M.run_prover
         (env_session()) sched
         ~context_unproved_goals_only:!context_unproved_goals_only
         ~cntexample
         ~limit:{Call_provers.empty_limit with
                Call_provers.limit_time = timelimit;
                              limit_mem = memlimit }
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
       M.replay (env_session()) sched ~obsolete_only:true
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
(* method: apply strategy on selected goals *)
(*****************************************************)


let apply_trans_on_selection tr =
  List.iter
    (fun r ->
       let a = get_any_from_row_reference r in
        M.transform (env_session()) sched
          ~context_unproved_goals_only:!context_unproved_goals_only
          tr a)
    (get_selected_row_references ())


let apply_strategy_on_selection str =
  List.iter
    (fun r ->
      let a = get_any_from_row_reference r in
      M.run_strategy (env_session()) sched
        ~context_unproved_goals_only:!context_unproved_goals_only
        str a)
    (get_selected_row_references ())


(*****************************************************)
(* method: bisect goal *)
(*****************************************************)

let bisect_proof_attempt pa =
  let eS = env_session () in
  let timelimit = ref (-1) in
  let set_timelimit res =
    timelimit := 1 + (int_of_float (floor res.Call_provers.pr_time)) in
  let cntexample = Whyconf.cntexample (Whyconf.get_main gconfig.config) in
  let rec callback lp pa c = function
    | S.Running | S.Scheduled -> ()
    | S.Interrupted ->
      dprintf debug "Bisecting interrupted.@."
    | S.Unedited | S.JustEdited -> assert false
    | S.InternalFailure exn ->
      (* Perhaps the test can be considered false in this case? *)
      dprintf debug "Bisecting interrupted by an error %a.@."
        Exn_printer.exn_printer exn
    | S.Done res ->
      let b = res.Call_provers.pr_answer = Call_provers.Valid in
      dprintf debug "Bisecting: %a.@."
        Call_provers.print_prover_result res;
      if b then set_timelimit res;
      let r = c b in
      match r with
      | Eliminate_definition.BSdone [] ->
        dprintf debug "Bisecting doesn't reduced the task.@."
      | Eliminate_definition.BSdone reml ->
        dprintf debug "Bisecting done.@.";
        begin try
        let keygen = MA.keygen in
        let notify = MA.notify in
        let reml = List.map (fun (m,l) -> m.Theory.meta_name,l) reml in
        let metas = S.add_registered_metas ~keygen eS reml pa.S.proof_parent in
        let trans = S.add_registered_transformation ~keygen
          eS "eliminate_builtin" metas.S.metas_goal in
        let goal = List.hd trans.S.transf_goals in (* only one *)
        let npa = S.copy_external_proof ~notify ~keygen ~obsolete:true
          ~goal ~env_session:eS pa in
        MA.init_any (S.Metas metas);
        M.run_external_proof eS sched ~cntexample npa
        with e ->
          dprintf debug "Bisecting error:@\n%a@."
            Exn_printer.exn_printer e end
      | Eliminate_definition.BSstep (t,c) ->
        assert (not lp.S.prover_config.C.in_place); (* TODO do this case *)
        M.schedule_proof_attempt
	  ~cntexample
          ~limit:{Call_provers.empty_limit with
                  Call_provers.limit_time = !timelimit;
                  limit_mem = pa.S.proof_limit.Call_provers.limit_mem }
          ?old:(S.get_edited_as_abs eS.S.session pa)
          (* It is dangerous, isn't it? to be in place for bisecting? *)
          ~inplace:lp.S.prover_config.C.in_place
          ~command:(C.get_complete_command lp.S.prover_config ~with_steps:false)
          ~driver:lp.S.prover_driver
          ~callback:(callback lp pa c) sched t
  in
    (* Run once the complete goal in order to verify its validity and
       update the proof attempt *)
  let first_callback pa = function
    (* this pa can be different than the first pa *)
    | S.Running | S.Scheduled -> ()
    | S.Interrupted ->
      dprintf debug "Bisecting interrupted.@."
    | S.Unedited | S.JustEdited -> assert false
    | S.InternalFailure exn ->
        dprintf debug "proof of the initial task interrupted by an error %a.@."
          Exn_printer.exn_printer exn
    | S.Done res ->
      if res.Call_provers.pr_answer <> Call_provers.Valid
      then dprintf debug "Initial task can't be proved.@."
      else
        let t = S.goal_task pa.S.proof_parent in
        let r = Eliminate_definition.bisect_step t in
        match r with
        | Eliminate_definition.BSdone res ->
          assert (res = []);
          dprintf debug "Task can't be reduced.@."
        | Eliminate_definition.BSstep (t,c) ->
          set_timelimit res;
          match S.load_prover eS pa.S.proof_prover with
          | None -> (* No prover so we do nothing *)
            dprintf debug "Prover can't be loaded.@."
          | Some lp ->
            M.schedule_proof_attempt
	      ~cntexample
              ~limit:{pa.S.proof_limit with
                        Call_provers.limit_steps =
                          Call_provers.empty_limit.Call_provers.limit_steps;
                        limit_time = !timelimit}
              ?old:(S.get_edited_as_abs eS.S.session pa)
              ~inplace:lp.S.prover_config.C.in_place
              ~command:(C.get_complete_command lp.S.prover_config
                            ~with_steps:false)
              ~driver:lp.S.prover_driver
              ~callback:(callback lp pa c) sched t in
  dprintf debug "Bisecting with %a started.@."
    C.print_prover pa.S.proof_prover;
  M.run_external_proof eS sched ~cntexample ~callback:first_callback pa

let apply_bisect_on_selection () =
  List.iter
    (fun r ->
      let a = get_any_from_row_reference r in
      S.iter_proof_attempt bisect_proof_attempt a
    ) (get_selected_row_references ())

(**************************************)
(* Copy Paste proof, transf and metas *)
(**************************************)
let copy_queue = Queue.create ()

let copy_on_selection () =
  Queue.clear copy_queue;
    List.iter
    (fun r ->
      let a = get_any_from_row_reference r in
      let rec add = function
      | S.Goal g -> S.goal_iter add g
      | S.Transf f -> Queue.push (S.Transf (S.copy_transf f)) copy_queue
      | S.Metas m -> Queue.push (S.Metas (S.copy_metas m)) copy_queue
      | S.Proof_attempt pa ->
        Queue.push (S.Proof_attempt (S.copy_proof pa)) copy_queue
      | _ -> () in
      add a
    ) (get_selected_row_references ())

let paste_on_selection () =
    List.iter
    (fun r ->
      let a = get_any_from_row_reference r in
      match a with
      | S.Goal g ->
        let keygen = MA.keygen in
        let paste = function
          | S.Transf f ->
            MA.init_any
              (S.Transf (S.add_transf_to_goal ~keygen (env_session()) g f))
          | S.Metas m  ->
            MA.init_any
              (S.Metas (S.add_metas_to_goal  ~keygen (env_session()) g m))
          | S.Proof_attempt pa ->
            MA.init_any (S.Proof_attempt
                           (S.add_proof_to_goal ~keygen (env_session()) g pa))
          | _ -> () in
        Queue.iter paste copy_queue
      | _ -> ()
    ) (get_selected_row_references ())



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
          | Some f -> open_file f
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
  file_factory#add_image_item (* ~key:GdkKeysyms._A *)
    ~label:"_Add file" ~callback:select_file
    ()

let gui_items = ref []

let add_gui_item f =
  f ();
  gui_items := f :: !gui_items

let recreate_gui () =
  List.iter (fun f -> f ()) (List.rev !gui_items)

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~label:"_Preferences" ~callback:
    (fun () ->
      Gconfig.preferences gconfig;
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
      let nb = gconfig.session_nb_processes in
      M.set_maximum_running_proofs nb sched)
    ()

(*
let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~label:"_Detect provers" ~callback:
    (fun () -> Gconfig.run_auto_detection gconfig; recreate_gui () )
    ()
*)

let save_session () =
  if !session_needs_saving then begin
    Debug.dprintf debug "[GUI] saving session@.";
    S.save_session gconfig.config (env_session()).S.session;
    session_needs_saving := false;
  end


let exit_function ~destroy () =
  (* do not save automatically anymore Gconfig.save_config (); *)
  if not !session_needs_saving then GMain.quit () else
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

let sans_font_family = "Sans"
let mono_font_family = "Monospace"

let change_font size =
(*
  Tools.resize_images (!Colors.font_size * 2 - 4);
*)
  let sff = sans_font_family ^ " " ^ string_of_int size in
  let mff = mono_font_family ^ " " ^ string_of_int size in
  let sf = Pango.Font.from_string sff in
  let mf = Pango.Font.from_string mff in
  List.iter (fun v -> v#modify_font sf) !modifiable_sans_font_views;
  List.iter (fun v -> v#modify_font mf) !modifiable_mono_font_views

let enlarge_font () =
  let size = Gconfig.incr_font_size 1 in
  change_font size

let reduce_font () =
  let size = Gconfig.incr_font_size (-1) in
  change_font size

let view_menu = factory#add_submenu "_View"
let view_factory = new GMenu.factory view_menu ~accel_group

let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._A
    ~label:"Select all"
    ~callback:(fun () -> goals_view#selection#select_all ()) ()

let (_ : GMenu.menu_item) =
  view_factory#add_item ~key:GdkKeysyms._plus
    ~callback:enlarge_font "Enlarge font"

let (_ : GMenu.menu_item) =
    view_factory#add_item ~key:GdkKeysyms._minus
      ~callback:reduce_font "Reduce font"

let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._E
    ~label:"Expand all" ~callback:(fun () -> goals_view#expand_all ()) ()

let rec collapse_verified = function
  | S.Goal g when Opt.inhabited (S.goal_verified g) ->
    let row = S.goal_key g in
    goals_view#collapse_row row#path
  | S.Theory th when Opt.inhabited th.S.theory_verified ->
    let row = th.S.theory_key in
    goals_view#collapse_row row#path
  | S.File f when Opt.inhabited f.S.file_verified ->
    let row = f.S.file_key in
    goals_view#collapse_row row#path
  | any -> S.iter collapse_verified any

let collapse_all_verified_things () =
  S.session_iter collapse_verified (env_session()).S.session

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
    Hstr.iter
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
  Hstr.iter
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


let tools_menu = factory#add_submenu "_Tools"
let tools_factory = new GMenu.factory tools_menu ~accel_group

let () = add_gui_item (fun () ->
  List.iter (fun item -> item#destroy ()) provers_box#all_children;
  List.iter (fun item -> item#destroy ()) tools_menu#all_children)

let add_tool_separator () =
  add_gui_item (fun () -> ignore(tools_factory#add_separator ()))

let add_tool_item label callback =
  add_gui_item (fun () -> ignore(tools_factory#add_image_item ~label ~callback ()))


let split_strategy =
  [| Strategy.Itransform(split_transformation,1) |]

let inline_strategy =
  [| Strategy.Itransform(inline_transformation,1) |]

(*
let test_strategy () =
  let config = gconfig.Gconfig.config in
  let altergo =
    let fp = Whyconf.parse_filter_prover "Alt-Ergo" in
    Whyconf.filter_one_prover config fp
  in
  let cvc4 =
    let fp = Whyconf.parse_filter_prover "CVC4" in
    Whyconf.filter_one_prover config fp
  in
  [|
    Strategy.Icall_prover(altergo.Whyconf.prover,1,1000);
    Strategy.Icall_prover(cvc4.Whyconf.prover,1,1000);
    Strategy.Itransform(split_transformation,0); (* goto 0 on success *)
    Strategy.Icall_prover(altergo.Whyconf.prover,10,4000);
    Strategy.Icall_prover(cvc4.Whyconf.prover,10,4000);
  |]
 *)

(*
let strategies () :
    (string * Pp.formatted * M.strategy *
       (string * Gdk.keysym) option) list =
  [ "Split", "Splits@ conjunctions@ of@ the@ goal", split_strategy,
    Some("s",GdkKeysyms._s);
    "Inline", "Inline@ defined@ symbols", inline_strategy,
    Some("i",GdkKeysyms._i);
    "Blaster", "Blaster@ strategy", test_strategy (),
    Some("b",GdkKeysyms._b);
  ]
*)

let loaded_strategies = ref []

let load_shortcut s =
  if String.length s <> 1 then None else
  try
    let key = match String.get s 0 with
      | 'a' -> GdkKeysyms._a
      | 'b' -> GdkKeysyms._b
      | 'c' -> GdkKeysyms._c
      | 'd' -> GdkKeysyms._d
      | 'e' -> GdkKeysyms._e
      | 'f' -> GdkKeysyms._f
      | 'g' -> GdkKeysyms._g
      | 'h' -> GdkKeysyms._h
      | 'i' -> GdkKeysyms._i
      | 'j' -> GdkKeysyms._j
      | 'k' -> GdkKeysyms._k
      | 'l' -> GdkKeysyms._l
      | 'm' -> GdkKeysyms._m
      | 'n' -> GdkKeysyms._n
      | 'o' -> GdkKeysyms._o
      | 'p' -> GdkKeysyms._p
      | 'q' -> GdkKeysyms._q
      | 'r' -> GdkKeysyms._r
      | 's' -> GdkKeysyms._s
      | 't' -> GdkKeysyms._t
      | 'u' -> GdkKeysyms._u
      | 'v' -> GdkKeysyms._v
      | 'w' -> GdkKeysyms._w
      | 'x' -> GdkKeysyms._x
      | 'y' -> GdkKeysyms._y
      | 'z' -> GdkKeysyms._z
      | _ -> raise Not_found
    in Some(s,key)
  with Not_found -> None

let strategies () =
  match !loaded_strategies with
    | [] ->
      let config = gconfig.Gconfig.config in
      let strategies = Whyconf.get_strategies config in
      let strategies =
        Mstr.fold_left
          (fun acc _ st ->
            let name = st.Whyconf.strategy_name in
            try
              let code = st.Whyconf.strategy_code in
              let code = Strategy_parser.parse (env_session()) code in
              let shortcut = load_shortcut st.Whyconf.strategy_shortcut in
              Format.eprintf "[GUI] Strategy '%s' loaded.@." name;
              (name, st.Whyconf.strategy_desc, code, shortcut) :: acc
            with Strategy_parser.SyntaxError msg ->
              Format.eprintf
                "[GUI warning] Loading strategy '%s' failed: %s@." name msg;
              acc)
          []
          strategies
      in
      let strategies = List.rev strategies in
      loaded_strategies := strategies;
      strategies
    | l -> l


let escape_text = Glib.Markup.escape_text

let sanitize_markup x =
  let remove = function
    | '_' -> "__"
    | c -> String.make 1 c in
  Ident.sanitizer remove remove (escape_text x)

let string_of_desc desc =
  let print_trans_desc fmt (x,r) =
    fprintf fmt "@[<hov 2>%s@\n%a@]" x Pp.formatted r
  in Pp.string_of print_trans_desc desc

let () =
  let transformations =
    List.sort (fun (x,_) (y,_) -> String.compare x y)
      (List.rev_append (Trans.list_transforms_l ()) (Trans.list_transforms ()))
  in
  let add_submenu_transform name filter () =
    let submenu = tools_factory#add_submenu name in
    let submenu = new GMenu.factory submenu ~accel_group in
    let iter ((name,_) as desc) =
      let callback () = apply_trans_on_selection name in
      let ii = submenu#add_image_item
        ~label:(sanitize_markup name) ~callback () in
      ii#misc#set_tooltip_text (string_of_desc desc)
    in
    let trans = List.filter filter transformations in
    List.iter iter trans
  in
  add_gui_item
    (add_submenu_transform "transformations (a-e)"
       (fun (x,_) -> x < "eliminate"));
  add_gui_item
    (add_submenu_transform "transformations (eliminate)"
       (fun (x,_) -> x >= "eliminate" && x < "eliminatf"));
  add_gui_item
    (add_submenu_transform "transformations (e-r)"
       (fun (x,_) -> x >= "eliminatf" && x < "s"));
  add_gui_item
    (add_submenu_transform "transformations (s-z)"
       (fun (x,_) -> x >= "s"));
  add_tool_separator ();
  add_tool_item "Bisect in selection" apply_bisect_on_selection

let () =
  let iter (name,desc,strat,k) =
    let desc = Scanf.format_from_string desc "" in
    let b = GButton.button ~packing:strategies_box#add
      ~label:(sanitize_markup name) ()
    in
    let name =
      match k with
        | None -> name
        | Some(s,_) -> name ^ " (shortcut:" ^ s ^ ")"
    in
    b#misc#set_tooltip_markup (string_of_desc (name,desc));
    let i = GMisc.image ~pixbuf:(!image_transf) () in
    let () = b#set_image i#coerce in
    let callback () = apply_strategy_on_selection strat in
    let (_ : GtkSignal.id) = b#connect#clicked ~callback in
    ()
  in
  List.iter iter (strategies ())


(*************)
(* Run  menu *)
(*************)

(*
let run_menu = factory#add_submenu "_Run"
let run_factory = new GMenu.factory run_menu ~accel_group

let eval const result =
  let msg =
    match Strings.split '.' const with
      | [f;m;i] ->
        begin
          let e = env_session () in
          let files = e.S.files in
          try
            let fi = Mstr.find f files in
            try
              let th = Mstr.find m fi in
              begin
                try
                  let ls = Theory.ns_find_ls th.Theory.th_export [i] in
                  match Decl.find_logic_definition th.Theory.th_known ls with
                    | None ->
                      Pp.sprintf
                        "Symbol '%s' has no definition in theory '%s.%s'" i f m
                    | Some d ->
                      let l,t = Decl.open_ls_defn d in
                      match l with
                        | [] ->
                          let t =
                            Mlw_interp.eval_global_term e.S.env
                              th.Theory.th_known t
                          in
                          Pp.sprintf "@[<hov 2>%a@]" Mlw_interp.print_value t
                        | _ ->
                          Pp.sprintf
                            "Symbol '%s' is not a constant in theory '%s.%s'"
                            i f m
                with Not_found ->
                  Pp.sprintf
                    "Constant '%s' not found in theory '%s.%s'" i f m
              end
            with Not_found ->
              Pp.sprintf "theory '%s.%s' not found" f m;
          with Not_found ->
            Pp.sprintf "@[<hov 2>file '%s' not found. Files are: [%a]@]" f
              (Pp.print_list Pp.comma Pp.string)
              (Mstr.keys files)
        end
      | _ ->
        "must be of the form <filename>.<theory name>.<identifier>";
  in
  result#source_buffer#set_text msg

let constant_to_evaluate = ref ""


(*
let selected_file = ref ""
*)

let evaluate_window () =
  let dialog = GWindow.dialog ~modal:true
    ~title:"Why3: evaluate constant" ~icon:!Gconfig.why_icon ()
  in
  let vbox = dialog#vbox in
  let frame =
    GBin.frame ~label:"Evaluation" ~shadow_type:`ETCHED_OUT
    ~packing:vbox#add ()
  in
  let vbox = GPack.vbox ~packing:frame#add () in
  let text =
    "Enter the constant to evaluate under the form <filename>.<theory name>.<identifier>"
  in
  let _ = GMisc.label ~ypad:20 ~text ~xalign:0.5 ~packing:vbox#add () in
  let exec_entry =
    GEdit.entry ~text:!constant_to_evaluate ~packing:vbox#add ()
  in
  let (_ : GtkSignal.id) =
    exec_entry#connect#changed ~callback:
      (fun () -> constant_to_evaluate := exec_entry#text)
  in
(*
  let hb = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
  let e = env_session () in
  let files_map = e.S.files in
  let (files_combo, _) =
    GEdit.combo_box_entry_text ~packing:hb#pack ()
  in
  let _,file_names =
    Mstr.fold
      (fun f _th (i,names) ->
        if f = !selected_file then files_combo#set_active i;
        (i+1, f::names))
      files_map (0, [])
  in
  let (_store, column) =
    GTree.store_of_list Gobject.Data.string file_names
  in
  files_combo#set_text_column column;
  let ( _ : GtkSignal.id) = files_combo#connect#changed
    ~callback:(fun () ->
      match files_combo#active_iter with
      | None -> ()
      | Some row ->
        let s = files_combo#model#get ~row ~column in
        selected_file := s)
  in
*)
  let b = GButton.button ~label:"Run" ~packing:vbox#add () in
  let text =
    "Result:"
  in
  let _input = GMisc.label ~ypad:20 ~text ~xalign:0.0 ~packing:vbox#add () in
(*
  let _ = input#event#connect#key_press ~callback:
    (fun k -> if GdkEvent.Key.keyval k = GdkKeysyms._Return then
        eval !constant_to_evaluate view;
      true)
  in
*)
 let scroll =
   GBin.scrolled_window
     ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
     ~shadow_type:`ETCHED_OUT ~packing:vbox#add ()
 in
 let view =
   GSourceView2.source_view
     ~editable:false
     ~packing:scroll#add
     ~height:100
     ()
 in
  let (_ : GtkSignal.id) =
    b#connect#clicked ~callback:(fun () -> eval !constant_to_evaluate view)
  in
  dialog#add_button "Close" `CLOSE ;
  let _ = dialog#run () in
  dialog#destroy ()

let (_ : GMenu.image_menu_item) =
  run_factory#add_image_item
    ~label:"Evaluate a logic constant"
    ~callback:evaluate_window
    ()

let function_to_execute = ref ""

let execute_window () =
  let dialog = GWindow.dialog ~modal:true
    ~title:"Why3: execute function" ~icon:!Gconfig.why_icon ()
  in
  let vbox = dialog#vbox in
  let text =
    "Enter the function to execute under the form <module name>.<function name>"
  in
  let _ = GMisc.label ~ypad:20 ~text ~xalign:0.5 ~packing:vbox#add () in
  let exec_entry =
    GEdit.entry ~text:!function_to_execute ~packing:vbox#add ()
  in
  let (_ : GtkSignal.id) =
    exec_entry#connect#changed ~callback:
      (fun () -> function_to_execute := exec_entry#text)
  in
  dialog#add_button "Close" `CLOSE ;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  dialog#destroy ()

(*
let (_ : GMenu.image_menu_item) =
  run_factory#add_image_item
    ~label:"Execute a WhyML function"
    ~callback:execute_window
    ()
*)

*)

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


(***************)
(* source view *)
(***************)

let scrolled_source_view = GBin.scrolled_window
  ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
  ~packing:source_tab#add ~shadow_type:`ETCHED_OUT
  ()

let allow_editing = false (* not reliable enough yet *)

let source_view =
  GSourceView2.source_view
    ~auto_indent:true
    ~insert_spaces_instead_of_tabs:true ~tab_width:2
    ~show_line_numbers:true
    ~right_margin_position:80 ~show_right_margin:true
    (* ~smart_home_end:true *)
    ~editable:allow_editing
    ~packing:scrolled_source_view#add
    ()



(*
  source_view#misc#modify_font_by_name font_name;
*)
let () = modifiable_mono_font_views :=
          source_view#misc :: !modifiable_mono_font_views
let () = change_font (Gconfig.incr_font_size 0)

let () = source_view#source_buffer#set_language None
let () = source_view#set_highlight_current_line true
(*
let () = source_view#source_buffer#set_text (source_text fname)
*)

let set_current_file f =
  current_file := f;
  file_info#set_text ("file: " ^ !current_file)


let move_to_line ~yalign (v : GSourceView2.source_view) line =
  let line = max 0 line in
  let line = min line v#buffer#line_count in
  let it = v#buffer#get_iter (`LINE line) in
  v#buffer#place_cursor ~where:it;
  let mark = `MARK (v#buffer#create_mark it) in
  v#scroll_to_mark ~use_align:true ~yalign mark


let premise_tag = source_view#buffer#create_tag
  ~name:"premise_tag" [`BACKGROUND gconfig.premise_color]

let neg_premise_tag = source_view#buffer#create_tag
  ~name:"neg_premise_tag" [`BACKGROUND gconfig.neg_premise_color]

let goal_tag = source_view#buffer#create_tag
  ~name:"goal_tag" [`BACKGROUND gconfig.goal_color]

let error_tag = source_view#buffer#create_tag
  ~name:"error_tag" [`BACKGROUND gconfig.error_color]

let erase_color_loc (v:GSourceView2.source_view) =
  let buf = v#buffer in
  buf#remove_tag premise_tag ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag neg_premise_tag ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag goal_tag ~start:buf#start_iter ~stop:buf#end_iter;
  buf#remove_tag error_tag ~start:buf#start_iter ~stop:buf#end_iter

let color_loc (v:GSourceView2.source_view) ~color l b e =
  let buf = v#buffer in
  let top = buf#start_iter in
  let start = top#forward_lines (l-1) in
  let start = start#forward_chars b in
  let stop = start#forward_chars (e-b) in
  buf#apply_tag ~start ~stop color

let scroll_to_file f =
  if f <> !current_file then
    begin
      let lang =
        if Filename.check_suffix f ".why" ||
          Filename.check_suffix f ".mlw"
        then why_lang else any_lang f
      in
      source_view#source_buffer#set_language lang;
      source_view#source_buffer#set_text (file_contents f);
      set_current_file f;
    end

let scroll_to_loc ?(yalign=0.0) ~color loc =
  reset_gc ();
  let (f,l,b,e) = Loc.get loc in
  scroll_to_file f;
  move_to_line ~yalign source_view (l-1);
  erase_color_loc source_view;
  (* FIXME: use another color or none at all *)
  color_loc source_view ~color l b e;
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
  Opt.iter (fun loc -> color_loc ~color loc; b := true) f.Term.t_loc;
  Term.t_fold (fun b loc -> color_locs ~color loc || b) !b f

(* FIXME: we shouldn't open binders _every_time_ we redraw screen!!!
   No t_fold, no t_open_quant! *)
let rec color_t_locs f =
  let premise_tag = function
    | { Term. t_node = Term.Tnot _; t_loc = None } -> neg_premise_tag
    | _ -> premise_tag
  in
  match f.Term.t_node with
    | Term.Tbinop (Term.Timplies,f1,f2) ->
        let b = color_locs ~color:(premise_tag f1) f1 in
        color_t_locs f2 || b
    | Term.Tlet (t,fb) ->
        let _,f1 = Term.t_open_bound fb in
        let b = color_locs ~color:(premise_tag t) t in
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
          Opt.iter (color_loc ~color:goal_tag) id.Ident.id_loc
    | _ ->
        assert false

let scroll_to_theory th =
  let id = th.S.theory_name in
  scroll_to_id ~color:goal_tag id


let reload () =
  try
    erase_color_loc source_view;
    current_file := "";
    (* create a new environnement
       (in order to reload the files which are "use") *)
    gconfig.env <- Env.create_env (Env.get_loadpath gconfig.env);
    (* reload the session *)
    let old_session = (env_session()).S.session in
    let new_env_session,(_:bool),(_:bool) =
      (* use_shapes is true since session is in memory *)
      M.update_session ~allow_obsolete:true ~release:false ~use_shapes:true
        old_session gconfig.env gconfig.Gconfig.config
    in
    current_env_session := Some new_env_session;
    display_warnings ()
  with
    | e ->
        begin
          match e with
          | Loc.Located(loc,_) ->
            scroll_to_loc ~color:error_tag ~yalign:0.5 loc;
            notebook#goto_page source_page (* go to "source" tab *)
          | _ -> ()
        end;
        fprintf str_formatter
          "@[Error:@ %a@]" Exn_printer.exn_printer e;
        let msg = flush_str_formatter () in
        file_info#set_text msg;
        info_window `ERROR msg

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
Saving the source_view
*)

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

let () =
  if allow_editing then
    let (_ : GMenu.image_menu_item) =
      file_factory#add_image_item ~key:GdkKeysyms._S
        ~label:"_Save" ~callback:save_file
        ()
    in ()


let (_ : GtkSignal.id) = w#connect#destroy
  ~callback:(exit_function ~destroy:true)

let (_ : GMenu.image_menu_item) =
  file_factory#add_image_item ~key:GdkKeysyms._Q ~label:"_Quit"
    ~callback:(exit_function ~destroy:false) ()


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
        let e = env_session () in
	let cntexample = Whyconf.cntexample (Whyconf.get_main gconfig.config) in
(*
        let coq = { prover_name = "Coq" ; prover_version = "8.3pl3";
                    prover_altern = "" } in
        let c = e.Session.whyconf in
        let p = Mprover.find coq (get_provers c) in
        let time = Whyconf.timelimit (Whyconf.get_main c) in
        Debug.dprintf debug
          "[debug] save_config %d: timelimit=%d ; editor for Coq=%s@."
          0 time p.editor;
*)
        M.edit_proof ~cntexample e sched ~default_editor:gconfig.default_editor a
    | S.Transf _ -> ()
    | S.Metas _ -> ()

let edit_current_proof () =
  match get_selected_row_references () with
    | [] -> ()
    | [r] -> edit_selected_row r
    | _ ->
        info_window `INFO "Please select exactly one proof to edit"

let () =
  add_tool_separator ();
  add_tool_item "Edit current proof" edit_current_proof;
  add_tool_item "Replay selection" replay_obsolete_proofs;
  add_tool_item "Mark as obsolete" cancel_proofs;
  add_tool_item "Mark as archived" (set_archive_proofs true);
  add_tool_item "Remove from archive" (set_archive_proofs false)

let () =
  let b = GButton.button ~packing:tools_box#add ~label:"Edit" () in
  b#misc#set_tooltip_markup
    "Edit the <b>selected proof</b> with the appropriate editor";

  let i = GMisc.image ~pixbuf:(!image_editor) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#clicked ~callback:edit_current_proof
  in ()

let () =
  let b = GButton.button ~packing:tools_box#add ~label:"Replay" () in
  b#misc#set_tooltip_markup
    "Replay <b>obsolete</b> proofs below the current selection";

  let i = GMisc.image ~pixbuf:(!image_replay) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#clicked ~callback:replay_obsolete_proofs
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
          "Do you really want to remove the selected transformation\n\
and all its subgoals?"
    | S.Metas m ->
      info_window
        ~callback:(fun () -> M.remove_metas m)
        `QUESTION
        "Do you really want to remove the selected addition of metas\n\
and all its subgoals?"

let remove_proof r =
  match get_any_from_row_reference r with
    | S.Goal _g -> ()
    | S.Theory _th -> ()
    | S.File _file -> ()
    | S.Proof_attempt a -> M.remove_proof_attempt a
    | S.Transf _tr -> ()
    | S.Metas _m -> ()

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
  add_tool_separator ();
  add_tool_item "Remove current proof" confirm_remove_selection;
  add_tool_item "Clean selection" clean_selection

let () =
  let b = GButton.button ~packing:tools_box#add ~label:"Remove" () in
  b#misc#set_tooltip_markup "Remove selected <b>proof attempts</b> and \
<b>transformations</b>";
  let i = GMisc.image ~pixbuf:(!image_remove) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#clicked ~callback:confirm_remove_selection
  in ()

let () =
  let b = GButton.button ~packing:tools_box#add ~label:"Clean" () in
  b#misc#set_tooltip_markup "Remove unsuccessful <b>proof attempts</b> \
associated to proved goals";
  let i = GMisc.image ~pixbuf:(!image_cleaning) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#clicked ~callback:clean_selection
  in ()

let () =
  let b = GButton.button ~packing:monitor_box#add ~label:"Interrupt" () in
  b#misc#set_tooltip_markup "Cancels all scheduled proof attempts";
  let i = GMisc.image ~pixbuf:(!image_cancel) () in
  let () = b#set_image i#coerce in
  let (_ : GtkSignal.id) =
    b#connect#clicked ~callback:(fun () -> M.cancel_scheduled_proofs sched)
  in ()

(***)

let () =
  add_tool_separator ();
  add_tool_item "Copy" copy_on_selection;
  add_tool_item "Paste" paste_on_selection;
  add_tool_separator ();
  let submenu = tools_factory#add_submenu "Strategies" in
  let submenu = new GMenu.factory submenu ~accel_group in
  let iter (name,desc,strat,k) =
    let desc = Scanf.format_from_string desc "" in
    let callback () = apply_strategy_on_selection strat in
    let ii = submenu#add_image_item
      ~label:(sanitize_markup name) ~callback ()
    in
    let name =
      match k with
        | None -> name
        | Some(s,_) -> name ^ " (shortcut:" ^ s ^ ")"
    in
    ii#misc#set_tooltip_text (string_of_desc (name,desc))
  in
  List.iter iter (strategies ());
  add_tool_separator ();
  let provers_factory =
    let tools_submenu_provers = tools_factory#add_submenu "Provers" in
    new GMenu.factory tools_submenu_provers
  in
  let add_item_provers () =
    let provers = C.get_provers gconfig.Gconfig.config in
    let provers =
      C.Mprover.fold
        (fun k p acc ->
          let pr = p.prover in
          if List.mem (C.prover_parseable_format pr) gconfig.hidden_provers
          then acc
          else C.Mprover.add k p acc)
        provers C.Mprover.empty
    in
    C.Mprover.iter
      (fun p _ ->
         let n = Pp.string_of_wnl C.print_prover p in
         let (_ : GMenu.image_menu_item) =
           provers_factory#add_image_item ~label:n
             ~callback:(fun () -> prover_on_selected_goals p)
             ()
         in
         let b = GButton.button ~packing:provers_box#add ~label:n () in
         b#misc#set_tooltip_markup
           (Pp.sprintf_wnl "Start <tt>%a</tt> on the <b>selected goals</b>"
              C.print_prover p);
         let (_ : GtkSignal.id) =
           b#connect#clicked
             ~callback:(fun () -> prover_on_selected_goals p)
         in ())
      provers
  in
  add_gui_item add_item_provers

(***********************************************)
(* Keyboard shortcuts in the (goals) tree view *)
(***********************************************)

(* TODO:
   - instead of a default prover, have instead keyboard shortcuts for
     any prover *)

let () =
  let run_default_prover () =
    if gconfig.default_prover = "" then
      Debug.dprintf debug "no default prover@." else
    let fp = Whyconf.parse_filter_prover gconfig.default_prover in
    let pr = Whyconf.filter_one_prover gconfig.config fp in
    prover_on_selected_goals pr.prover in
  let callback ev =
    let key = GdkEvent.Key.keyval ev in
    if key = GdkKeysyms._c then begin clean_selection (); true end else
    if key = GdkKeysyms._e then begin edit_current_proof (); true end else
    if key = GdkKeysyms._o then begin cancel_proofs (); true end else
    if key = GdkKeysyms._p then begin run_default_prover (); true end else
    if key = GdkKeysyms._r then begin replay_obsolete_proofs (); true end else
    if key = GdkKeysyms._x then begin confirm_remove_selection (); true end else
    (* strategy shortcuts *)
    let rec iter l =
      match l with
        | [] -> false (* otherwise, use the default event handler *)
        | (_,_,_,None) :: rem -> iter rem
        | (_,_,s,Some(_,k)) :: rem ->
          if key = k then begin apply_strategy_on_selection s; true end else
            iter rem
    in
    iter (strategies ())
  in
  ignore (goals_view#event#connect#key_press ~callback)


(***************)
(* Bind events *)
(***************)

(* to be run when a row in the tree view is selected *)
let select_row r =
  let ind = goals_model#get ~row:r#iter ~column:index_column in
  current_selected_row := Some ind;
  let a = get_any_from_row_reference r in
  update_tabs a;
  match a with
    | S.Goal g ->
      scroll_to_source_goal g
    | S.Theory th ->
      scroll_to_theory th;
      (* notebook#goto_page source_page (* go to "source" tab *)*)
    | S.File file ->
      scroll_to_file (Filename.concat project_dir file.S.file_name);
      (* notebook#goto_page source_page (\* go to "source" tab *\) *)
    | S.Proof_attempt a ->
      scroll_to_source_goal a.S.proof_parent;
      (* notebook#goto_page output_page (\* go to "prover output" tab *\) *)
    | S.Transf tr ->
      scroll_to_source_goal tr.S.transf_parent
    | S.Metas m ->
      scroll_to_source_goal m.S.metas_parent

(* row selection on tree view on the left *)
let (_ : GtkSignal.id) =
  goals_view#selection#connect#after#changed ~callback:
    begin fun () ->
      match get_selected_row_references () with
        | [p] -> select_row p
        | [] -> ()
        | _ -> ()
    end

let (_:GtkSignal.id) =
  goals_view#connect#row_collapsed ~callback:(row_expanded false)

let (_:GtkSignal.id) =
  goals_view#connect#row_expanded ~callback:(row_expanded true)

(*
let () = Debug.set_flag (Debug.lookup_flag "transform")
*)

let () = display_warnings ()

let () = GMain.main ()

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
