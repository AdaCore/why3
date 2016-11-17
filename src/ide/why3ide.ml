
open Format
open Why3
open Gconfig
open Stdlib
open Session_itp
open Controller_itp
open Session_user_interface
open Historic

external reset_gc : unit -> unit = "ml_reset_gc"

let debug = Debug.lookup_flag "ide_info"

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

let task_driver =
  let main = Whyconf.get_main gconfig.config in
  let d = Filename.concat (Whyconf.datadir main)
                          (Filename.concat "drivers" "why3_itp.drv")
  in
  Driver.load_driver gconfig.env d []


let provers : Whyconf.config_prover Whyconf.Mprover.t =
  Whyconf.get_provers gconfig.config

let cont =
  Session_user_interface.cont_from_files spec usage_str gconfig.env files provers

let () =
  Debug.dprintf debug "[GUI] Init the GTK interface...@?";
  ignore (GtkMain.Main.init ());
  Debug.dprintf debug " done.@.";
  Gconfig.init ()


(**********************)
(* Graphical elements *)
(**********************)

let main_window =
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
   1. the menu
   2. an horizontal box
 *)

let vbox = GPack.vbox ~packing:main_window#add ()

let menubar = GMenu.menu_bar
  ~packing:(vbox#pack ?from:None ?expand:None ?fill:None ?padding:None)
  ()

let hb = GPack.hbox ~packing:vbox#add ()

(* 1. Menu *)

let factory = new GMenu.factory menubar

let accel_group = factory#accel_group

(* 1.1 "File" menu *)

let file_menu = factory#add_submenu "_File"
let file_factory = new GMenu.factory file_menu ~accel_group

let exit_function ~destroy () =
  ignore(destroy); GMain.quit ()

let (_ : GtkSignal.id) = main_window#connect#destroy
  ~callback:(exit_function ~destroy:true)

let (_ : GMenu.menu_item) =
  file_factory#add_item ~key:GdkKeysyms._S "_Save session"
    ~callback:(fun () -> Session_itp.save_session cont.Controller_itp.controller_session)

let (replay_menu_item : GMenu.menu_item) =
  file_factory#add_item ~key:GdkKeysyms._R "_Replay all"

let (_ : GMenu.menu_item) =
  file_factory#add_item ~key:GdkKeysyms._Q "_Quit"
    ~callback:(exit_function ~destroy:false)


(* 1.2 "View" menu

   the entries in that menu are defined later

*)

(* 2. horizontal box contains:
   2.1 TODO: a tool box ?
   2.2 a horizontal paned containing:
     2.2.1 a scrolled window to hold the tree view of the session
     2.2.2 a vertical paned containing
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

let vpan222 = GPack.paned `VERTICAL ~packing:hp#add ()

(*  the scrolled window 2.2.1 contains a GTK tree

*)


(* view for the session tree *)
let scrolled_session_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:scrollview#add
    ()

let cols = new GTree.column_list
let name_column = cols#add Gobject.Data.string
let index_column = cols#add Gobject.Data.int
let status_column = cols#add Gobject.Data.gobject

let name_renderer = GTree.cell_renderer_text [`XALIGN 0.]
let view_name_column = GTree.view_column ~title:"Theories/Goals" ()
let () =
  view_name_column#pack name_renderer;
  view_name_column#add_attribute name_renderer "text" name_column;
  view_name_column#set_sizing `AUTOSIZE

let status_renderer = GTree.cell_renderer_pixbuf [ ]
let view_status_column = GTree.view_column ~title:"Status"
    ~renderer:(status_renderer, ["pixbuf", status_column])()

let goals_model,goals_view =
  Debug.dprintf debug "[GUI] Creating tree model...@?";
  let model = GTree.tree_store cols in
  let view = GTree.view ~model ~packing:scrolled_session_view#add () in
(*
  let () = view#selection#set_mode (* `SINGLE *) `MULTIPLE in
  let () = view#set_rules_hint true in
 *)
  ignore (view#append_column view_name_column);
  ignore (view#append_column view_status_column);
(*
  ignore (view#append_column view_status_column);
  ignore (view#append_column view_time_column);
*)
  Debug.dprintf debug " done@.";
  model,view

(* vpan222 contains:
   2.2.2.1 a view of the current task
   2.2.2.2 a vertiacal pan which contains
     2.2.2.2.1 the input field to type commands
     2.2.2.2.2 a scrolled window to hold the output of the commands
 *)

let scrolled_task_view =
  GBin.scrolled_window
    ~hpolicy: `AUTOMATIC ~vpolicy: `AUTOMATIC
    ~shadow_type:`ETCHED_OUT
    ~packing:vpan222#add ()

let task_view =
  GSourceView2.source_view
    ~editable:false
    ~cursor_visible:false
    ~show_line_numbers:true
    ~packing:scrolled_task_view#add
    ()

let vbox2222 = GPack.vbox ~packing:vpan222#add  ()

let hbox22221 =
  GPack.hbox
    ~packing:(vbox2222#pack ?from:None ?expand:None ?fill:None ?padding:None) ()

let monitor =
  GMisc.label
    ~text:"  0/0/0"
    ~width:80
    ~xalign:0.0
    ~packing:(hbox22221#pack ?from:None ?expand:None ?fill:None ?padding:None) ()

let command_entry = GEdit.entry ~packing:hbox22221#add ()

let message_zone =
  let sv = GBin.scrolled_window
      ~hpolicy:`AUTOMATIC ~vpolicy:`AUTOMATIC
      ~shadow_type:`ETCHED_OUT ~packing:vbox2222#add ()
  in
  GText.view ~editable:false ~cursor_visible:false
    ~packing:sv#add ()

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


(*******************************)
(* commands of the "View" menu *)
(*******************************)

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

let (_ : GMenu.image_menu_item) =
  view_factory#add_image_item ~key:GdkKeysyms._E
    ~label:"Expand all" ~callback:(fun () -> goals_view#expand_all ()) ()


let () =
  Gconfig.add_modifiable_sans_font_view goals_view#misc;
  Gconfig.add_modifiable_mono_font_view monitor#misc;
  Gconfig.add_modifiable_mono_font_view task_view#misc;
  Gconfig.add_modifiable_mono_font_view command_entry#misc;
  Gconfig.add_modifiable_mono_font_view message_zone#misc;
  Gconfig.set_fonts ()

let image_of_result ~obsolete rOpt =
  match rOpt with
  | None -> !image_undone
  | Some r ->
    match r.Call_provers.pr_answer with
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

let image_of_pa_status ~obsolete pa_status =
  match pa_status with
    | Controller_itp.Interrupted -> !image_undone
    | Controller_itp.Unedited -> !image_editor
    | Controller_itp.JustEdited -> !image_unknown
    | Controller_itp.Scheduled -> !image_scheduled
    | Controller_itp.Running -> !image_running
    | Controller_itp.InternalFailure _
    | Controller_itp.Uninstalled _ -> !image_failure
    | Controller_itp.Done r -> image_of_result ~obsolete (Some r)

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

let init_comp () =
  (* add the names of all the the transformations *)
  List.iter add_completion_entry (Trans.list_trans ());
  (* add the name of the commands *)
  List.iter (fun (c,_,_) -> add_completion_entry c)
    Session_user_interface.commands;
  (* todo: add queries *)

  command_entry_completion#set_text_column completion_col;

  command_entry#set_completion command_entry_completion




(*********************)
(* Terminal historic *)
(*********************)

let list_commands = create_historic()

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

(********************************************)
(* controller instance on the GTK scheduler *)
(********************************************)


module S = struct
    let idle ~prio f =
      let (_ : GMain.Idle.id) = GMain.Idle.add ~prio f in ()

    let timeout ~ms f =
      let (_ : GMain.Timeout.id) = GMain.Timeout.add ~ms ~callback:f in
      ()
end

module C = Controller_itp.Make(S)

let () =
  let n = gconfig.session_nb_processes in
  Debug.dprintf debug "[IDE] setting max proof tasks to %d@." n;
  C.set_max_tasks n;
  C.register_observer update_monitor

let (_ : GtkSignal.id) =
  replay_menu_item#connect#activate
    ~callback:(fun () ->
               let callback = C.replay_print in
               C.replay ~use_steps:false cont ~callback ~remove_obsolete:false)


(***********************************)
(* Mapping session to the GTK tree *)
(***********************************)

type index =
  | Inone
  | IproofAttempt of proofAttemptID
  | IproofNode of proofNodeID
  | Itransformation  of transID
  | Ifile of file
  | Itheory of theory

let model_index : index Hint.t = Stdlib.Hint.create 17
(* To each proofnodeid we have the corresponding row_reference *)
let pn_id_to_gtree : GTree.row_reference Hpn.t = Hpn.create 17
let pan_id_to_gtree : GTree.row_reference Hpan.t = Hpan.create 17

let set_status_column_from_cont cont iter =
  let index = goals_model#get ~row:iter ~column:index_column in
  let index = Hint.find model_index index in
  let image = match index with
    | Inone -> assert false
    | IproofAttempt panid ->
      let pa = get_proof_attempt_node cont.controller_session panid in
      image_of_result ~obsolete:pa.proof_obsolete pa.Session_itp.proof_state
    | IproofNode pn ->
      if pn_proved cont pn
      then !image_valid
      else !image_unknown
    | Itransformation tn -> if tn_proved cont tn
      then !image_valid
      else !image_unknown
    | Ifile _ -> !image_file
    | Itheory th -> if th_proved cont th
      then !image_valid
      else !image_unknown
  in
  goals_model#set ~row:iter ~column:status_column image

let new_node =
  let cpt = ref (-1) in
  fun ?parent ?(collapse=false) name ind ->
  incr cpt;
  Hint.add model_index !cpt ind;
  let parent = Opt.map (fun x -> x#iter) parent in
  let iter = goals_model#append ?parent () in
  goals_model#set ~row:iter ~column:name_column name;
  goals_model#set ~row:iter ~column:index_column !cpt;
  let new_ref = goals_model#get_row_reference (goals_model#get_path iter) in
  (* By default expand_path when creating a new node *)
  if not collapse then goals_view#expand_to_path (goals_model#get_path iter);
  begin
    match ind with
    | IproofAttempt panid ->
       Hpan.add pan_id_to_gtree panid new_ref
    | IproofNode pnid ->
       Hpn.add pn_id_to_gtree pnid new_ref
    | _ -> ()
  end;
  new_ref

let build_subtree_proof_attempt_from_goal cont row_ref id =
  Whyconf.Hprover.iter
    (fun pa panid ->
       let name = Pp.string_of Whyconf.print_prover pa in
       let r = new_node ~parent:row_ref name (IproofAttempt panid) in
       set_status_column_from_cont cont r#iter)
    (get_proof_attempt_ids cont.controller_session id)

let rec build_subtree_from_goal cont th_row_reference id =
  let ses = cont.controller_session in
  let name = get_proof_name ses id in
  let row_ref =
    new_node ~parent:th_row_reference name.Ident.id_string
             (IproofNode id)
  in
  set_status_column_from_cont cont row_ref#iter;
  List.iter
    (fun trans_id ->
      ignore (build_subtree_from_trans cont row_ref trans_id))
    (get_transformations ses id);
  build_subtree_proof_attempt_from_goal cont row_ref id

and build_subtree_from_trans cont goal_row_reference trans_id =
  let ses = cont.controller_session in
  let name = get_transf_name ses trans_id in
  let row_ref =
    new_node ~parent:goal_row_reference name (Itransformation trans_id) in
  set_status_column_from_cont cont row_ref#iter;
  List.iter
    (fun goal_id ->
      (build_subtree_from_goal cont row_ref goal_id))
    (get_sub_tasks ses trans_id);
  row_ref

let build_tree_from_session cont =
  let ses = cont.controller_session in
  let files = get_files ses in
  Stdlib.Hstr.iter
    (fun _ file ->
       let file_row_reference = new_node file.file_name (Ifile file) in
       set_status_column_from_cont cont file_row_reference#iter;
       List.iter (fun th ->
                  let th_row_reference =
                    new_node ~parent:file_row_reference
                             (theory_name th).Ident.id_string
                             (Itheory th)
                  in
                  set_status_column_from_cont cont th_row_reference#iter;
                  List.iter (build_subtree_from_goal cont th_row_reference)
                            (theory_goals th))
                 file.file_theories)
    files

(******************)
(*    actions     *)
(******************)

(* TODO We currently use this for transformations etc... With strategies, we sure
   do not want to move the current index with the computing of strategy. *)
let current_selected_index = ref Inone

let rec update_status_column_from cont iter =
  set_status_column_from_cont cont iter;
  match goals_model#iter_parent iter with
  | Some p -> update_status_column_from cont p
  | None -> ()

(* Callback of a transformation *)
let callback_update_tree_transform cont status =
  match status with
  | TSdone trans_id ->
    let ses = cont.controller_session in
    let id = get_trans_parent ses trans_id in
    let row_ref = Hpn.find pn_id_to_gtree id in (* TODO exception *)
    let r = build_subtree_from_trans cont row_ref trans_id in
    update_status_column_from cont r#iter;
    (match Session_itp.get_sub_tasks ses trans_id with
     | first_goal :: _ ->
       (* Put the selection on the first goal *)
       goals_view#selection#select_iter (Hpn.find pn_id_to_gtree first_goal)#iter
     | [] -> ())
  | _ -> ()

let apply_transform cont t args =
  match !current_selected_index with
  | IproofNode id ->
     let callback = callback_update_tree_transform cont in
    C.schedule_transformation cont id t args ~callback
  | _ -> printf "Error: Give the name of the transformation@."

(* Callback of a proof_attempt *)
let callback_update_tree_proof cont panid pa_status =
  let ses = cont.controller_session in
  let pa = get_proof_attempt_node ses panid in
  let prover = pa.prover in
  let name = Pp.string_of Whyconf.print_prover prover in
  let obsolete = pa.proof_obsolete in
  let r = match pa_status with
  | Scheduled ->
     begin
       try
         Hpan.find pan_id_to_gtree panid
       with Not_found ->
         let parent_id = get_proof_attempt_parent ses panid in
         let parent = Hpn.find pn_id_to_gtree parent_id in
         new_node ~parent name (IproofAttempt panid)
     end
  | Done _ ->
    let r = Hpan.find pan_id_to_gtree panid in
    begin match goals_model#iter_parent r#iter with
    | Some iter -> update_status_column_from cont iter
    | None -> ()
    end;
    r
  | _  -> Hpan.find pan_id_to_gtree panid (* TODO ? *)
  in
  goals_model#set ~row:r#iter ~column:status_column
    (image_of_pa_status ~obsolete pa_status)

let test_schedule_proof_attempt cont (p: Whyconf.config_prover) limit =
  match !current_selected_index with
  | IproofNode id ->
    let prover = p.Whyconf.prover in
    let callback = callback_update_tree_proof cont in
    C.schedule_proof_attempt cont id prover ~limit ~callback
  | _ -> message_zone#buffer#set_text ("Must be on a proof node to use a prover.")


let run_strategy_on_task s =
  match !current_selected_index with
  | IproofNode id ->
     let l = Session_user_interface.strategies
               cont.controller_env gconfig.config
     in
     let st = List.filter (fun (_,c,_,_) -> c=s) l in
     begin
       match st with
       | [(n,_,_,st)] ->
          printf "running strategy '%s'@." n;
          let callback sts =
            printf "Strategy status: %a@." print_strategy_status sts
          in
          let callback_pa =
            callback_update_tree_proof cont
          in
          let callback_tr st =
            callback_update_tree_transform cont st
          in
          C.run_strategy_on_goal cont id st ~callback_pa ~callback_tr ~callback
    | _ -> printf "Strategy '%s' not found@." s
     end
  | _ -> (
)

let clear_command_entry () = command_entry#set_text ""

let interp cmd =
  let id =
    match !current_selected_index with
    | IproofNode id -> Some id
    | _ -> None
  in
  try
  match interp cont id cmd with
    | Transform(s,_t,args) ->
       clear_command_entry ();
       apply_transform cont s args
    | Query s ->
       clear_command_entry ();
       message_zone#buffer#set_text s
    | Other(s,args) ->
      begin
        match parse_prover_name gconfig.config s args with
        | Some (prover_config, limit) ->
          clear_command_entry ();
          test_schedule_proof_attempt cont prover_config limit
        | None ->
          match s with
          | "auto" ->
             let s =
               match args with
               | "2"::_ -> "2"
               | _ -> "1"
             in
             clear_command_entry ();
             run_strategy_on_task s
          | "help" ->
             clear_command_entry ();
             let text = Pp.sprintf
                          "Please type a command among the following (automatic completion available)@\n\
                           @\n\
                           @ <transformation name> [arguments]@\n\
                           @ <prover name> [<time limit> [<mem limit>]]@\n\
                           @ <query> [arguments]@\n\
                           @ auto [auto level]@\n\
                           @\n\
                           Available queries are:@\n@[%a@]" help_on_queries ()
             in
             message_zone#buffer#set_text text
          | _ ->
             message_zone#buffer#set_text ("unknown command '"^s^"'")
      end
  with e when not (Debug.test_flag Debug.stack_trace) ->
       message_zone#buffer#set_text (Pp.sprintf "anomaly: %a" Exn_printer.exn_printer e)

let (_ : GtkSignal.id) =
  command_entry#connect#activate
    ~callback:(fun () -> add_command list_commands command_entry#text; interp command_entry#text)


let get_selected_row_references () =
  List.map
    (fun path -> goals_model#get_row_reference path)
    goals_view#selection#get_selected_rows

let on_selected_row r =
  let index = goals_model#get ~row:r#iter ~column:index_column in
  try
    let session_element = Hint.find model_index index in
(*
    let () = match session_element with
             | IproofNode id -> Hpn.add pn_id_to_gtree id r (* TODO maybe not the good place to fill
                                                                    this table *)
             | _ -> () in
 *)
    current_selected_index := session_element;
    match session_element with
    | IproofNode id ->
       let task = get_task cont.controller_session id in
       let s = Pp.string_of
                 (Driver.print_task ~cntexample:false task_driver)
                 task
       in task_view#source_buffer#set_text s;
       (* scroll to end of text *)
       task_view#scroll_to_mark `INSERT
    | _ -> task_view#source_buffer#set_text ""
  with
    | Not_found -> task_view#source_buffer#set_text ""

let (_ : GtkSignal.id) =
  goals_view#selection#connect#after#changed ~callback:
    (fun () ->
      match get_selected_row_references () with
        | [r] -> on_selected_row r
        | _ -> ())

(***********************)
(* start the interface *)
(***********************)

let () =
  build_tree_from_session cont;
  (* temporary *)
  init_comp ();
  vpan222#set_position 500;
  goals_view#expand_all ();
  main_window#add_accel_group accel_group;
  main_window#set_icon (Some !Gconfig.why_icon);
  message_zone#buffer#set_text "Welcome to Why3 IDE\ntype 'help' for help";
  main_window#show ();
  GMain.main ()
