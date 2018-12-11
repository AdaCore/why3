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

open Why3
open Rc
open Whyconf

let debug = Debug.register_info_flag "ide_info"
  ~desc:"Print@ why3ide@ debugging@ messages."

(** set the exception call back handler to the Exn_printer of why3 *)
let () = (***** TODO TODO make that work, it seems not called!!! *)
  let why3_handler exn =
    Format.eprintf "@[Why3ide callback raised an exception:@\n%a@]@.@."
      Exn_printer.exn_printer exn;
    (* print the stack trace if asked to (can't be done by the usual way) *)
    if Debug.test_flag Debug.stack_trace then
      Printf.eprintf "Backtrace:\n%t\n%!" Printexc.print_backtrace
  in
  GtkSignal.user_handler := why3_handler

(* config file *)

type t =
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
      mutable font_size : int;
      mutable current_tab : int;
      mutable verbose : int;
      mutable show_full_context : bool;
      mutable show_attributes : bool;
      mutable show_coercions : bool;
      mutable show_locs : bool;
      mutable show_time_limit : bool;
      mutable max_boxes : int;
      mutable allow_source_editing : bool;
      mutable saving_policy : int;
      (** 0 = always, 1 = never, 2 = ask *)
      mutable premise_color : string;
      mutable neg_premise_color : string;
      mutable goal_color : string;
      mutable error_color : string;
      mutable error_color_bg : string;
      mutable error_line_color : string;
      mutable iconset : string;
      (** colors *)
      mutable config : Whyconf.config;
      original_config : Whyconf.config;
      (* mutable altern_provers : altern_provers; *)
      (* mutable replace_prover : conf_replace_prover; *)
      mutable hidden_provers : string list;
      mutable session_time_limit : int;
      mutable session_mem_limit : int;
      mutable session_nb_processes : int;
    }


type ide = {
  ide_window_width : int;
  ide_window_height : int;
  ide_tree_width : int;
  ide_task_height : int;
  ide_font_size : int;
  ide_current_tab : int;
  ide_verbose : int;
  ide_show_full_context : bool;
  ide_show_attributes : bool;
  ide_show_coercions : bool;
  ide_show_locs : bool;
  ide_show_time_limit : bool;
  ide_max_boxes : int;
  ide_allow_source_editing : bool;
  ide_saving_policy : int;
  ide_premise_color : string;
  ide_neg_premise_color : string;
  ide_goal_color : string;
  ide_error_color : string;
  ide_error_color_bg : string;
  ide_error_line_color : string;
  ide_iconset : string;
  (* ide_replace_prover : conf_replace_prover; *)
  ide_hidden_provers : string list;
}

let default_ide =
  { ide_window_width = 1024;
    ide_window_height = 768;
    ide_tree_width = 512;
    ide_task_height = 400;
    ide_font_size = 10;
    ide_current_tab = 0;
    ide_verbose = 0;
    ide_show_full_context = false;
    ide_show_attributes = false;
    ide_show_coercions = true;
    ide_show_locs = false;
    ide_show_time_limit = false;
    ide_max_boxes = 16;
    ide_allow_source_editing = true;
    ide_saving_policy = 2;
    ide_premise_color = "chartreuse";
    ide_neg_premise_color = "pink";
    ide_goal_color = "gold";
    ide_error_color_bg = "yellow";
    ide_error_color = "red";
    ide_error_line_color = "yellow";
    ide_iconset = "fatcow";
    ide_hidden_provers = [];
  }

let load_ide section =
  { ide_window_width =
      get_int section ~default:default_ide.ide_window_width "window_width";
    ide_window_height =
      get_int section ~default:default_ide.ide_window_height "window_height";
    ide_tree_width =
      get_int section ~default:default_ide.ide_tree_width "tree_width";
    ide_task_height =
      get_int section ~default:default_ide.ide_task_height "task_height";
    ide_current_tab =
      get_int section ~default:default_ide.ide_current_tab "current_tab";
    ide_font_size =
      get_int section ~default:default_ide.ide_font_size "font_size";
    ide_verbose =
      get_int section ~default:default_ide.ide_verbose "verbose";
    ide_show_full_context =
      get_bool section ~default:default_ide.ide_show_full_context
        "show_full_context";
    ide_show_attributes =
      get_bool section ~default:default_ide.ide_show_attributes "print_attributes";
    ide_show_coercions =
      get_bool section ~default:default_ide.ide_show_attributes "print_coercions";
    ide_show_locs =
      get_bool section ~default:default_ide.ide_show_locs "print_locs";
    ide_show_time_limit =
      get_bool section ~default:default_ide.ide_show_time_limit
        "print_time_limit";
    ide_max_boxes =
      get_int section ~default:default_ide.ide_max_boxes
        "max_boxes";
    ide_allow_source_editing =
      get_bool section ~default:default_ide.ide_allow_source_editing "allow_source_editing";
    ide_saving_policy =
      get_int section ~default:default_ide.ide_saving_policy "saving_policy";
    ide_premise_color =
      get_string section ~default:default_ide.ide_premise_color
        "premise_color";
    ide_neg_premise_color =
      get_string section ~default:default_ide.ide_neg_premise_color
        "neg_premise_color";
    ide_goal_color =
      get_string section ~default:default_ide.ide_goal_color
        "goal_color";
    ide_error_color =
      get_string section ~default:default_ide.ide_error_color
        "error_color";
    ide_error_color_bg =
      get_string section ~default:default_ide.ide_error_color_bg
        "error_color_bg";
    ide_error_line_color =
      get_string section ~default:default_ide.ide_error_line_color
        "error_line_color";
    ide_iconset =
      get_string section ~default:default_ide.ide_iconset
        "iconset";
    ide_hidden_provers = get_stringl ~default:default_ide.ide_hidden_provers section "hidden_prover";
  }


let set_attr_flag =
  let fl = Debug.lookup_flag "print_attributes" in
  fun b ->
    (if b then Debug.set_flag else Debug.unset_flag) fl

let set_coercions_flag =
  let fl = Debug.lookup_flag "print_coercions" in
  fun b ->
    (if b then Debug.set_flag else Debug.unset_flag) fl

let set_locs_flag =
  let fl = Debug.lookup_flag "print_locs" in
  fun b ->
    (if b then Debug.set_flag else Debug.unset_flag) fl

let load_config config original_config =
  let main = get_main config in
  let ide  = match Whyconf.get_section config "ide" with
    | None -> default_ide
    | Some s -> load_ide s
  in
  set_attr_flag ide.ide_show_attributes;
  set_coercions_flag ide.ide_show_coercions;
  set_locs_flag ide.ide_show_locs;
  { window_height = ide.ide_window_height;
    window_width  = ide.ide_window_width;
    tree_width    = ide.ide_tree_width;
    task_height   = ide.ide_task_height;
    current_tab   = ide.ide_current_tab;
    font_size     = ide.ide_font_size;
    verbose       = ide.ide_verbose;
    show_full_context= ide.ide_show_full_context ;
    show_attributes   = ide.ide_show_attributes ;
    show_coercions = ide.ide_show_coercions ;
    show_locs     = ide.ide_show_locs ;
    show_time_limit = ide.ide_show_time_limit;
    max_boxes = ide.ide_max_boxes;
    allow_source_editing = ide.ide_allow_source_editing ;
    saving_policy = ide.ide_saving_policy ;
    premise_color = ide.ide_premise_color;
    neg_premise_color = ide.ide_neg_premise_color;
    goal_color = ide.ide_goal_color;
    error_color = ide.ide_error_color;
    error_color_bg = ide.ide_error_color_bg;
    error_line_color = ide.ide_error_line_color;
    iconset = ide.ide_iconset;
    config         = config;
    original_config = original_config;
    hidden_provers = ide.ide_hidden_provers;
    session_time_limit = Whyconf.timelimit main;
    session_mem_limit = Whyconf.memlimit main;
    session_nb_processes = Whyconf.running_provers_max main;
}

let save_config t =
  Debug.dprintf debug "[config] saving IDE config file@.";
  (* taking original config, without the extra_config *)
  let config = t.original_config in
  (* copy possibly modified settings to original config *)
  let new_main = Whyconf.get_main t.config in
  let time = Whyconf.timelimit new_main in
  let mem = Whyconf.memlimit new_main in
  let nb = Whyconf.running_provers_max new_main in
  let main = get_main config in
  let main = set_limits main time mem nb in
  let main = set_default_editor main (Whyconf.default_editor new_main) in
  let config = set_main config main in
  (* copy also provers section since it may have changed (the editor
     can be set via the preferences dialog) *)
  let config = set_provers config (get_provers t.config) in
  (* copy also the possibly changed policies *)
  let config = set_policies config (get_policies t.config) in
  let ide = empty_section in
  let ide = set_int ide "window_height" t.window_height in
  let ide = set_int ide "window_width" t.window_width in
  let ide = set_int ide "tree_width" t.tree_width in
  let ide = set_int ide "task_height" t.task_height in
  let ide = set_int ide "current_tab" t.current_tab in
  let ide = set_int ide "font_size" t.font_size in
  let ide = set_int ide "verbose" t.verbose in
  let ide = set_bool ide "show_full_context" t.show_full_context in
  let ide = set_bool ide "print_attributes" t.show_attributes in
  let ide = set_bool ide "print_coercions" t.show_coercions in
  let ide = set_bool ide "print_locs" t.show_locs in
  let ide = set_bool ide "print_time_limit" t.show_time_limit in
  let ide = set_int ide "max_boxes" t.max_boxes in
  let ide = set_bool ide "allow_source_editing" t.allow_source_editing in
  let ide = set_int ide "saving_policy" t.saving_policy in
  let ide = set_string ide "premise_color" t.premise_color in
  let ide = set_string ide "neg_premise_color" t.neg_premise_color in
  let ide = set_string ide "goal_color" t.goal_color in
  let ide = set_string ide "error_color" t.error_color in
  let ide = set_string ide "error_color_bg" t.error_color_bg in
  let ide = set_string ide "error_line_color" t.error_line_color in
  let ide = set_string ide "iconset" t.iconset in
  let ide = set_stringl ide "hidden_prover" t.hidden_provers in
  let config = Whyconf.set_section config "ide" ide in
  Whyconf.save_config config

let config,load_config =
  let config = ref None in
  (fun () ->
    match !config with
      | None -> invalid_arg "configuration not yet loaded"
      | Some conf -> conf),
  (fun conf base_conf ->
    let c = load_config conf base_conf in
    config := Some c)

let save_config () = save_config (config ())

let get_main () = (get_main (config ()).config)

(*


  font size


 *)


let sans_font_family = "Sans"
let mono_font_family = "Monospace"

let modifiable_sans_font_views = ref []
let modifiable_mono_font_views = ref []

let add_modifiable_sans_font_view v =
  modifiable_sans_font_views := v :: !modifiable_sans_font_views

let add_modifiable_mono_font_view v =
  modifiable_mono_font_views := v :: !modifiable_mono_font_views

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

let incr_font_size n =
  let c = config () in
  let s = max (c.font_size + n) 4 in
  c.font_size <- s;
  s

let enlarge_fonts () = change_font (incr_font_size 1)

let reduce_fonts () = change_font (incr_font_size (-1))

let set_fonts () = change_font (incr_font_size 0)

(*

  images, icons

*)

let image_default = ref (GdkPixbuf.create ~width:1 ~height:1 ())
(* dumb pixbuf *)
let image_undone = ref !image_default
let image_scheduled = ref !image_default
let image_running = ref !image_default
let image_valid = ref !image_default
let image_unknown = ref !image_default
let image_invalid = ref !image_default
let image_timeout = ref !image_default
let image_outofmemory = ref !image_default
let image_steplimitexceeded = ref !image_default
let image_failure = ref !image_default
let image_valid_obs = ref !image_default
let image_unknown_obs = ref !image_default
let image_invalid_obs = ref !image_default
let image_timeout_obs = ref !image_default
let image_outofmemory_obs = ref !image_default
let image_steplimitexceeded_obs = ref !image_default
let image_failure_obs = ref !image_default
let image_yes = ref !image_default
let image_no = ref !image_default
let image_file = ref !image_default
let image_theory = ref !image_default
let image_goal = ref !image_default
let image_prover = ref !image_default
let image_transf = ref !image_default
let image_metas = ref !image_default
let image_editor = ref !image_default
let image_replay = ref !image_default
let image_cancel = ref !image_default
let image_reload = ref !image_default
let image_remove = ref !image_default
let image_cleaning = ref !image_default

let why_icon = ref !image_default

let image ?size f =
  let main = get_main () in
  let n =
    Filename.concat (datadir main)
      (Filename.concat "images" (f^".png"))
  in
  try (
  match size with
    | None ->
        GdkPixbuf.from_file n
    | Some s ->
        GdkPixbuf.from_file_at_size ~width:s ~height:s n
  ) with _ -> !image_default

let iconname_default = ref ""
let iconname_undone = ref ""
let iconname_scheduled = ref ""
let iconname_running = ref ""
let iconname_valid = ref ""
let iconname_unknown = ref ""
let iconname_invalid = ref ""
let iconname_timeout = ref ""
let iconname_outofmemory = ref ""
let iconname_steplimitexceeded = ref ""
let iconname_failure = ref ""
let iconname_valid_obs = ref ""
let iconname_unknown_obs = ref ""
let iconname_invalid_obs = ref ""
let iconname_timeout_obs = ref ""
let iconname_outofmemory_obs = ref ""
let iconname_steplimitexceeded_obs = ref ""
let iconname_failure_obs = ref ""
let iconname_yes = ref ""
let iconname_no = ref ""
let iconname_file = ref ""
let iconname_theory = ref ""
let iconname_goal = ref ""
let iconname_prover = ref ""
let iconname_transf = ref ""
let iconname_metas  = ref ""
let iconname_editor = ref ""
let iconname_replay = ref ""
let iconname_cancel = ref ""
let iconname_reload = ref ""
let iconname_remove = ref ""
let iconname_cleaning = ref ""

let iconsets () : (string * Why3.Rc.family) =
  let main = get_main () in
  let dir = Filename.concat (datadir main) "images" in
  let files = Sys.readdir dir in
  let f = ref [] in
  Array.iter
    (fun fn ->
       if Filename.check_suffix fn ".rc" then
         let n = Filename.concat dir fn in
         let d = Rc.from_file n in
         f := List.rev_append (Rc.get_family d "iconset") !f)
    files;
  (dir, !f)

let load_icon_names () =
  let ide = config () in
  let iconset = ide.iconset in
  let _,iconsets = iconsets () in
  let iconset,d =
    try
      iconset, List.assoc iconset iconsets
    with Not_found ->
      try
        "fatcow", List.assoc "fatcow" iconsets
      with Not_found ->
        failwith "No icon set found"
  in
  let get_icon_name n =
    Filename.concat iconset (get_string ~default:"default" d n)
  in
  iconname_default := get_icon_name "default";
  iconname_undone := get_icon_name "undone";
  iconname_scheduled := get_icon_name "scheduled";
  iconname_running := get_icon_name "running";
  iconname_valid := get_icon_name "valid";
  iconname_unknown := get_icon_name "unknown";
  iconname_invalid := get_icon_name "invalid";
  iconname_timeout := get_icon_name "timeout";
  iconname_outofmemory := get_icon_name "outofmemory";
  iconname_steplimitexceeded := get_icon_name "steplimitexceeded";
  iconname_failure := get_icon_name "failure";
  iconname_valid_obs := get_icon_name "valid_obs";
  iconname_unknown_obs := get_icon_name "unknown_obs";
  iconname_invalid_obs := get_icon_name "invalid_obs";
  iconname_timeout_obs := get_icon_name "timeout_obs";
  iconname_outofmemory_obs := get_icon_name "outofmemory_obs";
  iconname_steplimitexceeded_obs := get_icon_name "steplimitexceeded_obs";
  iconname_failure_obs := get_icon_name "failure_obs";
  iconname_yes := get_icon_name "yes";
  iconname_no := get_icon_name "no";
  iconname_file := get_icon_name "file";
  iconname_theory := get_icon_name "theory";
  iconname_goal := get_icon_name "goal";
  iconname_prover := get_icon_name "prover";
  iconname_transf := get_icon_name "transf";
  iconname_metas  := get_icon_name "metas";
  iconname_editor := get_icon_name "editor";
  iconname_replay := get_icon_name "replay";
  iconname_cancel := get_icon_name "cancel";
  iconname_reload := get_icon_name "reload";
  iconname_remove := get_icon_name "remove";
  iconname_cleaning := get_icon_name "cleaning";
  ()

let resize_images size =
  image_default := image ~size !iconname_default;
  image_undone := image ~size !iconname_undone;
  image_scheduled := image ~size !iconname_scheduled;
  image_running := image ~size !iconname_running;
  image_valid := image ~size !iconname_valid;
  image_unknown := image ~size !iconname_unknown;
  image_invalid := image ~size !iconname_invalid;
  image_timeout := image ~size !iconname_timeout;
  image_outofmemory := image ~size !iconname_outofmemory;
  image_steplimitexceeded := image ~size !iconname_steplimitexceeded;
  image_failure := image ~size !iconname_failure;
  image_valid_obs := image ~size !iconname_valid_obs;
  image_unknown_obs := image ~size !iconname_unknown_obs;
  image_invalid_obs := image ~size !iconname_invalid_obs;
  image_timeout_obs := image ~size !iconname_timeout_obs;
  image_outofmemory_obs := image ~size !iconname_outofmemory_obs;
  image_steplimitexceeded_obs := image ~size !iconname_steplimitexceeded_obs;
  image_failure_obs := image ~size !iconname_failure_obs;
  image_yes := image ~size !iconname_yes;
  image_no := image ~size !iconname_no;
  image_file := image ~size !iconname_file;
  image_theory := image ~size !iconname_theory;
  image_goal := image ~size !iconname_goal;
  image_prover := image ~size !iconname_prover;
  image_transf := image ~size !iconname_transf;
  image_metas := image ~size !iconname_metas;
  image_editor := image ~size !iconname_editor;
  image_replay := image ~size !iconname_replay;
  image_cancel := image ~size !iconname_cancel;
  image_reload := image ~size !iconname_reload;
  image_remove := image ~size !iconname_remove;
  image_cleaning := image ~size !iconname_cleaning;
  ()

let init () =
  Debug.dprintf debug "[config] reading icons...@?";
  load_icon_names ();
  why_icon := image "logo-why";
  resize_images 20;
  Debug.dprintf debug " done.@."

let show_legend_window ~parent () =
  let dialog =
    GWindow.dialog
      ~modal:true ~parent
      ~title:"Why3: legend of icons" ~icon:!why_icon
      ()
  in
  let vbox = dialog#vbox in
  let text = GText.view ~packing:vbox#add
    ~editable:false ~cursor_visible:false () in
  let b = text#buffer in
  let tt = b#create_tag [`WEIGHT `BOLD; `JUSTIFICATION `CENTER;
    `PIXELS_ABOVE_LINES 15; `PIXELS_BELOW_LINES 3; ] in
  let i s = b#insert ~iter:b#end_iter s in
  let it s = b#insert ~iter:b#end_iter ~tags:[tt] s in
  let ib i = b#insert_pixbuf ~iter:b#end_iter ~pixbuf:!i in
  it "Tree view\n";
  ib image_file;
  i "   File, containing a set of theories\n";
  ib image_theory;
  i "   Theory, containing a set of goals\n";
  ib image_goal;
  i "   Goal\n";
  ib image_prover;
  i "   External prover\n";
  ib image_transf;
  i "   Transformation or strategy\n";
  it "Status column\n";
  ib image_undone;
  i "   External proof attempt not done\n";
  ib image_scheduled;
  i "   Scheduled external proof attempt\n";
  ib image_running;
  i "   Running external proof attempt\n";
  ib image_valid;
  i "   Goal is proved / Theory is fully verified\n";
  ib image_invalid;
  i "   External prover disproved the goal\n";
  ib image_timeout;
  i "   External prover reached the time limit\n";
  ib image_outofmemory;
  i "   External prover ran out of memory\n";
  ib image_steplimitexceeded;
  i "   External prover exceeded the step limit\n";
  ib image_unknown;
  i "   External prover answer not conclusive\n";
  ib image_failure;
  i "   External prover call failed\n";
  ib image_valid_obs;
  i "   Valid but obsolete result\n";
  ib image_unknown_obs;
  i "   Answer not conclusive and obsolete\n";
  ib image_timeout_obs;
  i "   Time limit reached, obsolete\n";
  ib image_outofmemory_obs;
  i "   Out of memory, obsolete\n";
  ib image_steplimitexceeded_obs;
  i "   Step limit exceeded, obsolete\n";
  ib image_invalid_obs;
  i "   Prover disproved goal, but obsolete\n";
  ib image_failure_obs;
  i "   External prover call failed, obsolete\n";
  dialog#add_button "Close" `CLOSE ;
  let t = b#create_tag [`LEFT_MARGIN 10; `RIGHT_MARGIN 10 ] in
  b#apply_tag t ~start:b#start_iter ~stop:b#end_iter;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  dialog#destroy ()


let show_about_window ~parent () =
  let about_dialog =
    GWindow.about_dialog
      ~parent
      ~name:"The Why3 Verification Platform"
      ~authors:["François Bobot";
                "Jean-Christophe Filliâtre";
                "Claude Marché";
                "Guillaume Melquiond";
                "Andrei Paskevich";
                "";
                "with contributions of";
                "";
                "Stefan Berghofer";
                "Sylvie Boldo";
                "Martin Clochard";
                "Simon Cruanes";
                "Sylvain Dailler";
                "Clément Fumex";
                "Léon Gondelman";
                "David Hauzar";
                "Daisuke Ishii";
                "Johannes Kanig";
                "Mikhail Mandrykin";
                "David Mentré";
                "Benjamin Monate";
                "Kim Nguyễn";
                "Thi-Minh-Tuyen Nguyen";
                "Mário Pereira";
                "Raphaël Rieu-Helft";
                "Simão Melo de Sousa";
                "Asma Tafat";
                "Piotr Trojanek";
                "Makarius Wenzel";
               ]
      ~copyright:"Copyright 2010-2018 Inria, CNRS, Paris-Sud University"
      ~license:("See file " ^ Filename.concat Config.datadir "LICENSE")
      ~website:"http://why3.lri.fr/"
      ~website_label:"http://why3.lri.fr/"
      ~version:Config.version
      ~icon:!why_icon
      ~logo:!why_icon
      ()
  in
  let ( _ : GWindow.Buttons.about) = about_dialog#run () in
  about_dialog#destroy ()




(**** Preferences Window ***)

let general_settings (c : t) (notebook:GPack.notebook) =
  let label = GMisc.label ~text:"General" () in
  let page =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()
  in
  (* debug mode ? *)
(*
  let debugmode =
    GButton.check_button ~label:"debug" ~packing:page1#add ()
      ~active:(c.verbose > 0)
  in
  let (_ : GtkSignal.id) =
    debugmode#connect#toggled ~callback:
      (fun () -> c.verbose <- 1 - c.verbose)
  in
*)
  let page_pack = page#pack ?from:None ?expand:None ?fill:None ?padding:None in
  let external_processes_options_frame =
    GBin.frame ~label:"External provers options" ~packing:page_pack ()
  in
  let vb = GPack.vbox ~homogeneous:false
    ~packing:external_processes_options_frame#add ()
  in
  (* time limit *)
  let width = 300 and xalign = 0.0 in
  let hb = GPack.hbox ~homogeneous:false ~packing:vb#add () in
  let hb_pack = hb#pack ~expand:false ?from:None ?fill:None ?padding:None in
  let _ = GMisc.label ~text:"Time limit (in sec.): " ~width ~xalign
    ~packing:hb_pack () in
  let timelimit_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  timelimit_spin#adjustment#set_bounds ~lower:0. ~upper:86_400. ~step_incr:5. ();
  timelimit_spin#adjustment#set_value (float_of_int c.session_time_limit);
  let (_ : GtkSignal.id) =
    timelimit_spin#connect#value_changed ~callback:
      (fun () -> c.session_time_limit <- timelimit_spin#value_as_int)
  in
  (* mem limit *)
  let hb = GPack.hbox ~homogeneous:false ~packing:vb#add () in
  let hb_pack = hb#pack ~expand:false ?from:None ?fill:None ?padding:None in
  let _ = GMisc.label ~text:"Memory limit (in Mb): " ~width ~xalign
    ~packing:hb_pack () in
  let memlimit_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  memlimit_spin#adjustment#set_bounds ~lower:0. ~upper:16_000. ~step_incr:500. ();
  memlimit_spin#adjustment#set_value (float_of_int c.session_mem_limit);
  let (_ : GtkSignal.id) =
    memlimit_spin#connect#value_changed ~callback:
      (fun () -> c.session_mem_limit <- memlimit_spin#value_as_int)
  in
  (* nb of processes *)
  let hb = GPack.hbox ~homogeneous:false ~packing:vb#add () in
  let hb_pack = hb#pack ~expand:false ?from:None ?fill:None ?padding:None in
  let _ = GMisc.label ~text:"Nb of processes: " ~width ~xalign
    ~packing:hb_pack () in
  let nb_processes_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  nb_processes_spin#adjustment#set_bounds
    ~lower:1. ~upper:64. ~step_incr:1. ();
  nb_processes_spin#adjustment#set_value
    (float_of_int c.session_nb_processes);
  let (_ : GtkSignal.id) =
    nb_processes_spin#connect#value_changed ~callback:
      (fun () -> c.session_nb_processes <- nb_processes_spin#value_as_int)
  in
  (* counter-example *)
(*
  let cntexample_check = GButton.check_button ~label:"get counter-example"
    ~packing:vb#add ()
    ~active:c.session_cntexample
  in
  let (_: GtkSignal.id) =
    cntexample_check#connect#toggled ~callback:
      (fun () -> c.session_cntexample <- not c.session_cntexample)
  in
*)
  (* source editing allowed *)
  let source_editing_check = GButton.check_button ~label:"allow editing source files"
    ~packing:vb#add ()
    ~active:c.allow_source_editing
  in
  let (_: GtkSignal.id) =
    source_editing_check#connect#toggled ~callback:
      (fun () -> c.allow_source_editing <- not c.allow_source_editing)
  in
  (* session saving policy *)
  let set_saving_policy n () = c.saving_policy <- n in
  let saving_policy_frame =
    GBin.frame ~label:"Session saving policy"
      ~packing:page_pack ()
  in
  let saving_policy_box =
    GPack.button_box
      `VERTICAL ~border_width:5 ~spacing:5
      ~packing:saving_policy_frame#add ()
  in
  let saving_policy_box_pack =
    saving_policy_box#pack ?from:None ?expand:None ?fill:None ?padding:None
  in
  let choice0 =
    GButton.radio_button
      ~label:"always save on exit"
      ~active:(c.saving_policy = 0)
      ~packing:saving_policy_box_pack ()
  in
  let choice1 =
    GButton.radio_button
      ~label:"never save on exit" ~group:choice0#group
      ~active:(c.saving_policy = 1)
      ~packing:saving_policy_box_pack ()
  in
  let choice2 =
    GButton.radio_button
      ~label:"ask whether to save on exit" ~group:choice0#group
      ~active:(c.saving_policy = 2)
      ~packing:saving_policy_box_pack ()
  in
  let (_ : GtkSignal.id) =
    choice0#connect#toggled ~callback:(set_saving_policy 0)
  in
  let (_ : GtkSignal.id) =
    choice1#connect#toggled ~callback:(set_saving_policy 1)
  in
  let (_ : GtkSignal.id) =
    choice2#connect#toggled ~callback:(set_saving_policy 2)
  in
  let (_ : GPack.box) =
    GPack.vbox ~packing:page_pack ()
  in
  ()

(** Appearance *)

let appearance_settings (c : t) (notebook:GPack.notebook) =
  let label = GMisc.label ~text:"Appearance" () in
  let page =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()
  in
  let page_pack = page#pack ?from:None ?expand:None ?fill:None ?padding:None in
  let display_options_frame =
    GBin.frame ~label:"Display options" ~packing:page_pack ()
  in
  let vb = GPack.vbox ~homogeneous:false
    ~packing:display_options_frame#add ()
  in
  (* max boxes *)
  let width = 300 and xalign = 0.0 in
  let hb = GPack.hbox ~homogeneous:false ~packing:vb#add () in
  let hb_pack = hb#pack ~expand:false ?fill:None ?from:None ?padding:None in
  let _ = GMisc.label ~text:"Use ellipsis for terms deeper than: " ~width ~xalign ~packing:hb_pack () in
  let max_boxes_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  max_boxes_spin#adjustment#set_bounds ~lower:0. ~upper:1000. ~step_incr:1. ();
  max_boxes_spin#adjustment#set_value (float_of_int c.max_boxes);
  let (_ : GtkSignal.id) =
    max_boxes_spin#connect#value_changed ~callback:
      (fun () -> c.max_boxes <- max_boxes_spin#value_as_int)
  in
  (* options for task display *)
  let display_options_box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:vb#add ()
  in
  let showfullcontext =
    GButton.check_button ~label:"show full task context"
      ~packing:display_options_box#add ()
      ~active:c.show_full_context
  in
  let (_ : GtkSignal.id) =
    showfullcontext#connect#toggled ~callback:
      (fun () -> c.show_full_context <- not c.show_full_context)
  in
  let showattrs =
    GButton.check_button
      ~label:"show attributes in formulas"
      ~packing:display_options_box#add ()
      ~active:c.show_attributes
  in
  let (_ : GtkSignal.id) =
    showattrs#connect#toggled ~callback:
      (fun () ->
         c.show_attributes <- not c.show_attributes;
         set_attr_flag c.show_attributes)
  in
  let showcoercions =
    GButton.check_button
      ~label:"show coercions in formulas"
      ~packing:display_options_box#add ()
      ~active:c.show_coercions
  in
  let (_ : GtkSignal.id) =
    showcoercions#connect#toggled ~callback:
      (fun () ->
         c.show_coercions <- not c.show_coercions;
         set_coercions_flag c.show_coercions)
  in
  let showlocs =
    GButton.check_button
      ~label:"show source locations in formulas"
      ~packing:display_options_box#add ()
      ~active:c.show_locs
  in
  let (_ : GtkSignal.id) =
    showlocs#connect#toggled ~callback:
      (fun () ->
         c.show_locs <- not c.show_locs;
         set_locs_flag c.show_locs)
  in
  let showtimelimit =
    GButton.check_button
      ~label:"show time and memory limits for each proof"
      ~packing:display_options_box#add ()
      ~active:c.show_time_limit
  in
  let (_ : GtkSignal.id) =
    showtimelimit#connect#toggled ~callback:
      (fun () ->
         c.show_time_limit <- not c.show_time_limit)
  in
  (* icon sets *)
  let icon_sets_frame =
    GBin.frame ~label:"Change icon family (needs save & restart)"
      ~packing:page_pack ()
  in
  let icon_sets_box =
    GPack.button_box
      `VERTICAL ~border_width:5 ~spacing:5
      ~packing:icon_sets_frame#add ()
  in
  let icon_sets_box_pack =
    icon_sets_box#pack ?from:None ?expand:None ?fill:None ?padding:None
  in
  let dir,iconsets = iconsets () in
  let set_icon_set s () = c.iconset <- s in
  let (_,choices) = List.fold_left
    (fun (acc,l) (s,fields) ->
      let name = Rc.get_string ~default:s fields "name" in
      let license = Rc.get_string ~default:"" fields "license" in
      let acc,choice =
        match acc with
        | None ->
          let choice =
            GButton.radio_button
              ~label:name
              ~active:(c.iconset = s)
              ~packing:icon_sets_box_pack ()
          in
          (Some choice,choice)
        | Some c0 ->
          let choice =
            GButton.radio_button
              ~label:name
              ~active:(c.iconset = s)
              ~group:c0#group
              ~packing:icon_sets_box_pack ()
          in (acc,choice)
      in
      if license <> "" then
        begin
          let f = Filename.concat (Filename.concat dir s) license in
          let c = Sysutil.file_contents f in
          let text = "See license in " ^ f ^ ":\n\n" in
          let l = String.length c in
          let text =
            if l >= 256 then
              text ^ String.sub c 0 255 ^ "\n[...]"
            else
              text ^ c
          in
          choice#misc#set_tooltip_markup text
        end;
      (acc,(s,choice)::l))
    (None,[]) iconsets
  in
  List.iter
    (fun (s,c) ->
      let (_ : GtkSignal.id) =
        c#connect#toggled ~callback:(set_icon_set s)
      in ())
    choices;
  let (_ : GPack.box) =
    GPack.vbox ~packing:page_pack ()
  in
  ()

(* Page "Provers" *)

let provers_page c (notebook:GPack.notebook) =
  let label = GMisc.label ~text:"Provers" () in
  let page =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()
  in
  let page_pack = page#pack ~fill:true ~expand:true ?from:None ?padding:None in
  let hbox = GPack.hbox ~packing:page_pack () in
  let hbox_pack = hbox#pack ~fill:true ~expand:true ?from:None ?padding:None in
  let scrollview =
  try
    GBin.scrolled_window ~hpolicy:`NEVER ~vpolicy:`AUTOMATIC
      ~packing:hbox_pack ()
  with Gtk.Error _ -> assert false
  in let () = scrollview#set_shadow_type `OUT in
  let vbox = GPack.vbox ~packing:scrollview#add_with_viewport () in
  let vbox_pack = vbox#pack ~fill:true ~expand:true ?from:None ?padding:None in
  let hbox = GPack.hbox ~packing:vbox_pack () in
  let hbox_pack = hbox#pack ~fill:true ~expand:true ?from:None ?padding:None in
  (* show/hide provers *)
  let frame =
    GBin.frame ~label:"Provers visible in the context menu" ~packing:hbox_pack ()
  in
  let provers_box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:frame#add () in
  let hidden_provers = Hashtbl.create 7 in
  Mprover.iter
    (fun _ p ->
      let name = prover_parseable_format p.prover in
      let label = Pp.string_of_wnl print_prover p.prover in
      let hidden = ref (List.mem name c.hidden_provers) in
      Hashtbl.add hidden_provers name hidden;
      let b =
        GButton.check_button ~label ~packing:provers_box#add ()
          ~active:(not !hidden)
      in
      let (_ : GtkSignal.id) =
        b#connect#toggled ~callback:
          (fun () -> hidden := not !hidden;
            c.hidden_provers <-
              Hashtbl.fold
              (fun l h acc -> if !h then l::acc else acc) hidden_provers [])
      in ())
    (Whyconf.get_provers c.config);
  (* default prover *)
(*
  let frame2 =
    GBin.frame ~label:"Default prover" ~packing:hbox_pack () in
  let provers_box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:frame2#add () in
  let group =
    let b =
      GButton.radio_button ~label:"(none)" ~packing:provers_box#add
                           ~active:(c.config.default_prover = "") () in
    let (_ : GtkSignal.id) =
      b#connect#toggled ~callback:(fun () -> c.config.default_prover <- "") in
    b#group in
  Mprover.iter
    (fun _ p ->
      let name = prover_parseable_format p.prover in
      let label = Pp.string_of_wnl print_prover p.prover in
      let b =
        GButton.radio_button ~label ~group ~packing:provers_box#add
                             ~active:(name = c.config.default_prover) () in
      let (_ : GtkSignal.id) =
        b#connect#toggled ~callback:(fun () -> c.config.default_prover <- name)
      in ())
    (Whyconf.get_provers c.config)
 *)
  ()

(* Page "Uninstalled provers" *)

let alternatives_frame c (notebook:GPack.notebook) =
  let label = GMisc.label ~text:"Uninstalled provers policies" () in
  let page =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()
  in
  let page_pack = page#pack ?fill:None ?expand:None ?from:None ?padding:None in
  let frame =
    GBin.frame ~label:"Click to remove a setting" ~packing:page_pack ()
  in
  let box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:frame#add ()
  in
  let remove button p () =
    button#destroy ();
    c.config <- set_policies c.config (Mprover.remove p (get_policies c.config));
  in
  let iter p policy =
    let label =
      match policy with
        | CPU_remove -> Pp.sprintf_wnl "proofs with %a removed" print_prover p
        | CPU_keep -> Pp.sprintf_wnl "proofs with %a kept as they are" print_prover p
        | CPU_upgrade t ->
          Pp.sprintf_wnl "proofs with %a moved to %a" print_prover p print_prover t
        | CPU_duplicate t ->
          Pp.sprintf_wnl "proofs with %a duplicated to %a" print_prover p print_prover t
    in
    let button = GButton.button ~label ~packing:box#add () in
    let (_ : GtkSignal.id) =
      button#connect#released ~callback:(remove button p)
    in ()
  in
  Mprover.iter iter (get_policies c.config);
  let page_pack = page#pack ?fill:None ~expand:true ?from:None ?padding:None in
  let _fillbox = GPack.vbox ~packing:page_pack () in
  ()

let editors_page c (notebook:GPack.notebook) =
  let label = GMisc.label ~text:"Editors" () in
  let page =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()
  in
  let page_pack = page#pack ~fill:true ~expand:true ?from:None ?padding:None in
  let hbox = GPack.hbox ~packing:page_pack () in
  let hbox_pack = hbox#pack ~fill:true ~expand:true ?from:None ?padding:None in
  let scrollview =
    GBin.scrolled_window ~hpolicy:`NEVER ~vpolicy:`AUTOMATIC
      ~packing:hbox_pack ()
  in
  let vbox = GPack.vbox ~packing:scrollview#add_with_viewport () in
  let vbox_pack = vbox#pack ?fill:None ?expand:None ?from:None ?padding:None in
  let default_editor_frame =
    GBin.frame ~label:"Default editor" ~packing:vbox_pack ()
  in
  let main = Whyconf.get_main c.config in
  let editor_entry =
   GEdit.entry ~text:(default_editor main) ~packing:default_editor_frame#add ()
  in
  let (_ : GtkSignal.id) =
    editor_entry#connect#changed
      ~callback:
      (fun () ->
       c.config <- Whyconf.set_main c.config
	(Whyconf.set_default_editor main editor_entry#text))
  in
  let frame = GBin.frame ~label:"Specific editors" ~packing:vbox_pack () in
  let box = GPack.vbox ~border_width:5 ~packing:frame#add () in
  let box_pack = box#pack ?fill:None ?expand:None ?from:None ?padding:None in
  let editors = Whyconf.get_editors c.config in
  let _,strings,indexes,map =
    Meditor.fold
      (fun k data (i,str,ind,map) ->
        let n = data.editor_name in
        (i+1, n::str, Meditor.add k i ind, Meditor.add n k map))
      editors (2, [], Meditor.empty, Meditor.empty)
  in
  let strings = "(default)" :: "--" :: (List.rev strings) in
  let add_prover p pi =
    let text = Pp.string_of_wnl Whyconf.print_prover p in
    let hb = GPack.hbox ~homogeneous:false ~packing:box_pack () in
    let hb_pack_fill_expand =
      hb#pack ~fill:true ~expand:true ?from:None ?padding:None
    in
    let hb_pack = hb#pack ?fill:None ?expand:None ?from:None ?padding:None in
    let _ = GMisc.label ~width:150 ~xalign:0.0 ~text
      ~packing:hb_pack_fill_expand () in
    let (combo, ((_ : GTree.list_store), column)) =
      GEdit.combo_box_text ~packing:hb_pack ~strings ()
    in
    combo#set_row_separator_func
      (Some (fun m row -> m#get ~row ~column = "--"));
    let i =
      try Meditor.find pi.editor indexes with Not_found -> 0
    in
    combo#set_active i;
    let ( _ : GtkSignal.id) = combo#connect#changed
      ~callback:(fun () ->
        match combo#active_iter with
          | None -> ()
          | Some row ->
	    let data =
              match combo#model#get ~row ~column with
                | "(default)" -> ""
                | s ->
                  try Meditor.find s map
                  with Not_found -> assert false
            in
	    (* Debug.dprintf debug "prover %a: selected editor '%s'@." *)
            (*   print_prover p data; *)
            let provers = Whyconf.get_provers c.config in
            c.config <-
              Whyconf.set_provers c.config
              (Mprover.add p { pi with editor = data} provers)
      )
    in
    ()
  in
  Mprover.iter add_prover (Whyconf.get_provers c.config)


let preferences ~parent (c : t) =
  let dialog = GWindow.dialog
    ~modal:true ~parent ~icon:(!why_icon)
    ~title:"Why3: preferences" ()
  in
  let vbox = dialog#vbox in
  let notebook = GPack.notebook ~packing:vbox#add () in
  (* page "general settings" **)
  general_settings c notebook;
  (* page "appearance" **)
  appearance_settings c notebook;
  (* page "editors" **)
  editors_page c notebook;
  (* page "Provers" **)
  provers_page c notebook;
  (* page "uninstalled provers" *)
  alternatives_frame c notebook;
  (* page "Colors" **)
(*
  let label2 = GMisc.label ~text:"Colors" () in
  let _color_sel = GMisc.color_selection (* ~title:"Goal color" *)
    ~show:true
    ~packing:(fun w -> ignore(notebook#append_page
                                ~tab_label:label2#coerce w)) ()
  in
  let (_ : GtkSignal.id) =
    color_sel#connect ColorSelection.S.color_changed ~callback:
      (fun c -> Format.eprintf "Gconfig.color_sel: %s@."
         c)
  in
*)
  (* bottom button **)
  dialog#add_button "Save&Close" `SAVE ;
  dialog#add_button "Close" `CLOSE ;
  let ( answer : [`SAVE | `CLOSE | `DELETE_EVENT ]) = dialog#run () in
  begin
    match answer with
    | `SAVE ->
      c.config <- Whyconf.set_main c.config
        (Whyconf.set_limits (Whyconf.get_main c.config)
           c.session_time_limit c.session_mem_limit c.session_nb_processes);
      save_config ()
    | `CLOSE | `DELETE_EVENT -> ()
  end;
  dialog#destroy ()

(*
let run_auto_detection gconfig =
  let config = Autodetection.run_auto_detection gconfig.config in
  gconfig.config <- config;
  let _provers = get_provers config in
(* TODO: store the result differently
  gconfig.provers <- Mstr.fold (Session.get_prover_data gconfig.env) provers
  Mstr.empty
*)
  ()
*)

(*let () = Debug.dprintf debug "[config] end of configuration initialization@."*)

let uninstalled_prover_dialog ~parent ~callback c unknown =
  let others,names,versions =
    Whyconf.unknown_to_known_provers
      (Whyconf.get_provers c.config) unknown
  in
  let dialog = GWindow.dialog
                 ~icon:(!why_icon) ~modal:true ~parent
                 ~title:"Why3: Uninstalled prover" ()
  in
  let vbox = dialog#vbox in
  let vbox_pack = vbox#pack ~fill:true ~expand:true ?from:None ?padding:None in
  let hbox = GPack.hbox ~packing:vbox_pack () in
  let hbox_pack = hbox#pack ~fill:true ~expand:true ?from:None ?padding:None in
  let height = parent#misc#allocation.Gtk.height * 3 / 4 in
  let scrollview =
    GBin.scrolled_window ~hpolicy:`NEVER ~vpolicy:`AUTOMATIC ~height
      ~packing:hbox_pack ()
  in
  let () = scrollview#set_shadow_type `OUT in
  let vbox = GPack.vbox ~packing:scrollview#add_with_viewport () in
  (* header *)
  let hb = GPack.hbox ~packing:vbox#add () in
  let _ = GMisc.image ~stock:`DIALOG_WARNING ~packing:hb#add () in
  let (_:GMisc.label) =
    let text =
      Pp.sprintf "The prover %a is not installed"
        Whyconf.print_prover unknown
    in
    GMisc.label ~ypad:20 ~text ~xalign:0.5 ~packing:hb#add ()
  in
  let (_:GMisc.label) =
    let text =
      "WARNING: this policy will not be taken into account immediately \
        but only if you replay again the proofs."
    in
    GMisc.label ~text ~line_wrap:true ~packing:vbox#add ()
  in
  let (_:GMisc.label) =
    let text =
      "WARNING: do not forget to save preferences to keep this policy in future sessions"
    in
    GMisc.label ~text ~line_wrap:true ~packing:vbox#add ()
  in
  (* choices *)
  let vbox_pack =
    vbox#pack ~fill:true ~expand:true ?from:None ?padding:None
  in
  let label = "Please select a policy for associated proof attempts" in
  let policy_frame = GBin.frame ~label ~packing:vbox_pack () in
  let choice = ref 1 in
  let prover_choosed = ref None in
  let set_prover prover () = prover_choosed := Some prover in
  let box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:policy_frame#add ()
  in
  let choice_keep = GButton.radio_button
      ~label:"keep proofs as they are, do not try to play them"
      ~active:true
      ~packing:box#add () in
  let choice1 = GButton.radio_button
      ~label:"move proofs to the selected prover below"
      ~active:false ~group:choice_keep#group
      ~packing:box#add () in
  let choice2 = GButton.radio_button
      ~label:"duplicate proofs to the selected prover below"
      ~active:false ~group:choice_keep#group
      ~packing:box#add () in
  let choice3 = GButton.radio_button
      ~label:"remove these proofs from session"
      ~active:false  ~group:choice_keep#group
      ~packing:box#add () in
  let first = ref None in
  let alternatives_section acc label alternatives =
    if alternatives <> [] then
      let frame = GBin.frame ~label ~packing:vbox#add () in
      let box =
        GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
          ~packing:frame#add ()
      in
      let iter_alter prover =
        let choice_button =
          let label = Pp.string_of_wnl print_prover prover in
          match !first with
          | None ->
              let choice_button =
                GButton.radio_button ~label ~active:true ~packing:box#add ()
              in
              prover_choosed := Some prover;
              first := Some choice_button;
              choice_button
          | Some first ->
              GButton.radio_button ~label ~group:first#group
                ~active:false ~packing:box#add ()
        in
        ignore (choice_button#connect#toggled ~callback:(set_prover prover))
      in
      List.iter iter_alter alternatives;
      frame#misc :: (* box#misc :: *) acc
    else acc
  in
  let boxes = alternatives_section [] "Same name and same version" versions in
  let boxes = alternatives_section boxes "Same name and different version" names in
  let boxes = alternatives_section boxes "Different name" others in
  let hide_provers () = List.iter (fun b -> b#set_sensitive false) boxes in
  let show_provers () = List.iter (fun b -> b#set_sensitive true) boxes in
  if versions<>[] || names<>[] then
    begin
      choice_keep#set_active false;
      choice1#set_active true;
    end
  else
    hide_provers();
  ignore (choice_keep#connect#toggled
            ~callback:(fun () -> choice := 0; hide_provers ()));
  ignore (choice1#connect#toggled
            ~callback:(fun () -> choice := 1; show_provers ()));
  ignore (choice2#connect#toggled
            ~callback:(fun () -> choice := 2; show_provers ()));
  ignore (choice3#connect#toggled
            ~callback:(fun () -> choice := 3; hide_provers ()));
  dialog#add_button "Ok" `CLOSE ;
  ignore (dialog#run ());
  dialog#destroy ();
  let policy =
    match !choice, !prover_choosed with
    | 0,_ -> CPU_keep
    | 1, Some p -> CPU_upgrade p
    | 2, Some p -> CPU_duplicate p
    | 3,_ -> CPU_remove
    | _ -> assert false
  in
  c.config <- set_prover_upgrade_policy c.config unknown policy;
  let () = callback unknown policy in
  ()


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.opt"
End:
*)
