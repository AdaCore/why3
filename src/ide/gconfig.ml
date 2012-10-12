(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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
open Why3
open Rc
open Whyconf

let debug = Debug.register_info_flag "ide_info"
  ~desc:"About why3ide."
let () = Debug.set_flag debug

(** set the exception call back handler to the Exn_printer of why3 *)
let () = (***** TODO TODO make that work, it seems not called!!! *)
  let why3_handler exn =
    Format.eprintf "@[Why3ide callback raised an exception:@\n%a@]@.@."
      Exn_printer.exn_printer exn;
    (** print the stack trace if asked to (can't be done by the usual way) *)
    if Debug.test_flag Debug.stack_trace then
      Printf.eprintf "Backtrace:\n%t\n%!" Printexc.print_backtrace
  in
  GtkSignal.user_handler := why3_handler

(* config file *)

(* type altern_provers = prover option Mprover.t *)

(** Todo do something generic perhaps*)
(*
type conf_replace_prover =
  | CRP_Ask
  | CRP_Not_Obsolete
*)

type t =
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
      mutable verbose : int;
      mutable default_editor : string;
      mutable intro_premises : bool;
      mutable show_labels : bool;
      mutable show_locs : bool;
      mutable show_time_limit : bool;
      mutable saving_policy : int;
      (** 0 = always, 1 = never, 2 = ask *)
      mutable premise_color : string;
      mutable goal_color : string;
      mutable error_color : string;
      mutable iconset : string;
      (** colors *)
      mutable env : Env.env;
      mutable config : Whyconf.config;
      original_config : Whyconf.config;
      (* mutable altern_provers : altern_provers; *)
      (* mutable replace_prover : conf_replace_prover; *)
      (* hidden prover buttons *)
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
  ide_verbose : int;
  ide_intro_premises : bool;
  ide_show_labels : bool;
  ide_show_locs : bool;
  ide_show_time_limit : bool;
  ide_saving_policy : int;
  ide_premise_color : string;
  ide_goal_color : string;
  ide_error_color : string;
  ide_iconset : string;
  ide_default_editor : string;
  (* ide_replace_prover : conf_replace_prover; *)
  ide_hidden_provers : string list;
}

let default_ide =
  { ide_window_width = 1024;
    ide_window_height = 768;
    ide_tree_width = 512;
    ide_task_height = 384;
    ide_verbose = 0;
    ide_intro_premises = true;
    ide_show_labels = false;
    ide_show_locs = false;
    ide_show_time_limit = false;
    ide_saving_policy = 2;
    ide_premise_color = "chartreuse";
    ide_goal_color = "gold";
    ide_error_color = "orange";
    ide_iconset = "boomy";
    (* ide_replace_prover = CRP_Ask; *)
    ide_default_editor =
      (try Sys.getenv "EDITOR" ^ " %f"
       with Not_found -> "editor %f");
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
    ide_verbose =
      get_int section ~default:default_ide.ide_verbose "verbose";
    ide_intro_premises =
      get_bool section ~default:default_ide.ide_intro_premises
        "intro_premises";
    ide_show_labels =
      get_bool section ~default:default_ide.ide_show_labels "print_labels";
    ide_show_locs =
      get_bool section ~default:default_ide.ide_show_locs "print_locs";
    ide_show_time_limit =
      get_bool section ~default:default_ide.ide_show_time_limit
        "print_time_limit";
    ide_saving_policy =
      get_int section ~default:default_ide.ide_saving_policy "saving_policy";
    ide_premise_color =
      get_string section ~default:default_ide.ide_premise_color
        "premise_color";
    ide_goal_color =
      get_string section ~default:default_ide.ide_goal_color
        "goal_color";
    ide_error_color =
      get_string section ~default:default_ide.ide_error_color
        "error_color";
    ide_iconset =
      get_string section ~default:default_ide.ide_iconset
        "iconset";
    ide_default_editor =
      get_string section ~default:default_ide.ide_default_editor
        "default_editor";
 (*
   ide_replace_prover =
      begin
        match get_stringo section "replace_prover" with
        | None -> default_ide.ide_replace_prover
        | Some "never not obsolete" -> CRP_Not_Obsolete
        | Some "ask" | Some _ -> CRP_Ask
      end;
 *)
    ide_hidden_provers = get_stringl ~default:default_ide.ide_hidden_provers section "hidden_prover";
  }


let set_labels_flag =
  let fl = Debug.lookup_flag "print_labels" in
  fun b ->
    (if b then Debug.set_flag else Debug.unset_flag) fl

let set_locs_flag =
  let fl = Debug.lookup_flag "print_locs" in
  fun b ->
    (if b then Debug.set_flag else Debug.unset_flag) fl

(* dead code
let load_altern alterns (_,section) =
  let unknown =
    {prover_name = get_string section "unknown_name";
     prover_version = get_string section "unknown_version";
     prover_altern = get_string ~default:"" section "unknown_alternative"
    } in
  let name = get_stringo section "known_name" in
  let known = match name with
    | None -> None
    | Some name ->
      Some
        {prover_name = name;
         prover_version = get_string section "known_version";
         prover_altern = get_string ~default:"" section "known_alternative";
        } in
  Mprover.add unknown known alterns
*)

let load_config config original_config =
  let main = get_main config in 
  let ide  = match get_section config "ide" with
    | None -> default_ide
    | Some s -> load_ide s
  in
  (* let alterns = *)
  (*   List.fold_left load_altern *)
  (*     Mprover.empty (get_family config "alternative_prover") in *)
  (* temporary sets env to empty *)
  let env = Env.create_env [] in
  set_labels_flag ide.ide_show_labels;
  set_locs_flag ide.ide_show_locs;
  { window_height = ide.ide_window_height;
    window_width  = ide.ide_window_width;
    tree_width    = ide.ide_tree_width;
    task_height   = ide.ide_task_height;
    verbose       = ide.ide_verbose;
    intro_premises= ide.ide_intro_premises ;
    show_labels   = ide.ide_show_labels ;
    show_locs     = ide.ide_show_locs ;
    show_time_limit = ide.ide_show_time_limit;
    saving_policy = ide.ide_saving_policy ;
    premise_color = ide.ide_premise_color;
    goal_color = ide.ide_goal_color;
    error_color = ide.ide_error_color;
    iconset = ide.ide_iconset;
    default_editor = ide.ide_default_editor;
    config         = config;
    original_config = original_config;
    env            = env;
    (* altern_provers = alterns; *)
    (* replace_prover = ide.ide_replace_prover; *)
    hidden_provers = ide.ide_hidden_provers;
    session_time_limit = Whyconf.timelimit main;
    session_mem_limit = Whyconf.memlimit main;
    session_nb_processes = Whyconf.running_provers_max main;
}


(*

  let save_altern unknown known (id,family) =
  let alt = empty_section in
  let alt = set_string alt "unknown_name" unknown.prover_name in
  let alt = set_string alt "unknown_version" unknown.prover_version in
  let alt =
    set_string ~default:"" alt "unknown_alternative" unknown.prover_altern in
  let alt = match known with
    | None -> alt
    | Some known ->
      let alt = set_string alt "known_name" known.prover_name in
      let alt = set_string alt "known_version" known.prover_version in
      set_string ~default:"" alt "known_alternative" known.prover_altern in
  (id+1,(sprintf "alt%i" id,alt)::family)

  *)

(*
let debug_save_config n c =
  let coq = { prover_name = "Coq" ; prover_version = "8.3pl3";
              prover_altern = "" } in
  let p = Mprover.find coq (get_provers c) in
  let time = Whyconf.timelimit (Whyconf.get_main c) in
  Format.eprintf "[debug] save_config %d: timelimit=%d ; editor for Coq=%s@."
    n time p.editor
*)

let save_config t =
  Debug.dprintf debug "[Info] saving IDE config file@.";
  (* taking original config, without the extra_config *)
  let config = t.original_config in
  (* copy possibly modified settings to original config *)
  let new_main = Whyconf.get_main t.config in
  let time = Whyconf.timelimit new_main in
  let mem = Whyconf.memlimit new_main in
  let nb = Whyconf.running_provers_max new_main in
  let config = set_main config (set_limits (get_main config) time mem nb) in
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
  let ide = set_int ide "verbose" t.verbose in
  let ide = set_bool ide "intro_premises" t.intro_premises in
  let ide = set_bool ide "print_labels" t.show_labels in
  let ide = set_bool ide "print_locs" t.show_locs in
  let ide = set_bool ide "print_time_limit" t.show_time_limit in
  let ide = set_int ide "saving_policy" t.saving_policy in
  let ide = set_string ide "premise_color" t.premise_color in
  let ide = set_string ide "goal_color" t.goal_color in
  let ide = set_string ide "error_color" t.error_color in
  let ide = set_string ide "iconset" t.iconset in
  let ide = set_string ide "default_editor" t.default_editor in
  let ide = set_stringl ide "hidden_prover" t.hidden_provers in
  let config = set_section config "ide" ide in
  Whyconf.save_config config

let read_config conf_file extra_files =
  try
    let config = Whyconf.read_config conf_file in
    let merged_config = List.fold_left Whyconf.merge_config config extra_files in
    load_config merged_config config
  with e when not (Debug.test_flag Debug.stack_trace) ->
    eprintf "@.%a@." Exn_printer.exn_printer e;
    exit 1

let config,read_config =
  let config = ref None in
  (fun () ->
    match !config with
      | None -> invalid_arg "configuration not yet loaded"
      | Some conf -> conf),
  (fun conf_file extra_files ->
    (*Debug.dprintf debug "[Info] reading config file...@?";*)
    let c = read_config conf_file extra_files in
    (*Debug.dprintf debug " done.@.";*)
    config := Some c)

let save_config () = save_config (config ())

let get_main () = (get_main (config ()).config)


(*

  images, icons

*)

let image_default = ref (GdkPixbuf.create ~width:1 ~height:1 ())
(** dumb pixbuf *)
let image_undone = ref !image_default
let image_scheduled = ref !image_default
let image_running = ref !image_default
let image_valid = ref !image_default
let image_unknown = ref !image_default
let image_invalid = ref !image_default
let image_timeout = ref !image_default
let image_outofmemory = ref !image_default
let image_failure = ref !image_default
let image_valid_obs = ref !image_default
let image_unknown_obs = ref !image_default
let image_invalid_obs = ref !image_default
let image_timeout_obs = ref !image_default
let image_outofmemory_obs = ref !image_default
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
  match size with
    | None ->
        GdkPixbuf.from_file n
    | Some s ->
        GdkPixbuf.from_file_at_size ~width:s ~height:s n

let iconname_default = ref ""
let iconname_undone = ref ""
let iconname_scheduled = ref ""
let iconname_running = ref ""
let iconname_valid = ref ""
let iconname_unknown = ref ""
let iconname_invalid = ref ""
let iconname_timeout = ref ""
let iconname_outofmemory = ref ""
let iconname_failure = ref ""
let iconname_valid_obs = ref ""
let iconname_unknown_obs = ref ""
let iconname_invalid_obs = ref ""
let iconname_timeout_obs = ref ""
let iconname_outofmemory_obs = ref ""
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

let load_icon_names () =
  let ide = config () in
  let iconset = ide.iconset in
  let main = get_main () in
  let n =
    Filename.concat (datadir main) (Filename.concat "images" "icons.rc")
  in
  let d = Rc.from_file n in
  let d = Rc.get_family d "iconset" in
  let d = List.assoc iconset d in
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
  iconname_failure := get_icon_name "failure";
  iconname_valid_obs := get_icon_name "valid_obs";
  iconname_unknown_obs := get_icon_name "unknown_obs";
  iconname_invalid_obs := get_icon_name "invalid_obs";
  iconname_timeout_obs := get_icon_name "timeout_obs";
  iconname_outofmemory_obs := get_icon_name "outofmemory_obs";
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
  image_failure := image ~size !iconname_failure;
  image_valid_obs := image ~size !iconname_valid_obs;
  image_unknown_obs := image ~size !iconname_unknown_obs;
  image_invalid_obs := image ~size !iconname_invalid_obs;
  image_timeout_obs := image ~size !iconname_timeout_obs;
  image_outofmemory_obs := image ~size !iconname_outofmemory_obs;
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
  Debug.dprintf debug "[Info] reading icons...@?";
  load_icon_names ();
  why_icon := image "logo-why";
  resize_images 20;
  Debug.dprintf debug " done.@."

let show_legend_window () =
  let dialog = GWindow.dialog ~title:"Why3: legend of icons" () in
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
  i "   Transformation\n";
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
  ib image_unknown;
  i "   External prover answer not conclusive\n";
  ib image_failure;
  i "   External prover call failed\n";
  ib image_valid_obs;
  i "   Valid but obsolete result\n";
  ib image_unknown_obs;
  i "   Answer not conclusive and obsolete\n";
  ib image_invalid_obs;
  i "   Prover disproved goal, but obsolete\n";
  ib image_failure_obs;
  i "   External prover call failed, obsolete\n";
  dialog#add_button "Close" `CLOSE ;
  let t = b#create_tag [`LEFT_MARGIN 10; `RIGHT_MARGIN 10 ] in
  b#apply_tag t ~start:b#start_iter ~stop:b#end_iter;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  dialog#destroy ()


let show_about_window () =
  let about_dialog =
    GWindow.about_dialog
      ~name:"Why3"
      ~authors:["François Bobot";
                "Jean-Christophe Filliâtre";
                "Claude Marché";
                "Andrei Paskevich"
               ]
      ~copyright:"Copyright 2010-2011 Univ Paris-Sud, CNRS, INRIA"
      ~license:"GNU Lesser General Public License"
      ~website:"https://gforge.inria.fr/projects/why3"
      ~website_label:"Project web site"
      ~version:Config.version
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
  let external_processes_options_frame =
    GBin.frame ~label:"External provers options"
      ~packing:page#pack ()
  in
  let vb = GPack.vbox ~homogeneous:false
    ~packing:external_processes_options_frame#add ()
  in
  (* time limit *)
  let width = 200 and xalign = 0.0 in
  let hb = GPack.hbox ~homogeneous:false ~packing:vb#add ()
  in
  let _ = GMisc.label ~text:"Time limit (in sec.): " ~width ~xalign
    ~packing:(hb#pack ~expand:false) () in
  let timelimit_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  timelimit_spin#adjustment#set_bounds ~lower:0. ~upper:300. ~step_incr:1. ();
  timelimit_spin#adjustment#set_value (float_of_int c.session_time_limit);
  let (_ : GtkSignal.id) =
    timelimit_spin#connect#value_changed ~callback:
      (fun () -> c.session_time_limit <- timelimit_spin#value_as_int)
  in
  (* mem limit *)
  let hb = GPack.hbox ~homogeneous:false ~packing:vb#add ()
  in
  let _ = GMisc.label ~text:"Memory limit (in Mb): " ~width ~xalign
    ~packing:(hb#pack ~expand:false) () in
  let memlimit_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  memlimit_spin#adjustment#set_bounds ~lower:0. ~upper:4000. ~step_incr:100. ();
  memlimit_spin#adjustment#set_value (float_of_int c.session_mem_limit);
  let (_ : GtkSignal.id) =
    memlimit_spin#connect#value_changed ~callback:
      (fun () -> c.session_mem_limit <- memlimit_spin#value_as_int)
  in
  (* nb of processes *)
  let hb = GPack.hbox ~homogeneous:false ~packing:vb#add ()
  in
  let _ = GMisc.label ~text:"Nb of processes: " ~width ~xalign
    ~packing:(hb#pack ~expand:false) () in
  let nb_processes_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  nb_processes_spin#adjustment#set_bounds
    ~lower:1. ~upper:16. ~step_incr:1. ();
  nb_processes_spin#adjustment#set_value
    (float_of_int c.session_nb_processes);
  let (_ : GtkSignal.id) =
    nb_processes_spin#connect#value_changed ~callback:
      (fun () -> c.session_nb_processes <- nb_processes_spin#value_as_int)
  in
  let hb = GPack.hbox ~homogeneous:false ~packing:vb#add () in
  let save_for_future = ref false in
  let save =
    GButton.check_button
      ~label:"save settings above for future sessions"
      ~packing:hb#add ()
      ~active:false
  in
  let (_ : GtkSignal.id) =
    save#connect#toggled ~callback:
      (fun () -> save_for_future := not !save_for_future)
  in
  let display_options_frame =
    GBin.frame ~label:"Display options"
      ~packing:page#pack ()
  in
  (* options for task display *)
  let display_options_box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:display_options_frame#add ()
  in
  let intropremises =
    GButton.check_button ~label:"introduce premises"
      ~packing:display_options_box#add ()
      ~active:c.intro_premises
  in
  let (_ : GtkSignal.id) =
    intropremises#connect#toggled ~callback:
      (fun () -> c.intro_premises <- not c.intro_premises)
  in
  let showlabels =
    GButton.check_button
      ~label:"show labels in formulas"
      ~packing:display_options_box#add ()
      ~active:c.show_labels
  in
  let (_ : GtkSignal.id) =
    showlabels#connect#toggled ~callback:
      (fun () ->
         c.show_labels <- not c.show_labels;
         set_labels_flag c.show_labels)
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
  (* session saving policy *)
  let set_saving_policy n () = c.saving_policy <- n in
  let saving_policy_frame =
    GBin.frame ~label:"Session saving policy"
      ~packing:page#pack ()
  in
  let saving_policy_box =
    GPack.button_box
      `VERTICAL ~border_width:5 ~spacing:5
      ~packing:saving_policy_frame#add ()
  in
  let choice0 =
    GButton.radio_button
      ~label:"always save on exit"
      ~active:(c.saving_policy = 0)
      ~packing:saving_policy_box#pack ()
  in
  let choice1 =
    GButton.radio_button
      ~label:"never save on exit" ~group:choice0#group
      ~active:(c.saving_policy = 1)
      ~packing:saving_policy_box#pack ()
  in
  let choice2 =
    GButton.radio_button
      ~label:"ask whether to save on exit" ~group:choice0#group
      ~active:(c.saving_policy = 2)
      ~packing:saving_policy_box#pack ()
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
    GPack.vbox ~packing:(page#pack ~expand:true) ()
  in
  save_for_future

(* Page "Provers" *)

let provers_page c (notebook:GPack.notebook) =
  let label = GMisc.label ~text:"Provers" () in
  let page =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()
  in
  let frame =
    GBin.frame ~label:"Provers button shown in the left toolbar"
      ~packing:page#pack ()
  in
  let provers_box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:frame#add ()
  in
  let hidden_provers = Hashtbl.create 7 in
  Mprover.iter
    (fun _ p ->
      let p = p.prover in
      let label = p.prover_name ^ " " ^ p.prover_version in
      let hidden = ref (List.mem label c.hidden_provers) in
      Hashtbl.add hidden_provers label hidden;
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
  let _fillbox =
    GPack.vbox ~packing:(page#pack ~expand:true) ()
  in
  ()

(* Page "Uninstalled provers" *)

let alternatives_frame c (notebook:GPack.notebook) =
  let label = GMisc.label ~text:"Uninstalled provers" () in
  let page =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()
  in
  let frame =
    GBin.frame ~label:"Click to remove a setting"
      ~packing:page#pack ()
  in
  let box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:frame#add ()
  in
  let remove button p () =
    button#destroy ();
    c.config <- set_policies c.config (Mprover.remove p (get_policies c.config))
  in
  let iter p policy =
    let label =
      match policy with
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
  let _fillbox =
    GPack.vbox ~packing:(page#pack ~expand:true) ()
  in
  ()

let editors_page c (notebook:GPack.notebook) =
  let label = GMisc.label ~text:"Editors" () in
  let page =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label#coerce w)) ()
  in
  let default_editor_frame =
    GBin.frame ~label:"Default editor" ~packing:page#pack ()
  in
  let editor_entry =
   GEdit.entry ~text:c.default_editor ~packing:default_editor_frame#add ()
  in
  let (_ : GtkSignal.id) =
    editor_entry#connect#changed ~callback:
      (fun () -> c.default_editor <- editor_entry#text)
  in
  let frame = GBin.frame ~label:"Specific editors" ~packing:page#pack () in
  let box = GPack.vbox ~border_width:5 ~packing:frame#add () in
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
    let text = p.prover_name ^ " " ^ p.prover_version in
    let hb = GPack.hbox ~homogeneous:false ~packing:box#pack () in
    let _ = GMisc.label ~width:150 ~xalign:0.0 ~text ~packing:(hb#pack ~expand:false) () in
    let (combo, ((_ : GTree.list_store), column)) =
      GEdit.combo_box_text ~packing:hb#pack ~strings ()
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
	    (* Debug.dprintf debug "prover %a : selected editor '%s'@." *)
            (*   print_prover p data; *)
            let provers = Whyconf.get_provers c.config in
            c.config <-
              Whyconf.set_provers c.config
              (Mprover.add p { pi with editor = data} provers)
      )
    in
    ()
  in
  Mprover.iter add_prover (Whyconf.get_provers c.config);
  let _fillbox =
    GPack.vbox ~packing:(page#pack ~expand:true) ()
  in
  ()


let preferences (c : t) =
  let dialog = GWindow.dialog
    ~modal:true
    ~title:"Why3: preferences" ()
  in
  let vbox = dialog#vbox in
  let notebook = GPack.notebook ~packing:vbox#add () in
  (** page "general settings" **)
  let save_for_future_session = general_settings c notebook in
  (*** page "editors" **)
  editors_page c notebook;
  (** page "Provers" **)
  provers_page c notebook;
  (*** page "uninstalled provers" *)
  alternatives_frame c notebook;
  (** page "Colors" **)
(*
  let label2 = GMisc.label ~text:"Colors" () in
  let _color_sel = GMisc.color_selection (* ~title:"Goal color" *)
    ~show:true
    ~packing:(fun w -> ignore(notebook#append_page
                                ~tab_label:label2#coerce w)) ()
  in
  let (_ : GtkSignal.id) =
    color_sel#connect ColorSelection.S.color_changed ~callback:
      (fun c -> Format.eprintf "Gconfig.color_sel : %s@."
         c)
  in
*)
  (** bottom button **)
  dialog#add_button "Close" `CLOSE ;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  (* let config = set_main config *)
  (*   (set_limits (get_main config) *)
  (*      t.time_limit t.mem_limit t.max_running_processes) *)
  (* in *)

  if !save_for_future_session then
    c.config <- Whyconf.set_main c.config
      (Whyconf.set_limits (Whyconf.get_main c.config)
         c.session_time_limit c.session_mem_limit c.session_nb_processes);
  save_config ();
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

(*let () = Debug.dprintf debug "[Info] end of configuration initialization@."*)

let uninstalled_prover c eS unknown =
  try
    Whyconf.get_prover_upgrade_policy c.config unknown
  with Not_found ->
    let others,names,versions = Session_tools.unknown_to_known_provers
      (Whyconf.get_provers eS.Session.whyconf) unknown in
    let dialog = GWindow.dialog
      ~icon:(!why_icon) ~modal:true
      ~title:"Why3: Uninstalled prover" ()
    in
    let vbox = dialog#vbox in
    let hb = GPack.hbox ~packing:vbox#add () in
    let _i = GMisc.image ~stock:`DIALOG_WARNING ~packing:hb#add () in
    let text =
      Pp.sprintf "The prover %a is not installed"
        Whyconf.print_prover unknown
    in
    let _label1 = GMisc.label ~ypad:20 ~text ~xalign:0.5 ~packing:hb#add () in
    let label = "Please select a policy for associated proof attempts" in
    let policy_frame = GBin.frame ~label ~packing:vbox#add () in
    let choice = ref 0 in
    let prover_choosed = ref None in
    let set_prover prover () = prover_choosed := Some prover in
    let box =
      GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
        ~packing:policy_frame#add ()
    in
    let choice0 = GButton.radio_button
      ~label:"keep proofs as they are, do not try to play them"
      ~active:true
      ~packing:box#add () in
    let choice1 = GButton.radio_button
      ~label:"move proofs to the selected prover below"
      ~active:false ~group:choice0#group
      ~packing:box#add () in
    let choice2 = GButton.radio_button
      ~label:"duplicate proofs to the selected prover below"
      ~active:false ~group:choice0#group
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
          let choice =
            let label = Pp.string_of_wnl print_prover prover in
            match !first with
              | None ->
                let choice =
                  GButton.radio_button ~label ~active:true ~packing:box#add ()
                in
                prover_choosed := Some prover;
                first := Some choice;
                choice
              | Some first ->
                GButton.radio_button ~label ~group:first#group
                  ~active:false ~packing:box#add ()
          in
          ignore (choice#connect#toggled ~callback:(set_prover prover))
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
    hide_provers ();
    ignore (choice0#connect#toggled
              ~callback:(fun () -> choice := 0; hide_provers ()));
    ignore (choice1#connect#toggled
              ~callback:(fun () -> choice := 1; show_provers ()));
    ignore (choice2#connect#toggled
              ~callback:(fun () -> choice := 2; show_provers ()));
    dialog#add_button "Ok" `CLOSE ;
    ignore (dialog#run ());
    dialog#destroy ();
    let policy =
      match !choice, !prover_choosed with
        | 0,_ -> CPU_keep
        | 1, Some p -> CPU_upgrade p
        | 2, Some p -> CPU_duplicate p
        | _ -> assert false
    in
    c.config <- set_prover_upgrade_policy c.config unknown policy;
    policy
(*
let unknown_prover c eS unknown =
  let others,names,versions = Session_tools.unknown_to_known_provers
  (Whyconf.get_provers eS.Session.whyconf) unknown in
  let dialog = GWindow.dialog ~title:"Why3: Unknown prover" () in
  let vbox = dialog#vbox in
  let text = Pp.sprintf "The prover %a is unknown. Could you please choose \
an alternative?" Whyconf.print_prover unknown in
  let _label1 = GMisc.label ~text ~packing:vbox#add () in
  let frame = vbox in
  let prover_choosed = ref None in
  let set_prover prover () = prover_choosed := Some prover in
  let box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:frame#add ()
  in
  let choice0 = GButton.radio_button
    ~label:"ignore this prover"
    ~active:true
    ~packing:box#add () in
  ignore (choice0#connect#toggled
            ~callback:(fun () -> prover_choosed := None));
  let alternatives_section text alternatives =
    if alternatives <> [] then
    let _label1 = GMisc.label ~text ~packing:frame#add () in
    let box =
      GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
        ~packing:frame#add ()
    in
    let iter_alter prover =
      let choice = GButton.radio_button
        ~label:(Pp.string_of_wnl print_prover prover)
        ~group:choice0#group
        ~active:false
        ~packing:box#add () in
      ignore (choice#connect#toggled ~callback:(set_prover prover))
    in
    List.iter iter_alter alternatives in
  alternatives_section "Same name and same version:" versions;
  alternatives_section "Same name and different version:" names;
  alternatives_section "Different name and different version:" others;
  let save =
    GButton.check_button
      ~label:"always use this association"
      ~packing:frame#add ()
      ~active:true
  in
  dialog#add_button "Ok" `CLOSE ;
  ignore (dialog#run ());
  dialog#destroy ();
  if save#active then
    c.altern_provers <- Mprover.add unknown !prover_choosed c.altern_provers;
  !prover_choosed
*)

(* obsolete dialog
let replace_prover c to_be_removed to_be_copied =
  if not to_be_removed.Session.proof_obsolete &&
    c.replace_prover = CRP_Not_Obsolete
  then false
  else
  let dialog = GWindow.dialog ~title:"Why3: replace proof" () in
  let vbox = dialog#vbox in
  let text = Pp.sprintf
    "Do you want to replace the external proof %a by the external proof %a \
     (with the prover of the first)"
    Session.print_external_proof to_be_removed
    Session.print_external_proof to_be_copied in
  let _label1 = GMisc.label ~text ~line_wrap:true ~packing:vbox#add () in
  dialog#add_button "Replace" `Replace;
  dialog#add_button "Keep" `Keep;
  dialog#add_button "Never replace an external proof valid and not obsolete"
    `Never;
  let res = match dialog#run () with
    | `Replace -> true
    | `Never   -> c.replace_prover <- CRP_Not_Obsolete; false
    | `DELETE_EVENT | `Keep -> false in
  dialog#destroy ();
  res
*)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
