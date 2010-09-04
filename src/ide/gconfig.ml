
open Format
open Why
open Util
open Whyconf

type prover_data =
    { prover_id : string;
      prover_name : string;
      prover_version : string;
      command : string;
      driver_name : string;
      driver : Driver.driver;
      mutable editor : string;
    }

type t =
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
      mutable time_limit : int;
      mutable mem_limit : int;
      mutable verbose : int;
      mutable max_running_processes : int;
      mutable provers : prover_data list;
      mutable default_editor : string;
      env : Env.env;
      mutable config : Whyconf.config;
    }

let load_main c (key, value) =
  match key with
    | "width" -> c.window_width <- Rc.int value
    | "height" -> c.window_height <- Rc.int value
    | "tree_width" -> c.tree_width <- Rc.int value
    | "task_height" -> c.task_height <- Rc.int value
    | "time_limit" -> c.time_limit <- Rc.int value
    | "verbose" -> c.verbose <- Rc.int value
    | "max_processes" -> c.max_running_processes <- Rc.int value
    | "default_editor" -> c.default_editor <- Rc.string value
    | s ->
        eprintf "Warning: ignore unknown key [%s] in whyide config file@." s



let get_prover_data env id pr acc =
  try
    let dr = Driver.load_driver env pr.Whyconf.driver in
    { prover_id = id ;
      prover_name = pr.Whyconf.name;
      prover_version = pr.Whyconf.version;
      command = pr.Whyconf.command;
      driver_name = pr.Whyconf.driver;
      driver = dr;
      editor = pr.Whyconf.editor;
    }::acc
  with _e ->
    eprintf "Failed to load driver %s for prover %s. prover disabled@."
      pr.Whyconf.driver pr.Whyconf.name;
    acc

let load_config config =
    let env = Env.create_env (Lexer.retrieve config.main.loadpath) in
    { window_height = config.ide.Whyconf.window_height;
      window_width  = config.ide.Whyconf.window_width;
      tree_width    = config.ide.Whyconf.tree_width;
      task_height   = config.ide.Whyconf.task_height;
      time_limit    = config.main.Whyconf.timelimit;
      mem_limit     = config.main.Whyconf.memlimit;
      verbose       = config.ide.Whyconf.verbose;
      max_running_processes = config.main.Whyconf.running_provers_max;
      provers = Mstr.fold (get_prover_data env) config.Whyconf.provers [];
      default_editor = config.ide.Whyconf.default_editor;
      config         = config;
      env            = env
    }

let read_config () =
    let config = Whyconf.read_config None in
    load_config config


let save_config t =
  let save_prover acc pr =
    Mstr.add pr.prover_id
      {
        Whyconf.name    = pr.prover_name;
        command = pr.command;
        driver  = pr.driver_name;
        version = pr.prover_version;
        editor  = pr.editor;
      } acc in
  let config = t.config in
  let main = { config.main with
    Whyconf.timelimit    = t.time_limit;
    memlimit     = t.mem_limit;
    running_provers_max = t.max_running_processes;
  } in
  let ide = {
    Whyconf.window_height = t.window_height;
    window_width = t.window_width;
    tree_width   = t.tree_width;
    task_height  = t.task_height;
    verbose  = t.verbose;
    default_editor = t.default_editor;
  } in
  let config = {config with
    Whyconf.provers = List.fold_left save_prover Mstr.empty t.provers;
    main    = main;
    ide     = ide;
  } in
  save_config config

(*

  boomy icons

*)

let image ?size f =
  let n = Filename.concat Whyconf.datadir (Filename.concat "images" (f^".png"))
  in
  match size with
    | None ->
        GdkPixbuf.from_file n
    | Some s ->
        GdkPixbuf.from_file_at_size ~width:s ~height:s n

let iconname_default = "pause32"
let iconname_scheduled = "pause32"
let iconname_running = "play32"
let iconname_valid = "accept32"
let iconname_unknown = "help32"
let iconname_invalid = "delete32"
let iconname_timeout = "clock32"
let iconname_failure = "bug32"
let iconname_yes = "accept32"
let iconname_no = "delete32"
let iconname_directory = "folder32"
let iconname_file = "file32"
let iconname_prover = "wizard32"
let iconname_transf = "cutb32"

let image_default = ref (image ~size:20 iconname_default)
let image_scheduled = ref !image_default
let image_running = ref !image_default
let image_valid = ref !image_default
let image_unknown = ref !image_default
let image_invalid = ref !image_default
let image_timeout = ref !image_default
let image_failure = ref !image_default
let image_yes = ref !image_default
let image_no = ref !image_default
let image_directory = ref !image_default
let image_file = ref !image_default
let image_prover = ref !image_default
let image_transf = ref !image_default

let resize_images size =
  image_default := image ~size iconname_default;
  image_scheduled := image ~size iconname_scheduled;
  image_running := image ~size iconname_running;
  image_valid := image ~size iconname_valid;
  image_unknown := image ~size iconname_unknown;
  image_invalid := image ~size iconname_invalid;
  image_timeout := image ~size iconname_timeout;
  image_failure := image ~size iconname_failure;
  image_yes := image ~size iconname_yes;
  image_no := image ~size iconname_no;
  image_directory := image ~size iconname_directory;
  image_file := image ~size iconname_file;
  image_prover := image ~size iconname_prover;
  image_transf := image ~size iconname_transf;
  ()

let () = resize_images 20



let show_legend_window () =
  let dialog = GWindow.dialog ~title:"Why: legend of icons" () in      
  let vbox = dialog#vbox in
  let text = GText.view ~packing:vbox#add () in
  let b = text#buffer in
  let i s = b#insert ~iter:b#end_iter s in
  let ib i = b#insert_pixbuf ~iter:b#end_iter ~pixbuf:!i in
  i "== icons in the tree view on the left ==\n";
  i "\n";
  ib image_directory;
  i "A theory, containing a set of goals\n";
  ib image_file;
  i "A goal\n";
  ib image_prover;
  i "An external prover\n";
  ib image_transf;
  i "A split transformation\n";
  i "\n";
  i "== icons in the satatus column\n";
  i "\n";
  ib image_scheduled;
  i "external proof scheduled by not started yet\n";
  ib image_running;
  i "external proof is running\n";
  ib image_valid;
  i "goal is proved/theory is fully verified\n";
  ib image_timeout;
  i "external prover reached the time limit\n";
  ib image_unknown;
  i "external prover answer was not conclusive\n";
  ib image_failure;
  i "external prover call failed\n";
  i "\n";
  dialog#add_button "Close" `CLOSE ;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  dialog#destroy ()


let show_about_window () =
  let about_dialog = 
    GWindow.about_dialog 
      ~name:"Why" 
      ~authors:["Francois Bobot";
                "Jean-Christophe Filliatre";
                "Johannes Kanig";
                "Claude Marche";
                "Andrei Paskevich"
               ]
      ~copyright:"Copyright 2010"
      ~license:"Gnu Lesser General Public License"
      ~website:"http://why.lri.fr"
      ~website_label:"Click here for the web site"
      ~version:"3.0 alpha"
      ()
  in      
  let ( _ : GWindow.Buttons.about) = about_dialog#run () in
  about_dialog#destroy ()

let preferences c =
  let dialog = GWindow.dialog ~title:"Why: preferences" () in      
  let vbox = dialog#vbox in
  let notebook = GPack.notebook ~packing:vbox#add () in
  (** page 1 **)
  let label1 = GMisc.label ~text:"General" () in
  let page1 =
    GPack.vbox ~homogeneous:false ~packing:
      (fun w -> ignore(notebook#append_page ~tab_label:label1#coerce w)) ()
  in 
  (* debug mode ? *)
  let debugmode = 
    GButton.check_button ~label:"debug" ~packing:page1#add ()
      ~active:(c.verbose > 0)
  in
  let (_ : GtkSignal.id) = 
    debugmode#connect#toggled ~callback:
      (fun () -> c.verbose <- 1 - c.verbose)
  in
  (* timelimit ? *)
  let hb = GPack.hbox ~homogeneous:false ~packing:page1#add () in
  let _ = GMisc.label ~text:"Time limit" ~packing:hb#add () in
  let timelimit_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  timelimit_spin#adjustment#set_bounds ~lower:2. ~upper:300. ~step_incr:1. ();
  timelimit_spin#adjustment#set_value (float_of_int c.time_limit);
  let (_ : GtkSignal.id) = 
    timelimit_spin#connect#value_changed ~callback:
      (fun () -> c.time_limit <- timelimit_spin#value_as_int)
  in
  (* nb of processes ? *)
  let hb = GPack.hbox ~homogeneous:false ~packing:page1#add () in
  let _ = GMisc.label ~text:"Nb of processes" ~packing:hb#add () in
  let nb_processes_spin = GEdit.spin_button ~digits:0 ~packing:hb#add () in
  nb_processes_spin#adjustment#set_bounds ~lower:1. ~upper:16. ~step_incr:1. ();
  nb_processes_spin#adjustment#set_value (float_of_int c.max_running_processes);
  let (_ : GtkSignal.id) = 
    nb_processes_spin#connect#value_changed ~callback:
      (fun () -> c.max_running_processes <- nb_processes_spin#value_as_int)
  in
  (** page 2 **)
  let label2 = GMisc.label ~text:"Provers" () in
  let _page2 = GMisc.label ~text:"This page should display detected provers" 
    ~packing:(fun w -> ignore(notebook#append_page ~tab_label:label2#coerce w)) () 
  in
  dialog#add_button "Close" `CLOSE ;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  eprintf "saving IDE config file@.";
  save_config c;
  dialog#destroy ()

let run_auto_detection gconfig =
  let config2 = run_auto_detection gconfig.config in
  let gconfig2 = load_config config2 in
  gconfig.window_width <- gconfig2.window_width;
  gconfig.window_height <- gconfig2.window_height;
  gconfig.tree_width <- gconfig2.tree_width;
  gconfig.task_height <- gconfig2.task_height;
  gconfig.time_limit <- gconfig2.time_limit;
  gconfig.mem_limit <- gconfig2.mem_limit;
  gconfig.verbose <- gconfig2.verbose;
  gconfig.max_running_processes <- gconfig2.max_running_processes;
  gconfig.provers <- gconfig2.provers;
  gconfig.default_editor <- gconfig2.default_editor;
  gconfig.config <- gconfig2.config

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. bin/whyide.opt"
End: 
*)
