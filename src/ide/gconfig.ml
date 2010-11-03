
open Format
open Why
open Util
open Rc
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
      mutable provers : prover_data Util.Mstr.t;
      mutable default_editor : string;
      mutable env : Env.env;
      mutable config : Whyconf.config;
    }


type ide = {
  ide_window_width : int;
  ide_window_height : int;
  ide_tree_width : int;
  ide_task_height : int;
  ide_verbose : int;
  ide_default_editor : string;
}

let default_ide =
  { ide_window_width = 1024;
    ide_window_height = 768;
    ide_tree_width = 512;
    ide_task_height = 384;
    ide_verbose = 0;
    ide_default_editor = "";
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
    ide_default_editor =
      get_string section ~default:default_ide.ide_default_editor
        "default_editor";
  }

let get_prover_data env id pr acc =
  try
    let dr = Driver.load_driver env pr.Whyconf.driver in
    Mstr.add id
      { prover_id = id ;
      prover_name = pr.Whyconf.name;
      prover_version = pr.Whyconf.version;
      command = pr.Whyconf.command;
      driver_name = pr.Whyconf.driver;
      driver = dr;
      editor = pr.Whyconf.editor;
    }
      acc
  with _e ->
    eprintf "Failed to load driver %s for prover %s. prover disabled@."
      pr.Whyconf.driver pr.Whyconf.name;
    acc

let load_config config =
  let main = get_main config in
  let ide  = match get_section config "ide" with
    | None -> default_ide
    | Some s -> load_ide s in
(*
  let provers = get_provers config in
*)
(*
  let env = Env.create_env (Lexer.retrieve main.loadpath) in
*)
  (* temporary sets env to empty *)
  let env = Env.create_env (Lexer.retrieve []) in
  { window_height = ide.ide_window_height;
    window_width  = ide.ide_window_width;
    tree_width    = ide.ide_tree_width;
    task_height   = ide.ide_task_height;
    time_limit    = main.Whyconf.timelimit;
    mem_limit     = main.Whyconf.memlimit;
    verbose       = ide.ide_verbose;
    max_running_processes = main.Whyconf.running_provers_max;
(*
    provers = Mstr.fold (get_prover_data env) provers [];
*)
    provers = Mstr.empty;
    default_editor = ide.ide_default_editor;
    config         = config;
    env            = env
  }

let read_config () =
    let config = Whyconf.read_config None in
    load_config config


let save_config t =
  let save_prover _ pr acc =
    Mstr.add pr.prover_id
      {
        Whyconf.name    = pr.prover_name;
        command = pr.command;
        driver  = pr.driver_name;
        version = pr.prover_version;
        editor  = pr.editor;
      } acc in
  let config = t.config in
  let config = set_main config
    { (get_main config) with
      timelimit    = t.time_limit;
      memlimit     = t.mem_limit;
      running_provers_max = t.max_running_processes;
    } in
  let ide = empty_section in
  let ide = set_int ide "window_height" t.window_height in
  let ide = set_int ide "window_width" t.window_width in
  let ide = set_int ide "tree_width" t.tree_width in
  let ide = set_int ide "task_height" t.task_height in
  let ide = set_int ide "verbose" t.verbose in
  let ide = set_string ide "default_editor" t.default_editor in
  let config = set_section config "ide" ide in
  let config = set_provers config
    (Mstr.fold save_prover t.provers Mstr.empty) in
  save_config config

let config =
  eprintf "reading IDE config file...@?";
  let c= read_config () in
  eprintf " done.@.";
  c

let save_config () = save_config config

let get_main () = (get_main config.config)


(*

  boomy icons

*)

let image ?size f =
  let main = get_main () in
  let n = Filename.concat (datadir main) (Filename.concat "images" (f^".png"))
  in
  match size with
    | None ->
        GdkPixbuf.from_file n
    | Some s ->
        GdkPixbuf.from_file_at_size ~width:s ~height:s n

let iconname_default = "pausehalf32"
let iconname_scheduled = "pausehalf32"
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

let () =
  eprintf "reading icons...@?";
  resize_images 20;
  eprintf " done.@."



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
  i "== icons in the status column ==\n";
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
  (* editor *)
 let hb = GPack.hbox ~homogeneous:false ~packing:page1#add () in
 let _ = GMisc.label ~text:"Default editor" ~packing:hb#add () in
 let editor_entry = GEdit.entry ~text:c.default_editor ~packing:hb#add () in
 let (_ : GtkSignal.id) =
    editor_entry#connect#changed ~callback:
      (fun () -> c.default_editor <- editor_entry#text)
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
  nb_processes_spin#adjustment#set_bounds
    ~lower:1. ~upper:16. ~step_incr:1. ();
  nb_processes_spin#adjustment#set_value
    (float_of_int c.max_running_processes);
  let (_ : GtkSignal.id) =
    nb_processes_spin#connect#value_changed ~callback:
      (fun () -> c.max_running_processes <- nb_processes_spin#value_as_int)
  in
  (** page 2 **)
  let label2 = GMisc.label ~text:"Provers" () in
  let _page2 = GMisc.label ~text:"This page should display detected provers"
    ~packing:(fun w -> ignore(notebook#append_page
                                ~tab_label:label2#coerce w)) ()
  in
  dialog#add_button "Close" `CLOSE ;
  let ( _ : GWindow.Buttons.about) = dialog#run () in
  eprintf "saving IDE config file@.";
  save_config ();
  dialog#destroy ()

let run_auto_detection gconfig =
  let config = Autodetection.run_auto_detection gconfig.config in
  gconfig.config <- config;
  let provers = get_provers config in
  gconfig.provers <- Mstr.fold (get_prover_data gconfig.env) provers Mstr.empty


let () = eprintf "end of configuration initialization@."

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/whyide.opt"
End:
*)
